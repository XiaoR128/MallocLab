/* WORKING IMPLICIT LIST IMPLEMENTATION */
/*
* mm-naive.c - The fastest, least memory-efficient malloc package.
*
* In this naive approach, a block is allocated by simply incrementing
* the brk pointer.  A block is pure payload. There are no headers or
* footers.  Blocks are never coalesced or reused. Realloc is
* implemented directly using mm_malloc and mm_free.
*
* NOTE TO STUDENTS: Replace this header comment with your own header
* comment that gives a high level description of your solution.
*/
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>
#include "mm.h"
#include "memlib.h"

/*********************************************************
* NOTE TO STUDENTS: Before you do anything else, please
* provide your team information in the following struct.
********************************************************/
team_t team = {
  /* Team name */
  "Halp",
  /* First member's full name */
  "Victoria Cabales",
  /* First member's email address */
  "victoriacabales2019@u.northwestern.edu",
  /* Second member's full name (leave blank if none) */
  "Daniel Kim",
  /* Second member's email address (leave blank if none) */
  "danielkim2019@u.northwestern.edu"
};

#define ALIGNMENT               8
#define ALIGN(size)             (((size) + (ALIGNMENT-1)) & ~0x7)
#define WSIZE                   4
#define DSIZE                   8
#define CHUNKSIZE               (1<<12)
#define OVERHEAD                16

#define MAX_SEGLIST_SIZE        10
#define REALLOC_BUFFER          (1<<7)

#define MAX(x, y) ((x) > (y) ? (x) : (y))
#define MIN(x, y) ((x) < (y) ? (x) : (y))

#define PACK(size, alloc) ((size) | (alloc))

#define GET(bp)                   (*(unsigned int *)(bp))      /* Read value at address */
#define PUT(bp, val)              (*(unsigned int *)(bp) = (val))    /* Write value at address */
#define PUT_SEG_LIST(bp, val)     (*(unsigned int *)(bp) = (val) | GET_TAG(bp)) /* Put on seg list with tag*/
#define GET_SIZE(bp)               (GET(bp) & ~0x7) /* Read size at address */
#define GET_ALLOC(bp)              (GET(bp) & 0x1) /* Check if block is allocated*/

/* Tags for reallocation */
#define GET_TAG(p)                (GET(p) & 0x2)
#define SET_RATAG(p)              (GET(p) = GET(p) | 0x2)
#define REMOVE_RATAG(p)           (GET(p) = GET(p) & ~0x2)

#define HDRP(bp)                  ((char *)(bp) - WSIZE)  /* Get header */
#define FTRP(bp)                  ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) /* Get footer */
#define NEXT_BLKP(bp)             ((char *)(bp) + GET_SIZE((char *)(bp) - WSIZE)) /* Next physical block on heap */
#define PREV_BLKP(bp)             ((char *)(bp) - GET_SIZE((char *)(bp) - DSIZE)) /* Previous physical block on heap */
#define PREV_FREEP(bp)            ((char *)(bp)) /* Previous free block on heap*/
#define NEXT_FREEP(bp)            ((char *)(bp) + WSIZE) /* Next free block on heap */

#define PREV_SEGP(bp)             (*(char **)(bp))  /* Previous block on seg list */
#define NEXT_SEGP(bp)             (*(char **)(NEXT_FREEP(bp))) /* Next block on seg list */
#define SET_PTR(p, bp)            (*(unsigned int *)(p) = (unsigned int)(bp)) /* Set pointer on seg list*/

void *seg_list[MAX_SEGLIST_SIZE]; /* Segmented list */

static void *extend_heap(size_t size);
static void *coalesce(void *bp);
static void *place(void *bp, size_t asize);
static void *add_block(void *bp, size_t size);
static void *remove_block(void *bp);

char *heap_listp; /* Points to very first block of heap, for mm_check*/

int mm_init(void)
{
  int i;
  /* Initialize free segregated list*/
    for (i = 0; i < MAX_SEGLIST_SIZE; i++) {
        seg_list[i] = NULL;
    }

    if ((long)(heap_listp = mem_sbrk(4 * WSIZE)) == -1)
        return -1;

    PUT(heap_listp, 0);                                 /* Alignment Padding (4 bytes)*/
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1));      /* Prologue Header (4 bytes)*/
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1));      /* Prologue Footer (4 bytes)*/
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1));          /* Epilogue*/
    heap_listp = (heap_listp + (2*WSIZE));

    if (extend_heap(CHUNKSIZE) == NULL)
        return -1;

    return 0;
}

void *mm_malloc(size_t size)
{
    size_t extendsize;
    void *bp = NULL;

    if (heap_listp == 0)
    {
      mm_init();
    }

    if (size == 0)
        return NULL;

    size_t asize = MAX(ALIGN(size) + DSIZE, OVERHEAD);
    /* Arrange blocks by classes of 2^k*/

    /*
    size_t findClass = asize;
    for (int i = 0; ((i < MAX_SEGLIST_SIZE) && (bp != NULL)); i++)
    {
      if (((findClass <= 1) && (seg_list[i] != NULL)) || (i == MAX_SEGLIST_SIZE - 1))
      {
        bp = seg_list[i];
        while ((bp != NULL) && ((asize > GET_SIZE(HDRP(bp))) || (GET_TAG(HDRP(bp)))))
        {
          bp = PREV_SEGP(bp);
        }
      }
      findClass = findClass / 2;
    } */

    int i = 0;
    size_t findClass = asize;
    while (i < MAX_SEGLIST_SIZE) {
        if (((seg_list[i] != NULL) && (findClass <= 1)) || (i == MAX_SEGLIST_SIZE - 1)) {
            bp = seg_list[i];
            while ((bp != NULL) && ((asize > GET_SIZE(HDRP(bp))) || (GET_TAG(HDRP(bp)))))
            {
                bp = PREV_SEGP(bp);
            }
            if (bp != NULL)
                break;
        }

        findClass = findClass / 2;
        i++;
    }
    if (bp == NULL) {
        extendsize = MAX(asize, CHUNKSIZE);

        if ((bp = extend_heap(extendsize)) == NULL)
            return NULL;
    }
    bp = place(bp, asize);
    return bp;
}

void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));

    REMOVE_RATAG(HDRP(NEXT_BLKP(bp)));
    PUT_SEG_LIST(HDRP(bp), PACK(size, 0));
    PUT_SEG_LIST(FTRP(bp), PACK(size, 0));

    add_block(bp, size);
    coalesce(bp);

    return;
}

void *mm_realloc(void *bp, size_t size)
{
    void *new_bp = bp;
    size_t new_size = size;
    int remainder;
    int extendsize;
    int block_buffer;

    if (size == 0)
        return NULL;

    if (new_size <= DSIZE) {
        new_size = 2 * DSIZE;
    } else {
        new_size = ALIGN(size+DSIZE);
    }

    new_size += REALLOC_BUFFER;
    block_buffer = GET_SIZE(HDRP(bp)) - new_size;

    if (block_buffer < 0) {
        if (!GET_ALLOC(HDRP(NEXT_BLKP(bp))) || !GET_SIZE(HDRP(NEXT_BLKP(bp)))) {
            remainder = GET_SIZE(HDRP(bp)) + GET_SIZE(HDRP(NEXT_BLKP(bp))) - new_size;
            if (remainder < 0) {
                extendsize = MAX(-remainder, CHUNKSIZE);
                if (extend_heap(extendsize) == NULL)
                    return NULL;
                remainder += extendsize;
            }

            remove_block(NEXT_BLKP(bp));

            PUT(HDRP(bp), PACK(new_size + remainder, 1));
            PUT(FTRP(bp), PACK(new_size + remainder, 1));
        } else {
            new_bp = mm_malloc(new_size - DSIZE);
            mm_free(bp);
        }
        block_buffer = GET_SIZE(HDRP(new_bp)) - new_size;
    }

    if (block_buffer < 2 * REALLOC_BUFFER)
        SET_RATAG(HDRP(NEXT_BLKP(new_bp)));
    return new_bp;
}

static void *extend_heap(size_t size)
{
    void *bp;
    size_t asize = ALIGN(size);
    /*
    asize = (size % 2) ? (size + 1) * WSIZE : size * WSIZE;
    if (size < OVERHEAD)
    {
      size = OVERHEAD;
    } */

    if ((bp = mem_sbrk(asize)) == (void *)-1)
        return NULL;

    // Set headers and footer
    PUT(HDRP(bp), PACK(asize, 0));
    PUT(FTRP(bp), PACK(asize, 0));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));
    add_block(bp, asize);

    return coalesce(bp);
}

static void *add_block(void *bp, size_t size) {
    void *search = bp;
    void *insert = NULL;

    int findClass = 0;
    while ((findClass < MAX_SEGLIST_SIZE - 1) && (size > 1)) {
        size = size / 2; /* Find the class it belongs in within seg_list */
        findClass++;
    }

    search = seg_list[findClass];
    /* Sort addresses by ascending order */
    while ((search != NULL) && (size > GET_SIZE(HDRP(search)))) {
        insert = search;
        search = PREV_SEGP(search);
    }

    if (search)
    { /* Watch out for null access errors!!! */
        if (!insert)
        {
          /* printf("Running 1a of add_block/n"); */
          SET_PTR(PREV_FREEP(bp), search);
          SET_PTR(NEXT_FREEP(search), bp);
          SET_PTR(NEXT_FREEP(bp), NULL);
          seg_list[findClass] = bp;
        }
        else
        {
          /* printf("Running 1b of add_block\n"); */
          SET_PTR(PREV_FREEP(bp), search);
          SET_PTR(NEXT_FREEP(search), bp);
          SET_PTR(NEXT_FREEP(bp), insert);
          SET_PTR(PREV_FREEP(insert), bp);
        }
    }
    else if (!search)
    {
        if (insert) {
            /* printf("Running 2a of add_block\n"); */
            SET_PTR(PREV_FREEP(bp), NULL);
            SET_PTR(NEXT_FREEP(bp), insert);
            SET_PTR(PREV_FREEP(insert), bp);
        } else {
            /* printf("Running 2b of add_block\n"); */
            SET_PTR(PREV_FREEP(bp), NULL);
            SET_PTR(NEXT_FREEP(bp), NULL);
            seg_list[findClass] = bp;
        }
    }
    return bp;
}


static void *remove_block(void *bp) {
    int list = 0;
    size_t size = GET_SIZE(HDRP(bp));

    while ((list < MAX_SEGLIST_SIZE - 1) && (size > 1)) {
        size = size / 2;
        list++;
    }

    if (PREV_SEGP(bp) != NULL) {
        if (NEXT_SEGP(bp) != NULL) {
            SET_PTR(NEXT_FREEP(PREV_SEGP(bp)), NEXT_SEGP(bp));
            SET_PTR(PREV_FREEP(NEXT_SEGP(bp)), PREV_SEGP(bp));
        } else {
            SET_PTR(NEXT_FREEP(PREV_SEGP(bp)), NULL);
            seg_list[list] = PREV_SEGP(bp);
        }
    } else {
        if (NEXT_SEGP(bp) != NULL) {
            SET_PTR(PREV_FREEP(NEXT_SEGP(bp)), NULL);
        } else {
            seg_list[list] = NULL;
        }
    }
    return bp;
}


static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(HDRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (GET_TAG(HDRP(PREV_BLKP(bp))))
        prev_alloc = 1;

    if (prev_alloc && next_alloc) {
        return bp;
    }
    else if (prev_alloc && !next_alloc) {
        remove_block(bp);
        remove_block(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT_SEG_LIST(HDRP(bp), PACK(size, 0));
        PUT_SEG_LIST(FTRP(bp), PACK(size, 0));
    } else if (!prev_alloc && next_alloc) {
        remove_block(bp);
        remove_block(PREV_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT_SEG_LIST(FTRP(bp), PACK(size, 0));
        PUT_SEG_LIST(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    } else {
        remove_block(bp);
        remove_block(PREV_BLKP(bp));
        remove_block(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT_SEG_LIST(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT_SEG_LIST(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    add_block(bp, size);

    return bp;
}

static void *place(void *bp, size_t asize)
{
    size_t ptr_size = GET_SIZE(HDRP(bp));
    size_t remainder = ptr_size - asize;

    remove_block(bp);


    if (remainder <= DSIZE * 2) {
        // Do not split block
        PUT_SEG_LIST(HDRP(bp), PACK(ptr_size, 1));
        PUT_SEG_LIST(FTRP(bp), PACK(ptr_size, 1));
    }

    else if (asize >= 100) {
        // Split block
        PUT_SEG_LIST(HDRP(bp), PACK(remainder, 0));
        PUT_SEG_LIST(FTRP(bp), PACK(remainder, 0));
        PUT(HDRP(NEXT_BLKP(bp)), PACK(asize, 1));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(asize, 1));
        add_block(bp, remainder);
        return NEXT_BLKP(bp);

    }

    else {
        PUT_SEG_LIST(HDRP(bp), PACK(asize, 1));
        PUT_SEG_LIST(FTRP(bp), PACK(asize, 1));
        PUT(HDRP(NEXT_BLKP(bp)), PACK(remainder, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(remainder, 0));
        add_block(NEXT_BLKP(bp), remainder);
    }
    return bp;
}
