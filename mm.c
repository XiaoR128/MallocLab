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
  "vyc229",
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

#define MAX_SEGLIST_SIZE        10
#define REALLOC_BUFFER          (1<<7)

#define MAX(x, y) ((x) > (y) ? (x) : (y))
#define MIN(x, y) ((x) < (y) ? (x) : (y))

#define PACK(size, alloc) ((size) | (alloc))

#define GET(p)                  (*(unsigned int *)(p))
#define PUT(p, val)       (*(unsigned int *)(p) = (val))
#define PUT_SEG_LIST(p, val)    (*(unsigned int *)(p) = (val) | GET_TAG(p))

#define SET_PTR(p, ptr)         (*(unsigned int *)(p) = (unsigned int)(ptr))

#define GET_SIZE(p)             (GET(p) & ~0x7)
#define GET_ALLOC(p)            (GET(p) & 0x1)
#define GET_TAG(p)              (GET(p) & 0x2)
#define SET_RATAG(p)            (GET(p) |= 0x2)
#define REMOVE_RATAG(p)         (GET(p) &= ~0x2)

#define HDRP(ptr)               ((char *)(ptr) - WSIZE)
#define FTRP(ptr)               ((char *)(ptr) + GET_SIZE(HDRP(ptr)) - DSIZE)
#define NEXT_BLKP(ptr)          ((char *)(ptr) + GET_SIZE((char *)(ptr) - WSIZE))
#define PREV_BLKP(ptr)          ((char *)(ptr) - GET_SIZE((char *)(ptr) - DSIZE))
#define PREV_FREEP(ptr)           ((char *)(ptr))
#define NEXT_FREEP(ptr)           ((char *)(ptr) + WSIZE)

#define PREV_SEGP(ptr)               (*(char **)(ptr))
#define NEXT_SEGP(ptr)               (*(char **)(NEXT_FREEP(ptr)))

void *seg_list[MAX_SEGLIST_SIZE];

static void *extend_heap(size_t size);
static void *coalesce(void *ptr);
static void *place(void *ptr, size_t asize);
static void add_block(void *ptr, size_t size);
static void remove_block(void *ptr);

char *heap_listp;

int mm_init(void)
{
  /* Initialize free segregated list*/
    for (int i = 0; i < MAX_SEGLIST_SIZE; i++) {
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
    size_t asize;
    size_t extendsize;
    void *ptr = NULL;

    if (size == 0)
        return NULL;

    if (size <= DSIZE) {
        asize = 2 * DSIZE;
    } else {
        asize = ALIGN(size+DSIZE);
    }

    int list = 0;
    size_t searchsize = asize;
    while (list < MAX_SEGLIST_SIZE) {
        if ((list == MAX_SEGLIST_SIZE - 1) || ((searchsize <= 1) && (seg_list[list] != NULL))) {
            ptr = seg_list[list];
            while ((ptr != NULL) && ((asize > GET_SIZE(HDRP(ptr))) || (GET_TAG(HDRP(ptr)))))
            {
                ptr = PREV_SEGP(ptr);
            }
            if (ptr != NULL)
                break;
        }

        searchsize >>= 1;
        list++;
    }
    if (ptr == NULL) {
        extendsize = MAX(asize, CHUNKSIZE);

        if ((ptr = extend_heap(extendsize)) == NULL)
            return NULL;
    }
    ptr = place(ptr, asize);
    return ptr;
}

void mm_free(void *ptr)
{
    size_t size = GET_SIZE(HDRP(ptr));

    REMOVE_RATAG(HDRP(NEXT_BLKP(ptr)));
    PUT_SEG_LIST(HDRP(ptr), PACK(size, 0));
    PUT_SEG_LIST(FTRP(ptr), PACK(size, 0));

    add_block(ptr, size);
    coalesce(ptr);

    return;
}

void *mm_realloc(void *ptr, size_t size)
{
    void *new_ptr = ptr;
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
    block_buffer = GET_SIZE(HDRP(ptr)) - new_size;

    if (block_buffer < 0) {
        if (!GET_ALLOC(HDRP(NEXT_BLKP(ptr))) || !GET_SIZE(HDRP(NEXT_BLKP(ptr)))) {
            remainder = GET_SIZE(HDRP(ptr)) + GET_SIZE(HDRP(NEXT_BLKP(ptr))) - new_size;
            if (remainder < 0) {
                extendsize = MAX(-remainder, CHUNKSIZE);
                if (extend_heap(extendsize) == NULL)
                    return NULL;
                remainder += extendsize;
            }

            remove_block(NEXT_BLKP(ptr));

            PUT(HDRP(ptr), PACK(new_size + remainder, 1));
            PUT(FTRP(ptr), PACK(new_size + remainder, 1));
        } else {
            new_ptr = mm_malloc(new_size - DSIZE);
            memcpy(new_ptr, ptr, MIN(size, new_size));
            mm_free(ptr);
        }
        block_buffer = GET_SIZE(HDRP(new_ptr)) - new_size;
    }

    if (block_buffer < 2 * REALLOC_BUFFER)
        SET_RATAG(HDRP(NEXT_BLKP(new_ptr)));
    return new_ptr;
}

static void *extend_heap(size_t size)
{
    void *ptr;
    size_t asize;

    asize = ALIGN(size);

    if ((ptr = mem_sbrk(asize)) == (void *)-1)
        return NULL;

    // Set headers and footer
    PUT(HDRP(ptr), PACK(asize, 0));
    PUT(FTRP(ptr), PACK(asize, 0));
    PUT(HDRP(NEXT_BLKP(ptr)), PACK(0, 1));
    add_block(ptr, asize);

    return coalesce(ptr);
}

static void add_block(void *ptr, size_t size) {
    int list = 0;
    void *search_ptr = ptr;
    void *insert_ptr = NULL;

    while ((list < MAX_SEGLIST_SIZE - 1) && (size > 1)) {
        size >>= 1;
        list++;
    }

    search_ptr = seg_list[list];
    while ((search_ptr != NULL) && (size > GET_SIZE(HDRP(search_ptr)))) {
        insert_ptr = search_ptr;
        search_ptr = PREV_SEGP(search_ptr);
    }

    if (search_ptr != NULL) {
        if (insert_ptr != NULL) {
            SET_PTR(PREV_FREEP(ptr), search_ptr);
            SET_PTR(NEXT_FREEP(search_ptr), ptr);
            SET_PTR(NEXT_FREEP(ptr), insert_ptr);
            SET_PTR(PREV_FREEP(insert_ptr), ptr);
        } else {
            SET_PTR(PREV_FREEP(ptr), search_ptr);
            SET_PTR(NEXT_FREEP(search_ptr), ptr);
            SET_PTR(NEXT_FREEP(ptr), NULL);
            seg_list[list] = ptr;
        }
    } else {
        if (insert_ptr != NULL) {
            SET_PTR(PREV_FREEP(ptr), NULL);
            SET_PTR(NEXT_FREEP(ptr), insert_ptr);
            SET_PTR(PREV_FREEP(insert_ptr), ptr);
        } else {
            SET_PTR(PREV_FREEP(ptr), NULL);
            SET_PTR(NEXT_FREEP(ptr), NULL);
            seg_list[list] = ptr;
        }
    }

    return;
}


static void remove_block(void *ptr) {
    int list = 0;
    size_t size = GET_SIZE(HDRP(ptr));

    while ((list < MAX_SEGLIST_SIZE - 1) && (size > 1)) {
        size >>= 1;
        list++;
    }

    if (PREV_SEGP(ptr) != NULL) {
        if (NEXT_SEGP(ptr) != NULL) {
            SET_PTR(NEXT_FREEP(PREV_SEGP(ptr)), NEXT_SEGP(ptr));
            SET_PTR(PREV_FREEP(NEXT_SEGP(ptr)), PREV_SEGP(ptr));
        } else {
            SET_PTR(NEXT_FREEP(PREV_SEGP(ptr)), NULL);
            seg_list[list] = PREV_SEGP(ptr);
        }
    } else {
        if (NEXT_SEGP(ptr) != NULL) {
            SET_PTR(PREV_FREEP(NEXT_SEGP(ptr)), NULL);
        } else {
            seg_list[list] = NULL;
        }
    }
    return;
}


static void *coalesce(void *ptr)
{
    size_t prev_alloc = GET_ALLOC(HDRP(PREV_BLKP(ptr)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(ptr)));
    size_t size = GET_SIZE(HDRP(ptr));

    if (GET_TAG(HDRP(PREV_BLKP(ptr))))
        prev_alloc = 1;

    if (prev_alloc && next_alloc) {
        return ptr;
    }
    else if (prev_alloc && !next_alloc) {
        remove_block(ptr);
        remove_block(NEXT_BLKP(ptr));
        size += GET_SIZE(HDRP(NEXT_BLKP(ptr)));
        PUT_SEG_LIST(HDRP(ptr), PACK(size, 0));
        PUT_SEG_LIST(FTRP(ptr), PACK(size, 0));
    } else if (!prev_alloc && next_alloc) {
        remove_block(ptr);
        remove_block(PREV_BLKP(ptr));
        size += GET_SIZE(HDRP(PREV_BLKP(ptr)));
        PUT_SEG_LIST(FTRP(ptr), PACK(size, 0));
        PUT_SEG_LIST(HDRP(PREV_BLKP(ptr)), PACK(size, 0));
        ptr = PREV_BLKP(ptr);
    } else {
        remove_block(ptr);
        remove_block(PREV_BLKP(ptr));
        remove_block(NEXT_BLKP(ptr));
        size += GET_SIZE(HDRP(PREV_BLKP(ptr))) + GET_SIZE(HDRP(NEXT_BLKP(ptr)));
        PUT_SEG_LIST(HDRP(PREV_BLKP(ptr)), PACK(size, 0));
        PUT_SEG_LIST(FTRP(NEXT_BLKP(ptr)), PACK(size, 0));
        ptr = PREV_BLKP(ptr);
    }

    add_block(ptr, size);

    return ptr;
}

static void *place(void *ptr, size_t asize)
{
    size_t ptr_size = GET_SIZE(HDRP(ptr));
    size_t remainder = ptr_size - asize;

    remove_block(ptr);


    if (remainder <= DSIZE * 2) {
        // Do not split block
        PUT_SEG_LIST(HDRP(ptr), PACK(ptr_size, 1));
        PUT_SEG_LIST(FTRP(ptr), PACK(ptr_size, 1));
    }

    else if (asize >= 100) {
        // Split block
        PUT_SEG_LIST(HDRP(ptr), PACK(remainder, 0));
        PUT_SEG_LIST(FTRP(ptr), PACK(remainder, 0));
        PUT(HDRP(NEXT_BLKP(ptr)), PACK(asize, 1));
        PUT(FTRP(NEXT_BLKP(ptr)), PACK(asize, 1));
        add_block(ptr, remainder);
        return NEXT_BLKP(ptr);

    }

    else {
        PUT_SEG_LIST(HDRP(ptr), PACK(asize, 1));
        PUT_SEG_LIST(FTRP(ptr), PACK(asize, 1));
        PUT(HDRP(NEXT_BLKP(ptr)), PACK(remainder, 0));
        PUT(FTRP(NEXT_BLKP(ptr)), PACK(remainder, 0));
        add_block(NEXT_BLKP(ptr), remainder);
    }
    return ptr;
}
