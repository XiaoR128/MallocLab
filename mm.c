/* Segmented List Implementation */
/* 92/100 performance
*
*
* In this segmented list approach, the heap is essentially a large doubly linked
* list of blocks that are tagged as free, allocated, or re-allocated. Each block
* has a header and footer tag, which stores the size, allocation bit, and
* reallocation bit of the block.
*
* Free blocks are stored on an array called seg_list and arranged in groups
* of sizes of 2^k. This organization reduces the runtime of searching seg_list
* to log2(n), where n is the number of blocks on the array. Free blocks are
* distinguished from allocated blocks because they have an additional predecessor
* and successor on the segmented free list array. These predecessor and successor
* tags are over-written with data once the block is allocated. Each allocated block
* also has an allocated or reallocated tag to prevent blocks from being reused.
* Blocks are coalesced to prevent fragmentation, and an epilogue block indicates
* the end of the heap.
*
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
#define ALIGN(size)             (((size) + (ALIGNMENT-1)) & ~0x7) /* All blocks are divisble by 8*/
#define WSIZE                   4
#define DSIZE                   8
#define CHUNKSIZE               (1<<12)
#define OVERHEAD                16 /* Store user blocks */

#define MAX_SEGLIST_SIZE        10 /* Max number of classes */
#define REALLOC_BUFFER          (1<<8) /* idky this number works, but it does and i give up on this lab*/

#define MAX(x, y) ((x) > (y) ? (x) : (y))

#define PACK(size, alloc) ((size) | (alloc))  /* Pack data into one word size */

#define GET(bp)                   (*(unsigned int *)(bp))      /* Read value at address */
#define PUT(bp, val)              (*(unsigned int *)(bp) = (val))    /* Write value at address */
#define PUT_SEG_LIST(bp, val)     (*(unsigned int *)(bp) = (val) | GET_TAG(bp)) /* Put on seg list with tag*/
#define GET_SIZE(bp)               (GET(bp) & ~0x7) /* Read size at address */
#define GET_ALLOC(bp)              (GET(bp) & 0x1) /* Check if block is allocated*/

/* Tags for allocation/reallocation */
#define GET_TAG(p)                (GET(p) & 0x2)
#define SET_RATAG(p)              (GET(p) = GET(p) | 0x2)
#define REMOVE_RATAG(p)           (GET(p) = GET(p) & ~0x2)

/* Physical heap macros */
#define HDRP(bp)                  ((char *)(bp) - WSIZE)  /* Get header */
#define FTRP(bp)                  ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) /* Get footer */
#define NEXT_BLKP(bp)             ((char *)(bp) + GET_SIZE((char *)(bp) - WSIZE)) /* Next physical block on heap */
#define PREV_BLKP(bp)             ((char *)(bp) - GET_SIZE((char *)(bp) - DSIZE)) /* Previous physical block on heap */
#define PREV_FREEP(bp)            ((char *)(bp)) /* Previous free block on heap*/
#define NEXT_FREEP(bp)            ((char *)(bp) + WSIZE) /* Next free block on heap */

/* Free seg list macros */
#define PREV_SEGP(bp)             (*(char **)(bp))  /* Previous block on seg list */
#define NEXT_SEGP(bp)             (*(char **)(NEXT_FREEP(bp))) /* Next block on seg list */
#define SET_PTR(p, bp)            (*(unsigned int *)(p) = (unsigned int)(bp)) /* Set pointer on seg list*/
                                  /* Must be cast as unsigned to prevent NULL pointer warning*/

void *seg_list[MAX_SEGLIST_SIZE]; /* Segmented list */

static void *extend_heap(size_t size);
static void *coalesce(void *bp);
static void *place(void *bp, size_t asize);
static void *organizeClasses(void *ptr, size_t size);
static void *searchReallocBuffer(void *bp, void* ptr, size_t size);
static void *add_block(void *bp, size_t size);
static void *remove_block(void *bp);
static int mm_check();
static int checkblock(void *bp);
static void printblock(void *bp);



char *heap_listp; /* Points to very first block of heap, for mm_check*/

int mm_init(void)
{
  int i; /* Must initialize counter outside of for loop in C99 */
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
    /* Point between prologue header and footer -> where user data starts*/

    /* mm_check(); */

    if (extend_heap(CHUNKSIZE) == NULL)
        return -1;

    /* mm_check();  //Check alignment after extending */

    return 0;
}

static void *organizeClasses(void *ptr, size_t asize){
  int i = 0;
  size_t findClass = asize;
  while (i < MAX_SEGLIST_SIZE) { /* Organize classes in ascending order*/
      if (((seg_list[i] != NULL) && (findClass <= 1)) || (i == MAX_SEGLIST_SIZE - 1)) {
          ptr = seg_list[i];
          while ((ptr != NULL) && ((asize > GET_SIZE(HDRP(ptr))) || (GET_TAG(HDRP(ptr)))))
          {
              ptr = PREV_SEGP(ptr);
          }
          if (ptr != NULL)
              break;
      }

      findClass = findClass / 2; /* Classes are organized by powers of 2*/
      i++;
  }
  return ptr;
}

void *mm_malloc(size_t size)
{
    size_t extendsize;
    void *bp = NULL;

    if (heap_listp == 0) /* Call init if heap is empty*/
    {
      mm_init();
    }

    if (size == 0) /*No memory to allocate, return null */
        return NULL;

    size_t asize = MAX(ALIGN(size + DSIZE), OVERHEAD);
    bp = organizeClasses(bp, asize);

    if (bp == NULL) {
        extendsize = MAX(asize, CHUNKSIZE); /* Get more memory if bp is null*/
        if ((bp = extend_heap(extendsize)) == NULL)
            return NULL;
    }
    bp = place(bp, asize);
    /* mm_check(); */
    return bp;
}

void mm_free(void *bp)
{
    if (!bp) /*Check if there's nothing to free*/
    {
      return;
    }

    size_t size = GET_SIZE(HDRP(bp));

    REMOVE_RATAG(HDRP(NEXT_BLKP(bp))); /* Block now free, can reallocate*/
    PUT_SEG_LIST(HDRP(bp), PACK(size, 0)); /* Set header of free list*/
    PUT_SEG_LIST(FTRP(bp), PACK(size, 0)); /* Set footer of free list*/

    add_block(bp, size);
    coalesce(bp);
    return;
}

void *searchReallocBuffer(void *bp, void *ptr, size_t asize) {
  asize += REALLOC_BUFFER;
  int block_buffer = GET_SIZE(HDRP(bp)) - asize;
  int extendsize;
  int remainder;

  if (block_buffer < 0) { /*Make sure the size you are trying to adjust isn't larger than current block size */
      if (!GET_ALLOC(HDRP(NEXT_BLKP(bp))) || !GET_SIZE(HDRP(NEXT_BLKP(bp)))) {
          remainder = GET_SIZE(HDRP(bp)) + GET_SIZE(HDRP(NEXT_BLKP(bp))) - asize; /* Readjust size to fit */
          if (remainder < 0) {
              extendsize = MAX(remainder, CHUNKSIZE); /* Get more memory*/
              if (extend_heap(extendsize) == NULL)
                  return NULL;
              remainder += extendsize;
          }

          remove_block(NEXT_BLKP(bp));

          PUT(HDRP(bp), PACK(asize + remainder, 1));
          PUT(FTRP(bp), PACK(asize + remainder, 1));
      }
      else {
          ptr = mm_malloc(asize - DSIZE);
          mm_free(bp);
      }
      block_buffer = GET_SIZE(HDRP(ptr)) - asize;
  }
  /* mm_check(); */
  /* Use RA Tags to keep from reallocating blocks that have already been */
  if (block_buffer < 2 * REALLOC_BUFFER)
      SET_RATAG(HDRP(NEXT_BLKP(ptr)));

  return ptr;

}

void *mm_realloc(void *bp, size_t size)
{
    void *ptr = bp;

    if (ptr == NULL)
    {
      return mm_malloc(size);
    }

    if (size == 0)
    {
      mm_free(bp);
      return 0;
    }

    size_t asize = MAX(ALIGN(size + DSIZE), OVERHEAD);
    ptr = searchReallocBuffer(bp, ptr, asize);

    return ptr;
}

static void *extend_heap(size_t size)
{
    void *bp;
    size_t asize = ALIGN(size);
    /*
    From textbook but decreases efficiency
    asize = (size % 2) ? (size + 1) * WSIZE : size * WSIZE;
    if (size < OVERHEAD)
    {
      size = OVERHEAD;
    } */

    if ((bp = mem_sbrk(asize)) == (void *)-1)
        return NULL;

    PUT(HDRP(bp), PACK(asize, 0)); /* Set header */
    PUT(FTRP(bp), PACK(asize, 0)); /* Set footer */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* Set epilogue */
    add_block(bp, asize);

    /* mm_check();*/

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
    if (search && insert)
    {
      /* printf("Running 1b of add_block\n"); */
      SET_PTR(PREV_FREEP(bp), search);
      SET_PTR(NEXT_FREEP(search), bp);
      SET_PTR(NEXT_FREEP(bp), insert);
      SET_PTR(PREV_FREEP(insert), bp);
    }
    else if (search && !insert)
    {
      /* printf("Running 1a of add_block/n"); */
      SET_PTR(PREV_FREEP(bp), search);
      SET_PTR(NEXT_FREEP(search), bp);
      SET_PTR(NEXT_FREEP(bp), NULL);
      seg_list[findClass] = bp;
    }
    else if (!search && insert)
    {
      /* printf("Running 2a of add_block\n"); */
      SET_PTR(PREV_FREEP(bp), NULL);
      SET_PTR(NEXT_FREEP(bp), insert);
      SET_PTR(PREV_FREEP(insert), bp);
    }

    else{
      /* printf("Running 2b of add_block\n"); */
      SET_PTR(PREV_FREEP(bp), NULL);
      SET_PTR(NEXT_FREEP(bp), NULL);
      seg_list[findClass] = bp;
    }
    /* mm_check(); */
    return bp;
}


static void *remove_block(void *bp) { /* remove block from seg list */
    int i = 0;
    size_t size = GET_SIZE(HDRP(bp));

    while ((i < MAX_SEGLIST_SIZE - 1) && (size > 1)) {
        size = size / 2;
        i++;
    }

    if (PREV_SEGP(bp) != NULL && NEXT_SEGP(bp) != NULL)
    {
      SET_PTR(NEXT_FREEP(PREV_SEGP(bp)), NEXT_SEGP(bp));
      SET_PTR(PREV_FREEP(NEXT_SEGP(bp)), PREV_SEGP(bp));
    }

    else if (PREV_SEGP(bp) != NULL && NEXT_SEGP(bp) == NULL)
    {
      SET_PTR(NEXT_FREEP(PREV_SEGP(bp)), NULL);
      seg_list[i] = PREV_SEGP(bp);
    }

    else if (PREV_SEGP(bp) == NULL && NEXT_SEGP(bp) != NULL)
    {
      SET_PTR(PREV_FREEP(NEXT_SEGP(bp)), NULL);
    }
    else{
      seg_list[i] = NULL;
    }

    /* mm_check(); */
    return bp;
}


static void *coalesce(void *bp)
/* Remove block from the heap, check its neighbors to see what needs to be moved.*/
/* Place removed block on seg_list*/
{
    size_t prev_alloc = GET_ALLOC(HDRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (PREV_BLKP(bp) == bp) /* We already know bp is allocated */
    {
      prev_alloc = 1;
    }

    if (prev_alloc && next_alloc) /* Case 1*/
    {
        return bp;
    }
    else if (prev_alloc && !next_alloc) { /* Case 2*/
        remove_block(bp);
        remove_block(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        /* Put newly freed blocks on seg list*/
        PUT_SEG_LIST(HDRP(bp), PACK(size, 0));
        PUT_SEG_LIST(FTRP(bp), PACK(size, 0));
    } else if (!prev_alloc && next_alloc) { /* Case 3 */
        remove_block(bp);
        remove_block(PREV_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT_SEG_LIST(FTRP(bp), PACK(size, 0));
        PUT_SEG_LIST(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    } else { /* Case 4*/
        remove_block(bp);
        remove_block(PREV_BLKP(bp));
        remove_block(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT_SEG_LIST(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT_SEG_LIST(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    /* mm_check(); */

    add_block(bp, size);

    return bp;
}

static void *place(void *bp, size_t asize) /* Place block on seg list*/
{
    size_t csize = GET_SIZE(HDRP(bp)); /* Size of current bp*/
    size_t remainder = csize - asize; /* Calculate once to increase efficiency*/

    remove_block(bp);

    if (remainder <= OVERHEAD) {
        /* Block already fits, no need to split*/
        PUT_SEG_LIST(HDRP(bp), PACK(csize, 1));
        PUT_SEG_LIST(FTRP(bp), PACK(csize, 1));
    }

    else if (asize >= 50) {
        /* Split block if it's too large*/
        PUT_SEG_LIST(HDRP(bp), PACK(remainder, 0));
        PUT_SEG_LIST(FTRP(bp), PACK(remainder, 0));
        PUT(HDRP(NEXT_BLKP(bp)), PACK(asize, 1)); /* Pack by asize*/
        PUT(FTRP(NEXT_BLKP(bp)), PACK(asize, 1));
        add_block(bp, remainder);
        return NEXT_BLKP(bp);

    }
    else {
        PUT_SEG_LIST(HDRP(bp), PACK(asize, 1));
        PUT_SEG_LIST(FTRP(bp), PACK(asize, 1));
        PUT(HDRP(NEXT_BLKP(bp)), PACK(remainder, 0)); /* Pack by remainder since it's smaller */
        PUT(FTRP(NEXT_BLKP(bp)), PACK(remainder, 0));
        add_block(NEXT_BLKP(bp), remainder);
    }
    /* mm_check(); */
    return bp;
}

static int mm_check() { /* Check consistency of heap */
  int ret_val = 1;
  void *bp = heap_listp;
  printf("Heap Pointer Address: %p \n", heap_listp);

  /*Check for prologue header */
  printf("Checking prologue header: \n");
  if (checkblock(heap_listp) == 0)
    ret_val = checkblock(heap_listp); /*should indicate whether or not the alignment is off */
  printblock(heap_listp);

  if (!GET_ALLOC(HDRP(heap_listp)))
  {
    printf("Error: Prologue Header not allocated \n");
    printf("Printing address of header: %d \n", GET(HDRP(heap_listp)));
    ret_val = 0;
  }
  /* Traverse heap_listp */
  int i = 0;
  for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp))
  {
    if (i == 0)
    {
      printf("Traversing heap_listp...\n");
      i+=1;
    }
    printblock(bp);
    if (checkblock(heap_listp) == 0)
      ret_val = checkblock(bp);
  }

  /*Check for epilogue header */

  if ((GET_SIZE(HDRP(bp)) != 0) || !(GET_ALLOC(HDRP(bp))))
  {
    ret_val = 0;
    printf("Error: Bad epliogue header \n");
  }

  int j = 0;
  while ((seg_list[j] != NULL) && (j < MAX_SEGLIST_SIZE - 1))
  {
    bp = seg_list[j];
    if (j == 0)
    {
      printf("Traversing seg_list...\n");
    }
    size_t csize;
    size_t nextSize;
    /* ascending check */
    while (NEXT_SEGP(bp) != NULL){

      csize = GET_SIZE(HDRP(bp)); /* Get current size */

      nextSize = GET_SIZE(NEXT_SEGP(HDRP(bp))); /* Get next size */
      if (nextSize < csize)
        printf("Error: Segment List is not in ascending order \n");
        ret_val = 0;
      bp = NEXT_SEGP(bp);
    }
    j++;
    printblock(bp);
    checkblock(bp);
  }

  return ret_val; /* Everything's fine*/
}

static void printblock(void *bp) /* rewrite */
{
  int hsize, halloc, fsize, falloc;

  hsize = GET_SIZE(HDRP(bp));
  halloc = GET_ALLOC(HDRP(bp));
  fsize = GET_SIZE(FTRP(bp));
  falloc = GET_ALLOC(FTRP(bp));

  if (hsize == 0) {
    printf("%p: end of heap\n", bp);
    return;
  }
  /* Check if header and footer are aligned for each block */
  printf("%p: header: [%d:%c] footer: [%d:%c]\n", bp,
  hsize, (halloc ? 'a' : 'f'),
  fsize, (falloc ? 'a' : 'f'));
}

static int checkblock(void *bp)
{
  printf("Printing address of header: %d \n", GET(HDRP(bp)));
  printf("Printing address of footer: %d\n", GET(FTRP(bp)));

  if ((GET_SIZE(bp) % 8) != 0)
  {
    printf("Error: %p is not doubleword aligned\n", bp);
    return 0;
  }


  if (GET(HDRP(bp)) != GET(FTRP(bp)))
  printf("Error: header does not match footer\n");
  return 0;

  return 1;
}
