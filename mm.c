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

#define ALIGNMENT 8
#define ALIGN(size)         (((size) + (ALIGNMENT - 1)) & ~0x7)
#define SIZE_T_SIZE         (ALIGN(sizeof(size_t)))


#define WSIZE               4
#define DSIZE               8
#define CHUNKSIZE           (1<<12)
#define MAX(x,y)            ((x) > (y)? (x) : (y))
#define PACK(size, alloc)   ((size) | (alloc))
#define GET(p)              (*(unsigned int *)(p))
#define PUT(p, val)         (*(unsigned int *)(p) = (val))
#define GET_SIZE(p)         (GET(p) & ~0x7)
#define GET_ALLOC(p)        (GET(p) & 0x1)
#define HDRP(bp)            ((char *)(bp) - WSIZE)
#define FTRP(bp)            ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)
#define NEXT_BLKP(bp)       ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp)       ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))
//
#define NEXT_FREEP(ptr)     (*(char **)((char *)(ptr) + DSIZE))
#define PREV_FREEP(ptr)     (*(char **)((char * )(ptr)))
#define OVERHEAD            16


static char *heap_listp = 0;
static char *free_listp = 0;

static void *extend_heap(size_t words);
static void place(void *bp, size_t asize);
static void *find_fit(size_t asize);
static void *coalesce(void *bp);
static void printblock(void *bp);
static void checkblock(void *bp);
static void mm_check();
static void remove_block(void *bp);
static void insert_at_front(void *bp);


/*
mm_init - initialize the malloc package.
before calling malloc, realloc, or free, calls init to
perform any necessary initializaations (such as allocating
the initial heap area)
the return value should be -1 if there was a problem in
performing the initialization. 0 otherwise.
*/
int mm_init(void)
{

  /* Create the initial empty heap(free list) */
  if ((heap_listp = mem_sbrk(2*OVERHEAD)) == (void *)-1){
    return -1;
  }
  PUT(heap_listp, 0);                                                           /* Alignment padding */
  PUT(heap_listp + (1*WSIZE), PACK(OVERHEAD, 1));                               /* Prologue header */
  PUT(heap_listp + (2*WSIZE), 0);                                               /* Previous pointer */
  PUT(heap_listp + (3*WSIZE), 0);                                               /* Next Pointer */
  PUT(heap_listp + OVERHEAD, PACK(OVERHEAD, 1));                                /* Prologue footer */
  PUT(heap_listp + OVERHEAD + WSIZE, PACK(0, 1));                               /* Epilogue Header */
  free_listp = heap_listp + (DSIZE);
  heap_listp = (heap_listp + (2*WSIZE));

  mm_check();

  /* Extend the empty heap with a free block of CHUNKSIZE bytes */
  if (extend_heap(CHUNKSIZE/WSIZE) == NULL)
  return -1;

  return 0;
}

/*
* mm_malloc - Allocate a block by incrementing the brk pointer.
*     Always allocate a block whose size is a multiple of the alignment.
*/
void *mm_malloc(size_t size)
{
  size_t asize;                    /* Adjusted block size */
  size_t extendsize;               /* Amount to extend heap if no fit */
  char *bp;
  if (heap_listp == 0) {
    mm_init();
  }
  /* Ignore spurious requests */
  if (size == 0){
    return NULL;
  }

  asize = MAX(ALIGN(size) + DSIZE, OVERHEAD);
  /* Search the free list for a fit */
  if ((bp = find_fit(asize)) != NULL) {
    place(bp, asize);
    return bp;
  }

  /* No fit found. Get more memory and place the block */
  extendsize = MAX(asize, CHUNKSIZE);
  if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
  {
    return NULL;
  }

  place(bp,asize);
  return bp;
}

/*
* mm_free - Freeing a block does nothing.
*/
void mm_free(void *bp)
{
 //printf("starting free \n");

  if (!bp){
    return;
  }

  size_t size = GET_SIZE(HDRP(bp));

  PUT(HDRP(bp), PACK(size, 0));
  PUT(FTRP(bp), PACK(size, 0));
  coalesce(bp);

}

static void *coalesce(void *bp)
{

  size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))) || PREV_BLKP(bp) == bp;
  size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
  size_t size = GET_SIZE(HDRP(bp));


  if (prev_alloc && !next_alloc)        /* Case 2 */
  {
    size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
    remove_block(NEXT_BLKP(bp));
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
  }

  else if (!prev_alloc && next_alloc)       /* Case 3 */
  {
    size += GET_SIZE(HDRP(PREV_BLKP(bp)));
    bp = PREV_BLKP(bp);
    remove_block(bp);
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
  }
  else if (!prev_alloc && !next_alloc)                                      /* Case 4*/
  {
    size += GET_SIZE(HDRP(PREV_BLKP(bp))) +
    GET_SIZE(HDRP(NEXT_BLKP(bp)));
    remove_block(PREV_BLKP(bp));
    remove_block(NEXT_BLKP(bp));
    bp = PREV_BLKP(bp);
    PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
    PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
  }

  insert_at_front(bp);
  return bp;
}

/*
* mm_realloc - Implemented simply in terms of mm_malloc and mm_free
*/
void *mm_realloc(void *ptr, size_t size)
{
  size_t oldsize;
  void *newptr;
  size_t asize = MAX(ALIGN(size) + DSIZE, OVERHEAD);

  /* If size == 0 then this is just free, and we return NULL */
  if(size == 0)
  {
    mm_free(ptr);
    return 0;
  }

  /* if oldptr is NULL then this is just malloc */
  if (ptr == NULL)
  {
    return mm_malloc(size);
  }
  oldsize = GET_SIZE(HDRP(ptr));

  /* copy the old data. */
  if(oldsize == asize){
    return ptr;
  }
  if(asize <= oldsize){
    size = asize;
    if(oldsize - size <= OVERHEAD){
      return ptr;
    }

    PUT(HDRP(ptr), PACK(size,1));
    PUT(FTRP(ptr), PACK(size,1));
    PUT(HDRP(NEXT_BLKP(ptr)), PACK(oldsize - size, 1));
    mm_free(NEXT_BLKP(ptr));
    return ptr;
  }
  newptr = mm_malloc(size);

  /* if realloc() fails the original block is left untouched */
  if (!newptr) {
    return 0;
  }

  if(size < oldsize){
    oldsize = size;
  }
  memcpy(newptr, ptr, oldsize);

  /* Free the old block */
  mm_free(ptr);
  return newptr;
}

static void *extend_heap(size_t words)
{
  char *bp;
  size_t size;

  /* Allocate an even number of words to maintain alignment */
  size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
  if (size < OVERHEAD) {
    size = OVERHEAD;
  }
  if ((long)(bp = mem_sbrk(size)) == -1){
  return NULL;
}

  PUT(HDRP(bp), PACK(size, 0));               /* Free block header */
  PUT(FTRP(bp), PACK(size, 0));               /* Free block footer */
  PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));       /* New epilogue header */

  /* Coalesce if the previous block was free */
  return coalesce(bp);

}


static void place(void *bp, size_t asize)
{
  size_t csize = GET_SIZE(HDRP(bp));

  if ((csize - asize) >= (OVERHEAD)) {
    PUT(HDRP(bp), PACK(asize, 1));
    PUT(FTRP(bp), PACK(asize, 1));
    remove_block(bp);
    bp = NEXT_BLKP(bp);
    PUT(HDRP(bp), PACK(csize - asize, 0));
    PUT(FTRP(bp), PACK(csize - asize, 0));
    coalesce(bp);
  }
  else
  {
    PUT(HDRP(bp), PACK(csize, 1));
    PUT(FTRP(bp), PACK(csize, 1));
    remove_block(bp);
  }
}

static void *find_fit(size_t asize)
{
  /* First-fit search */
  void *bp;
  for (bp = free_listp; GET_ALLOC(HDRP(bp)) == 0; bp = NEXT_FREEP(bp)) {
    if (asize <= GET_SIZE(HDRP(bp))) {
      return bp;
    }
  }
  return NULL; /* No fit */
}

static void remove_block(void *bp)
{
  if (PREV_FREEP(bp)) {
    NEXT_FREEP(PREV_FREEP(bp) = NEXT_FREEP(bp));
  }
  else{
    free_listp = NEXT_FREEP(bp);
  }
  PREV_FREEP(NEXT_FREEP(bp)) = PREV_FREEP(bp);
}

static void insert_at_front(void *bp) {
  NEXT_FREEP(bp) = free_listp;

  PREV_FREEP(free_listp) = bp;

  PREV_FREEP(bp) = NULL;
  free_listp = bp;
}
/*
* mm_checkheap - Check the heap for consistency (not checking free_listp list)
*/

static void mm_check()
{
  void *bp = heap_listp;
  printf("Heap Pointer Address: %p \n", heap_listp);

  /*Check for prologue header */
  printf("Checking prologue header: \n");
  checkblock(heap_listp); /*should indicate whether or not the alignment is off */
  printblock(heap_listp);
  if (!GET_ALLOC(HDRP(heap_listp)))
  {
    printf("Error: Prologue Header not allocated");
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
    checkblock(bp);
  }
  printblock(bp);
  checkblock(bp);
  /*Check for epilogue header */

  if ((GET_SIZE(HDRP(bp)) != 0) || !(GET_ALLOC(HDRP(bp))))
  {
    printf("Error: Bad epliogue header \n");
  }

  /* Traverse list of free blocks */
  int j = 0;
  for (bp = free_listp; GET_ALLOC(HDRP(bp)) == 0; bp = NEXT_FREEP(bp))
  {
    if (j == 0)
    {
      printf("Traversing free_listp...\n");
      j+=1;
    }
    printblock(bp);
    checkblock(bp);
  }
}

static void printblock(void *bp) /* change later on */
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

  printf("%p: header: [%d:%c] footer: [%d:%c]\n", bp,
  hsize, (halloc ? 'a' : 'f'),
  fsize, (falloc ? 'a' : 'f'));
}

static void checkblock(void *bp) /* change later on */
{

  if ((size_t)bp % 8)
  printf("Error: %p is not doubleword aligned\n", bp);

  if (GET(HDRP(bp)) != GET(FTRP(bp)))
  printf("Error: header does not match footer\n");
}
