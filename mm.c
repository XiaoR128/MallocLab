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
#define GET(bp)              (*(unsigned int *)(bp))
#define PUT(bp, val)         (*(unsigned int *)(bp) = (val))
#define GET_SIZE(bp)         (GET(bp) & ~0x7)
#define GET_ALLOC(bp)        (GET(bp) & 0x1)
#define HDRP(bp)            ((char *)(bp) - WSIZE)
#define FTRP(bp)            ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Next and previous blocks, allocated or not allocated */
#define NEXT_BLKP(bp)       ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp)       ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

#define NEXT_FREEP(bp)     ((char *)(bp) + WSIZE) /* Gets the address of next free block */
#define PREV_FREEP(bp)     ((char * )(bp))
#define OVERHEAD            16

/* Segregated List */
#define MAX_SEGLIST_SIZE    10 /*10 size classes */
/* Pointers within the partitions themselves - could be helpful when building each class*/
#define NEXT_SEGP(bp)       (*(char **)(bp))
#define PREV_SEGP(bp)       (*(char **)(PREV_FREEP(bp)))

/* Realloc tags - prevent something from being reallocated several times */

static char *heap_listp = 0;
static char *seg_list[MAX_SEGLIST_SIZE];

static void *extend_heap(size_t words);
static void place(void *bp, size_t asize);
static void *find_fit(size_t asize);
static void *coalesce(void *bp);
static void printblock(void *bp);
static void checkblock(void *bp);
static void mm_check();
static void remove_block(void *bp);
static void* add_block(void *bp, size_t asize);


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
  /*Allocate memory for prologue and epilogue */
  if ((heap_listp = mem_sbrk(OVERHEAD)) == (void *)-1){
    return -1;
  }

  /* initialize segregated list */
  for (int i = 0; i < MAX_SEGLIST_SIZE; i++)
  {
    seg_list[i] = (char *)NULL;
  }

  seg_list[0] = heap_listp; /*Everything is free, store first block into seg_list */

  PUT(heap_listp, 0);                                                           /* Alignment padding (4 bytes)*/
  PUT(heap_listp + (1*WSIZE), PACK(OVERHEAD, 1));                               /* Prologue header (4 bytes)*/
  PUT(heap_listp + (2*WSIZE), PACK(OVERHEAD, 1));                                /* Prologue footer (4 bytes)*/
  /*Prologue together header + footer = 8 */
  PUT(heap_listp + (3*WSIZE), PACK(0, 1));                                       /* Epilogue Header (4 bytes)*/
  heap_listp = (heap_listp + (2*WSIZE));

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
  /* immediate coalescing implementation -> try to defer it*/
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

  add_block(bp, size);
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
  add_block(bp, size);
  exit(0);
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
  /*
  void *bp;
  for (bp = free_listp; GET_ALLOC(HDRP(bp)) == 0; bp = NEXT_FREEP(bp)) {
    if (asize <= GET_SIZE(HDRP(bp))) {
      return bp;
    }
  } */
  return NULL; /* No fit */
}

static void remove_block(void *bp)
{
  return;
}

static void* add_block(void *bp, size_t asize) {
  /*Find the class the block belongs in */
  int findClass = 0;
  char *search = bp;
  char *insert = NULL;

  for (; ((findClass < MAX_SEGLIST_SIZE - 1) && (asize > 1)); findClass++)
  {
    asize = asize / 2; /*All lists are sorted by powers of 2 */
  }

  search = seg_list[findClass];

  /*Search through linked list and insert block; keep blogs in ascending order */
  while ((search != NULL) && (asize > GET_SIZE(HDRP(search))))
  {
    insert = search;
    search = PREV_SEGP(search);
  }
  /* Ugh too many pointers. Make sure everything on the list is right */
  if (search != NULL) /* Watch out for null access errors!!!*/
  {
    if (insert)
    {
      PUT(PREV_SEGP(bp),(unsigned int)search);
      PUT(NEXT_SEGP(search),(unsigned int)bp);
      PUT(NEXT_SEGP(bp),(unsigned int)insert);
      PUT(PREV_SEGP(insert),(unsigned int)bp);
    }
    else
    {
      PUT(PREV_SEGP(bp),(unsigned int)search);
      PUT(NEXT_SEGP(search),(unsigned int)bp);
      PUT(NEXT_SEGP(bp),(unsigned int)NULL);
      seg_list[findClass] = bp;
    }
  }
  else
  {
    if (insert)
    {
      PUT(PREV_SEGP(bp),(unsigned int)NULL);
      PUT(NEXT_SEGP(bp),(unsigned int)insert);
      PUT(PREV_SEGP(insert),(unsigned int)bp);
    }
    else
    {
      PUT(PREV_SEGP(bp),(unsigned int)NULL);
      PUT(NEXT_SEGP(bp),(unsigned int)NULL);
      seg_list[findClass] = bp;
    }
  }
  /*Finds the block's place within the linked list */
  return bp;
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
    printf("Error: Prologue Header must be free");
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
