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

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))    

/* Basic constants and macros */
#define WSIZE 4              /* Word and header/footer size (bytes) */
#define DSIZE 8              /* Double word size (bytes) */
#define CHUNKSIZE (1<<12)    /* Extend heap by this amount (bytes) */
#define BLKSIZE 16          /* Minimum block size required */

#define MAX(x,y) ((x) > (y)? (x) : (y))

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc) ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p)              (*(unsigned int *)(p))
#define PUT(p, val)         (*(unsigned int *)(p) = (val))

/* Read the size and allocated fields from address p  */
#define GET_SIZE(p)         (GET(p) & ~0x7)
#define GET_ALLOC(p)        (GET(p) & 0x1) /*current block allocated */
#define GET_PREV_ALLOC(p)    (GET(p) & 0x2) /* previous allocated block */

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)            ((char *)(bp) - WSIZE)
#define FTRP(bp)            ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp)       ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp)       ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/* Address of next free blocks */
#define NEXT_FREEP(bp) (*(char **)((char *)(ptr) + DSIZE))  
#define PREV_FREEP(bp) ((*(char **)((char * )(ptr)))    

/* 

/* Global Variables */
static void *free_listp; /* segregated free list array */
static void *heap_listp; /* pointer to the first block */

/* Internal Helper Functions */

static void *extend_heap(size_t words);
static void *place(void *bp, size_t asize);
static void *find_fit(size_t asize);
static void *coalesce(void *bp);
static void printblock(void *bp); /* print header and footer */
static void checkblock(void *bp); /*check alignment of block */
static void mm_check();
static void insert_at_front(void *bp); /* LIFO Policy */
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
  /* Implemented using the textbook's solutions */

  /* Create the initial empty heap */
  if ((heap_listp = mem_sbrk(2*BLKSIZE)) == (void *) - 1 )
    return -1;

  PUT(heap_listp, 0); /* Padding */                                                       
  PUT(heap_listp + (1*WSIZE), PACK(OVERHEAD, 1)); /*Prologue Header */                            
  PUT(heap_listp + (2*WSIZE), 0); /* Previous pointer */                                            
  PUT(heap_listp + (3*WSIZE), 0); /* Next pointer */                                       
  PUT(heap_listp + OVERHEAD, PACK(OVERHEAD, 1)); /* Prologue footer */                               
  PUT(heap_listp + OVERHEAD + WSIZE, PACK(0, 1)); /* Epilogue header/Boundary Tag */                              
  

  free_listp = heap_listp + (DSIZE); /* Track all free blocks */
  heap_listp = (heap_listp + (2*WSIZE)); /* Pointer to the first block */

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
  char *bp;                        /* Use to search through list and find a fit */

  if (heap_listp == 0) {
    mm_init();
  }
  /* Ignore spurious requests */
  if (size == 0)
    return NULL;

  /* Adjust block size to include overhead and alignment reqs */
  if ((ALIGN(size) + DSIZE) > BLKSIZE) {
    asize = ALIGN(size) + DSIZE;
  }
  else {
    asize = BLKSIZE;
  }

  /* Search the free list for a fit */
  if ((bp = find_fit(asize)) != NULL) {
    place(bp, asize);
    return bp;
  }

  /* Get more memory if no fit found */
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
  if (bp == 0){
    return;
  }

  size_t size = GET_SIZE(HDRP(bp));

  PUT(HDRP(bp), PACK(size, 0));
  PUT(FTRP(bp), PACK(size, 0));
  coalesce(bp);

}

static void *coalesce(void *bp)
{
  size_t prev_alloc;
  /* Check if bp is the first block and check if it's allocated */
  if ((PREV_BLKP(bp) == bp) && GET_ALLOC(bp)) {
    prev_alloc = 1;
  }
  /* Check if the previouis block is allocated */
  else {
    prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
  }

  size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
  size_t size = GET_SIZE(HDRP(bp));

  if (prev_alloc && next_alloc)              /* Case 1, both allocated */
  {
    /* Maintain LIFO Policy and return bp as free */
    insert_at_front(bp);
    return bp;
  }

  else if (prev_alloc && !next_alloc)        /* Case 2 */
  {
    size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
    /* Since the next block isn't allocated, you can move it */
    if (PREV_FREEP(NEXT_BLKP(bp))) { /*find the previous free block of the next block */
      NEXT_FREEP(PREV_FREEP(NEXT_BLKP(bp))) = NEXT_FREEP(NEXT_BLKP(bp));
    }
    else {
      free_listp = NEXT_FREEP(NEXT_BLKP(bp));
    }
    PREV_FREEP(NEXT_FREEP(NEXT_BLKP(bp))) = PREV_FREEP(NEXT_BLKP(bp));

    /*Reset boundary tags */
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
  }

  else if (!prev_alloc && next_alloc)       /* Case 3 */
  {
    size += GET_SIZE(HDRP(PREV_BLKP(bp)));
    /* Remove previous block since it's not allocated */
    if (PREV_FREEP(PREV_BLKP(bp))) { /*find the previous free block of the previous block */
      NEXT_FREEP(PREV_FREEP(PREV_BLKP(bp))) = NEXT_FREEP(PREV_BLKP(bp));
    }
    else {
      free_listp = NEXT_FREEP(PREV_BLKP(bp));
    }
    PREV_FREEP(NEXT_FREEP(PREV_BLKP(bp))) = PREV_FREEP(PREV_BLKP(bp));

    /*reset boundary tags */
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
  }
  else                                        /* Case 4*/
  {
    /*Since neither blocks are allocated, remove both */
    size += GET_SIZE(HDRP(PREV_BLKP(bp))) +
    GET_SIZE(HDRP(NEXT_BLKP(bp)));
    /*remove previous */
    if (PREV_FREEP(PREV_BLKP(bp))) { /*find the previous free block of the previous block */
      NEXT_FREEP(PREV_FREEP(PREV_BLKP(bp))) = NEXT_FREEP(PREV_BLKP(bp));
    }
    else {
      free_listp = NEXT_FREEP(PREV_BLKP(bp));
    }
    PREV_FREEP(NEXT_FREEP(PREV_BLKP(bp))) = PREV_FREEP(PREV_BLKP(bp));
    /*remove next */
    if (PREV_FREEP(NEXT_BLKP(bp))) { /*find the previous free block of the next block */
      NEXT_FREEP(PREV_FREEP(NEXT_BLKP(bp))) = NEXT_FREEP(NEXT_BLKP(bp));
    }
    else {
      free_listp = NEXT_FREEP(NEXT_BLKP(bp));
    }
    PREV_FREEP(NEXT_FREEP(NEXT_BLKP(bp))) = PREV_FREEP(NEXT_BLKP(bp));

    /* Reset boundary tags */
    PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
    PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
  }

  insert_at_front(bp); /* LIFO */
  return bp;
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
  size_t oldsize;
  void *newptr;

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
  newptr = mm_malloc(size);

  /* if realloc() fails the original block is left untouched */
 if (!newptr) {
  return 0;
 }
  /* copy the old data. */
 oldsize = GET_SIZE(HDRP(ptr));
 if(size < oldsize) oldsize = size;
 memcpy(newptr, ptr, oldsize);

 /* Free the old block */
 mm_free(ptr);
 return newptr;

}


/* Inernal Helper Functions */


static void *extend_heap(size_t words)
{
  char *bp;
  size_t size;

  /* Allocate an even number of words to maintain alignment */
  size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
  if ((long)(bp = mem_sbrk(size)) == -1)
    return NULL;

  /* initialize free block header/footer and the epilogue header */
  PUT(HDRP(bp), PACK(size, 0));               /* Free block header */
  PUT(FTRP(bp), PACK(size, 0));               /* Free block footer */
  PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));       /* New epilogue header */

  /* Coalesce if the previous block was free */
  return coalesce(bp);

}


static void place(void *bp, size_t asize)
{
  size_t csize = GET_SIZE(HDRP(bp));

  if ((csize - asize) >= (BLKSIZE)) {
    PUT(HDRP(bp), PACK(asize, 1));
    PUT(FTRP(bp), PACK(asize, 1));
    bp = NEXT_BLKP(bp);
    PUT(HDRP(bp), PACK(csize - asize, 0));
    PUT(FTRP(bp), PACK(csize - asize, 0));
  }
  else
  {
    PUT(HDRP(bp), PACK(csize, 1));
    PUT(FTRP(bp), PACK(csize, 1));
  }
}

static void *find_fit(size_t asize)
{
  /* First-fit search */
  void *bp;
  for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
    if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
      return bp;
    }
  }
  return NULL; /* No fit */
}

/* mm_check -> check heap for consistency */

static void mm_check() {
  char *bp;


  printf("Heap (%p):\n", heap_listp);

  for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
      printblock(bp);
      checkblock(bp);
    } 
  /* Prologue header check */
  if ((GET_SIZE(HDRP(heap_listp)) != DSIZE) || !GET_ALLOC(HDRP(heap_listp))) {
    printf("Bad prologue header\n");
    checkblock(heap_listp);
    }
  /*Epilogue header check */
    printblock(bp);

  if ((GET_SIZE(HDRP(bp)) != 0) || !(GET_ALLOC(HDRP(bp)))) {
    printf("Bad epilogue header\n");
  }

}

static void printblock(void *bp)
{
    /* Print boundary tags for each block */
    if (GET_SIZE(HDRP(bp)) == 0) {
    printf("%p: end of heap\n", bp);
    return;
    }

    printf("%p: header: [%d:%c] footer: [%d:%c]\n", bp,
       GET_SIZE(HDRP(bp)), (GET_ALLOC(HDRP(bp)) ? 'a' : 'f'),
       GET_SIZE(FTRP(bp)), (GET_ALLOC(FTRP(bp)) ? 'a' : 'f'));
}


static void checkblock(void *bp)
{
    if ((size_t)bp % 8)
    printf("Error: %p is not aligned by 8\n", bp);
    if (GET(HDRP(bp)) != GET(FTRP(bp)))
    printf("Error: header does not match footer\n");
}

static void insert_at_front(void *bp) {
  NEXT_FREEP(bp) = free_listp;
  PREV_FREEP(free_listp) = bp; /* bp is no longer free */
  PREV_FREEP(bp) = NULL;
  free_listp = bp/
}