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
#include "mm.h"

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "individaul",
    /* First member's full name */
    "coyorkdow",
    /* First member's email address */
    "coyorkdow@outlook.com",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

#define WSIZE 4  // word and header/footer size (bytes)
#define DSIZE 8  // double word size (bytes)
#define INITCHUNKSIZE (1 << 6)
#define CHUNKSIZE (1 << 12)

#define SEG_LIST_NUM 20
#define REALLOC_BUFFER (1 << 7)

#define MAX(x, y) ((x) > (y) ? (x) : (y))
#define MIN(x, y) ((x) < (y) ? (x) : (y))

// Pack a size and allocated bit into a word
#define PACK(size, alloc) ((size) | (alloc))

// Read and write a word at address p
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

// Read the size and allocation bit from address p
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)
#define GET_TAG(p) (GET(p) & 0x2)

// Set or clear allocation bit
#define SET_ALLOC(p) PUT(p, (GET(p) | 0x1))
#define CLR_ALLOC(p) PUT(p, (GET(p) & ~0x1))

// Set block's size
#define SET_SIZE(p, size) PUT(p, (size | GET_ALLOC(p)))

// Address of block's header and footer
#define HDRP(ptr) ((char *)(ptr)-WSIZE)
#define FTRP(ptr) ((char *)(ptr) + GET_SIZE(HDRP(ptr)) - DSIZE)

// Address of (physically) next and previous blocks
#define NEXT_BLKP(ptr) ((char *)(ptr) + GET_SIZE((char *)(ptr)-WSIZE))
#define PREV_BLKP(ptr) ((char *)(ptr)-GET_SIZE((char *)(ptr)-DSIZE))

// Address of free block's predecessor and successor entries
#define PRED_PTR(ptr) ((char *)(ptr))
#define SUCC_PTR(ptr) ((char *)(ptr) + WSIZE)

#define BP_SMALLER(bp, size) (GET_SIZE(HDRP(bp)) < size)
#define BP_LARGER_EQUAL(bp, size) (GET_SIZE(HDRP(bp)) >= size)

static char *heap_listp = 0; /* Pointer to the prologue block */

static char *free_list_head = 0; /* Pointer to the head of explicit free list*/

// Address of free block's predecessor and successor
#define PRED(ptr) (char *)(free_list_head + GET(PRED_PTR(ptr)))
#define SUCC(ptr) (char *)(free_list_head + GET(SUCC_PTR(ptr)))

#define OFFSET(ptr) ((char *)(ptr)-free_list_head)

// Set blocks's predecessor and successor entries
#define SET_PRED(self, ptr) PUT(PRED_PTR(self), OFFSET(ptr))
#define SET_SUCC(self, ptr) PUT(SUCC_PTR(self), OFFSET(ptr))

// Link ptr1 and ptr2 as ptr1 is predecessor of ptr2
#define LINK(ptr1, ptr2)  \
  do {                    \
    SET_SUCC(ptr1, ptr2); \
    SET_PRED(ptr2, ptr1); \
  } while (0)

// Remove ptr from linked list
#define ERASE(ptr) LINK(PRED(ptr), SUCC(ptr))

// Insert target as successor
#define INSERT(self, target)  \
  do {                        \
    LINK(target, SUCC(self)); \
    LINK(self, target);       \
  } while (0)

static void *extend_heap(size_t words);

static void *coalesce(void *bp);

static void *find_fit(size_t asize);

static void place(void *bp, size_t asize);

/*
 * mm_init - initialize the malloc package.
 */
int mm_init(void) {
  /* Create the initial empty heap */
  if ((heap_listp = mem_sbrk(6 * WSIZE)) == (void *)-1) {
    return -1;
  }
  free_list_head = heap_listp + WSIZE; /* Init head ptr */
  PUT(heap_listp, 0);                  /* Alignment padding */
  PUT(heap_listp + WSIZE, 0);
  PUT(heap_listp + (2 * WSIZE), 0);
  PUT(heap_listp + (3 * WSIZE), PACK(DSIZE, 1)); /* Prologue header */
  PUT(heap_listp + (4 * WSIZE), PACK(DSIZE, 1)); /* Prologue footer */
  PUT(heap_listp + (5 * WSIZE), PACK(0, 1));     /* Epilogue header */
  heap_listp += (4 * WSIZE);

  /* Extend the empty heap with a free block of CHUNKSIZE bytes */
  if (extend_heap(CHUNKSIZE / WSIZE) == NULL) {
    return -1;
  }
  INSERT(free_list_head, NEXT_BLKP(heap_listp));
  return 0;
}

static void *extend_heap(size_t words) {
  char *bp;
  size_t size;

  /* Allocate an even number of words to maintain alignment */
  size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
  if ((long)(bp = mem_sbrk(size)) == -1) {
    return NULL;
  }

  /* Initialize free block header/footer and the epilogue header */
  PUT(HDRP(bp), PACK(size, 0));         /* Free block header */
  PUT(FTRP(bp), PACK(size, 0));         /* Free block footer */
  PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */

  /* Coalesce if the previous block was free */
  return coalesce(bp);
}

/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size) {
  size_t asize;      /* Adjusted block size */
  size_t extendsize; /* Amount to extend heap if no fit */
  char *bp;

  /* Ignore spurious requests */
  if (size == 0) {
    return NULL;
  }

  /* Adjust block size to include overhead and alignment reqs. */
  if (size <= DSIZE)
    asize = 2 * DSIZE;
  else
    asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);

  /* Search the free list for a fit */
  if ((bp = find_fit(asize)) != NULL) {
    place(bp, asize);
    return bp;
  }

  /* No fit found. Get more memory and place the block */

  extendsize = MAX(asize, CHUNKSIZE);
  if ((bp = extend_heap(extendsize / WSIZE)) == NULL) {
    return NULL;
  }
  INSERT(free_list_head, bp);
  place(bp, asize);
  return bp;
}

/*
 * find_fit - Perform a first-fit search of the implicit free list.
 */
void *find_fit(size_t asize) {
  char *ptr = free_list_head;
#ifdef DEBUG
  printf("head ptr = %p\n", ptr);
  printf("cur = %p, pred = %p, succ = %p\n", ptr, PRED(ptr), SUCC(ptr));
  int cnt = 0;
#endif
  while ((ptr = SUCC(ptr)) != free_list_head) {
#ifdef DEBUG
    cnt++;
    if (cnt == 10000) exit(1);
    printf("cur = %p, pred = %p, succ = %p\n", ptr, PRED(ptr), SUCC(ptr));
#endif
    if (GET_SIZE(HDRP(ptr)) >= asize) {
#ifdef DEBUG
      printf("[fit]  allocated = %d, addr = %p, size = %u, asize = %u\n",
             GET_ALLOC(HDRP(ptr)), ptr, GET_SIZE(HDRP(ptr)), asize);
#endif
      return ptr;
    }
#ifdef DEBUG
    printf("[skip]  allocated = %d, addr = %p, size = %u, asize = %u\n",
           GET_ALLOC(HDRP(ptr)), ptr, GET_SIZE(HDRP(ptr)), asize);
#endif
  }
  return NULL;
}

/*
 * place - Place the requested block at the beginning of the free block,
 * splitting only if the size of the remainder would equal or exceed the minimum
 * block size.
 */
void place(void *bp, size_t asize) {
#ifdef DEBUG
  printf("\n[before place] ptr is %p, pred = %p, succ = %p\n", bp, PRED(bp),
         SUCC(bp));
  printf("checking list...\n ");
  find_fit(1 << 31);
#endif
  SET_ALLOC(HDRP(bp));
  size_t size = GET_SIZE(HDRP(bp));
  if (size > asize && size - asize >= 2 * DSIZE) {
    size_t next_size = size - asize;
    SET_SIZE(HDRP(bp), asize);
    SET_SIZE(FTRP(bp), asize);
    char *next = NEXT_BLKP(bp);
    PUT(HDRP(next), PACK(next_size, 0));
    PUT(FTRP(next), PACK(next_size, 0));
    INSERT(free_list_head, next);
#ifdef DEBUG
    printf("[splitting] next ptr is %p, checking list...\n", next);
    find_fit(1 << 31);
#endif
  }
  SET_ALLOC(FTRP(bp));
  ERASE(bp);
#ifdef DEBUG
  printf("[after place] checking list...\n ");
  find_fit(1 << 31);
#endif
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr) {
  size_t size = GET_SIZE(HDRP(ptr));

  PUT(HDRP(ptr), PACK(size, 0));
  PUT(FTRP(ptr), PACK(size, 0));
#ifdef DEBUG
  printf("\n[before free] ptr is %p, checking list...\n", ptr);
  find_fit(1 << 31);
#endif
  ptr = coalesce(ptr);
  INSERT(free_list_head, ptr);
#ifdef DEBUG
  printf("[after free] ptr is %p, checking list...\n", ptr);
  find_fit(1 << 31);
#endif
}

static void *coalesce(void *bp) {
  size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
  size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
  size_t size = GET_SIZE(HDRP(bp));

  if (prev_alloc && next_alloc) { /* Case 1 */
    return bp;
  }

  else if (prev_alloc && !next_alloc) { /* Case 2 */
    ERASE(NEXT_BLKP(bp));
    size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
  }

  else if (!prev_alloc && next_alloc) { /* Case 3 */
    size += GET_SIZE(HDRP(PREV_BLKP(bp)));
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
    bp = PREV_BLKP(bp);
    ERASE(bp);
  }

  else { /* Case 4 */
    ERASE(NEXT_BLKP(bp));
    size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
    PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
    PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
    bp = PREV_BLKP(bp);
    ERASE(bp);
  }

  return bp;
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size) {
  void *oldptr = ptr;
  void *newptr;
  size_t copySize;

  newptr = mm_malloc(size);
  if (ptr == NULL || newptr == NULL) {
    return newptr;
  }

  copySize = MIN(GET_SIZE(HDRP(ptr)), GET_SIZE(HDRP(newptr)));
  memcpy(newptr, oldptr, copySize - WSIZE);
  mm_free(oldptr);
  return newptr;
}
