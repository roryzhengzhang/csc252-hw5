/*
 * mm.c - A malloc package relatively more efficient than the naive version.
 * 
 * In this implementation, it first searches the explicit free list for a suitable cache block. If one
 * is found, place the block accordingly; if not, extend the heap.
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
    "zzzxf",
    /* First member's full name */
    "Zheng Zhang",
    /* First member's email address */
    "roryzhang95@gmail.com",
    /* Second member's full name (leave blank if none) */
    "Xiaofei Zhou",
    /* Second member's email address (leave blank if none) */
    "zhouxf626@gmail.com"
};

/* Basic constants and macros */
#define WSIZE 4 
#define DSIZE 8 
#define CHUNKSIZE (1<<12)

#define SEGLIST_NUM 32 

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8
/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)
#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

#define MIN(x, y) ((x) < (y) ? (x) : (y))
#define MAX(x, y) ((x) > (y) ? (x) : (y))

/* Intergrate size and allocated bit */
#define PACK(size, alloc) ((size) | (alloc))

/* Read / write a word at address p */
#define GET(p)      (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

/* p should be either the header or footer */
#define GET_SIZE(p)  (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* Given the block ptr bp, compute address of the header/footer */
#define HDRP(bp)    ((char *)(bp) - WSIZE)
#define FTRP(bp)    ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given the block ptr bp, compute address of the next and previous block */
#define NEXT_BLKP(bp)   ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp)   ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/* Pointer declaration and operaton MACROs */
#define PRED_ADDR(bp) ((char *)(bp))
#define SUCC_ADDR(bp) ((char *)(bp) + WSIZE)

/* Dereferencing */
#define PRED(bp) (*(char **)(bp))
#define SUCC(bp) (*(char **)(SUCC_ADDR(bp)))

/* Store(write) the address/pointer into specified position */
#define STR_ADDR(p, ptr) (*(unsigned int *)(p) = (unsigned int)(ptr))

/* Segregated list related parameters */
#define SEG_CLASS_MIN 2  
#define SEG_STEP 2         
#define SEG_THRESHOLD (64 + 32)    


/* helper functions */
static void * extend_heap(size_t size);
static void * coalesce(void *bp);  
static void * place(void *bp, size_t adjusted_size);

/* Insert into / delete from the explicit free list */
static void insert(void *bp, size_t size);
static void delete(void *bp);

/* Global variables */
void * heap_start;
void * seg_list[SEGLIST_NUM]; 

/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    char * heap_list_pointer;

    if ((heap_list_pointer = mem_sbrk(4 * WSIZE)) == (void *)-1)
        return -1;

    PUT(heap_list_pointer, 0);
    /* Prologue header */
    PUT(heap_list_pointer + (1 * WSIZE), PACK(DSIZE, 1));
    /* Prologue footer */
    PUT(heap_list_pointer + (2 * WSIZE), PACK(DSIZE, 1));
    /* Epilogue header */
    PUT(heap_list_pointer + (3 * WSIZE), PACK(0, 1));
    heap_list_pointer += (2 * WSIZE); 
    heap_start = heap_list_pointer;

    /* Segregated free list initialization. */
    for (int seg_list_i = 0; seg_list_i < SEGLIST_NUM; ++seg_list_i) {
        seg_list[seg_list_i] = NULL;
    }

    /* !!! Tunable: try CHUNKSIZE also */
    if (extend_heap(CHUNKSIZE / DSIZE) == NULL)
        return -1;
    return 0;
}

/* 
 * mm_malloc - Allocate a new block in specified size.
 */
void *mm_malloc(size_t size)
{
    size_t adjusted_size;
    size_t extend_size;
    char * ptr = NULL;
    
    /* Ignore when the requested size is 0 */
    if (size == 0)
        return NULL;

    /* Calculate actual block size */
    if (size <= DSIZE)
        adjusted_size = 2 * DSIZE;
    else
        adjusted_size = ALIGN(size + DSIZE);
    
    size_t target_size = adjusted_size;
    /* Search for a suitable block in the free list. */
    for (int seg_list_i = 0; seg_list_i < SEGLIST_NUM; ++seg_list_i)
    {   
        if (((target_size < SEG_CLASS_MIN) && (seg_list[seg_list_i])) || \
            (seg_list_i == SEGLIST_NUM - 1)) {
            ptr = seg_list[seg_list_i];
            while ((ptr) && ((adjusted_size > GET_SIZE(HDRP(ptr)))))
                ptr = PRED(ptr);
            if (ptr) break;
        }
        target_size /= SEG_STEP;
    }

    if (!ptr){   /* If no fits found */
        extend_size = MAX(adjusted_size, CHUNKSIZE);
        ptr = extend_heap(extend_size);
        if(!ptr) return NULL;
    }
    
    // Place the requested block
    ptr = place(ptr, adjusted_size);
    return ptr;
}

/*
 * mm_free - Free a block by updating the allocation information
 */
void mm_free(void *ptr)
{
    size_t size = GET_SIZE(HDRP(ptr));

    /* Update the block header/footer */
    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));

    /* Insert into the free list. */
    insert(ptr, size);
    /* Combine free blocks. */
    coalesce(ptr);
}

/*
 * mm_realloc
 */
void *mm_realloc(void *ptr, size_t size)
{
    size_t new_size;     
    int extend_size;    

    if (!ptr)
        return mm_malloc(size);
    if (size == 0) {
        mm_free(ptr);
        return NULL;
    }
    /* Calculate the new block size. */
    new_size = (size <= DSIZE) ? (2 * DSIZE) : ALIGN(size + DSIZE);
    

    if (1) {
        // if (!next_allocated && next_size != 0) {
        int remainder = GET_SIZE(HDRP(ptr)) - new_size;

        unsigned int next_allocated = GET_ALLOC(HDRP(NEXT_BLKP(ptr)));
        int next_size = GET_SIZE(HDRP(NEXT_BLKP(ptr)));
        if (!next_allocated)
            remainder += next_size;

        if (remainder < 0) {
            /* If the current block is not big enough: */
            extend_size = MAX(-remainder, CHUNKSIZE);
            if (extend_heap(extend_size) == NULL) return NULL;
            remainder += extend_size;
        }
        /* Remove next block from the free list. */
        delete(NEXT_BLKP(ptr));
        /* Coalesce && Update tags. */
        PUT(HDRP(ptr), PACK(new_size + remainder, 1)); 
        PUT(FTRP(ptr), PACK(new_size + remainder, 1));
        return ptr; 
    }

    /* Allocate a new block. */
    /* In most cases, this part will not be executed. */
    void * new_ptr = mm_malloc(new_size);
    memcpy(new_ptr, ptr, MIN(size, new_size));
    mm_free(ptr);
    return new_ptr;
}

/*
 * mm_check - Heap checker prototype.
 */
void mm_check()
{
    void * ptr = heap_start;
    /* Check all blocks */
    for (; GET_SIZE(HDRP(ptr)) > 0;) {
        if (GET(HDRP(ptr)) != GET(FTRP(ptr))) printf("ERR: header footer match issue.\n");
        if(GET_SIZE(HDRP(ptr)) % ALIGNMENT) printf("ERR: Alignment issue.\n");
        ptr = NEXT_BLKP(ptr);
    }

    /* Check free list. */
    for (int seg_list_i = 0; (seg_list_i < SEGLIST_NUM);) {
        ptr = seg_list[seg_list_i];
        while ((ptr != NULL)) {
            if (GET_ALLOC(FTRP(ptr))) printf("ERR: free block not marked.\n");
            ptr = PRED(ptr);
        }
    }
    return;
}

/* 
 * HELPER FUNCTIONS 
 */
/*
 * extend_heap - Extend the heap with a new block.
 */
static void *extend_heap(size_t size)
{
    char *bp;
    /* Allocate an even number of words. */
    // Calculate the new block size.
    size_t adjusted_size = ALIGN(size);
    
    // Allocate a new block.
    if ((long)(bp = mem_sbrk(adjusted_size)) == -1)
        return NULL;

    /* Initialize free block header/footer */
    PUT(HDRP(bp), PACK(adjusted_size, 0)); 
    PUT(FTRP(bp), PACK(adjusted_size, 0)); 
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); 

    /* Insert the big chunk into the free list. */
    insert(bp, adjusted_size);
    return coalesce(bp);
}

/*
 * insert - Insert one block into the explicit free list.
 */
static void insert(void *ptr, size_t size) {
    void *t_ptr = NULL;  
    void *cur_ptr = NULL;  
    int seg_list_i = 0;  

    /* Find a suitable class */
    for (; (seg_list_i < SEGLIST_NUM) && (size >= SEG_CLASS_MIN);) {
        size /= SEG_STEP;
        seg_list_i += 1;
    }

    /* t_ptr: Starting pointer of the corresponding class. */
    t_ptr = seg_list[seg_list_i];
    
    /* Find the largest block of this class. */
    while ((t_ptr != NULL) && (size > GET_SIZE(HDRP(t_ptr)))) {
        cur_ptr = t_ptr;
        cur_ptr = PRED(t_ptr);
    }
    /*  Pointer list of one class:
        array_start: ptr1 (succ) <-> ptr2 (cur) <-> ptr3 (pred) <-> ... NULL
    */
    if (t_ptr) {
        if (cur_ptr) {
            STR_ADDR(SUCC_ADDR(t_ptr), ptr);
            STR_ADDR(PRED_ADDR(cur_ptr), ptr);

            STR_ADDR(PRED_ADDR(ptr), t_ptr);
            STR_ADDR(SUCC_ADDR(ptr), cur_ptr);
        } else {
            STR_ADDR(PRED_ADDR(ptr), t_ptr);
            STR_ADDR(SUCC_ADDR(ptr), NULL);

            STR_ADDR(SUCC_ADDR(t_ptr), ptr);
            seg_list[seg_list_i] = ptr;
        }
    } else {
        if (cur_ptr) {
            STR_ADDR(PRED_ADDR(ptr), NULL);
            STR_ADDR(SUCC_ADDR(ptr), cur_ptr);

            STR_ADDR(PRED_ADDR(cur_ptr), ptr);
        } else {
            STR_ADDR(PRED_ADDR(ptr), NULL);
            STR_ADDR(SUCC_ADDR(ptr), NULL);
            seg_list[seg_list_i] = ptr;
        }
    }
}

/*
 * delete - Delete one block from the explicit free list.
 */
static void delete(void *ptr) {
    int seg_list_i = 0;  
    size_t size = GET_SIZE(HDRP(ptr)); 

    /* Find a suitable class */
    for (; (seg_list_i < SEGLIST_NUM) && (size >= SEG_CLASS_MIN);) {
        size /= SEG_STEP;
        seg_list_i += 1;
    }
    /* Update the pointers of PRED and SUCC accordingly. */
    if (PRED(ptr)) {
        if (SUCC(ptr)) {
            STR_ADDR(SUCC_ADDR(PRED(ptr)), SUCC(ptr));
            STR_ADDR(PRED_ADDR(SUCC(ptr)), PRED(ptr));
        } else {
            STR_ADDR(SUCC_ADDR(PRED(ptr)), NULL);
            seg_list[seg_list_i] = PRED(ptr);
        }
    } else {
        if (SUCC(ptr)) {
            STR_ADDR(PRED_ADDR(SUCC(ptr)), NULL);
        } else {
            seg_list[seg_list_i] = NULL;
        }
    }
}

/*
 * coalesce - Combine consecutive free blocks.
 */
static void * coalesce(void *bp)
{
    /* Get current block size */
    size_t size = GET_SIZE(HDRP(bp));

    /* Check the previous and next block */
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));

    /* Deal with four cases:
        - Case1: Both allocated;
        - Case2: Prev allocated only;
        - Case3: Next allocated only;
        - Case4: Neither allocated;
     */
    if (prev_alloc && next_alloc) {     /* Case1 */
        return bp;
    }
    if (prev_alloc && !next_alloc) {    /* Case2 */ 
        delete(bp);
        delete(NEXT_BLKP(bp));

        size += GET_SIZE(HDRP(NEXT_BLKP(bp))); 

        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    if (!prev_alloc && next_alloc) {    /* Case3 */
        delete(bp);
        delete(PREV_BLKP(bp));

        size += GET_SIZE(HDRP(PREV_BLKP(bp)));

        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));

        bp = PREV_BLKP(bp);
    }
    if (!prev_alloc && !next_alloc) {   /* Case4 */
        delete(bp);
        delete(PREV_BLKP(bp));
        delete(NEXT_BLKP(bp));
    
        size += (GET_SIZE(HDRP(PREV_BLKP(bp))) + \
            GET_SIZE(FTRP(NEXT_BLKP(bp))));

        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));

        bp = PREV_BLKP(bp); 
    }

    insert(bp, size);
    return bp;
}

/*
 * place - Place the requested block. To be more specific,
 * split the block, update the allocation information, and update the free list. 
 */
static void *place(void *bp, size_t adjusted_size)
{
    size_t csize = GET_SIZE(HDRP(bp));
    size_t remainder = csize - adjusted_size;   
    delete(bp);

    if (remainder > (2 * DSIZE)) {
        if (adjusted_size >= SEG_THRESHOLD) { 
            PUT(HDRP(bp), PACK(remainder, 0));
            PUT(FTRP(bp), PACK(remainder, 0));
            PUT(HDRP(NEXT_BLKP(bp)), PACK(adjusted_size, 1));
            PUT(FTRP(NEXT_BLKP(bp)), PACK(adjusted_size, 1));
            
            insert(bp, remainder);
            bp = NEXT_BLKP(bp);
        }
        else {      
            PUT(HDRP(bp), PACK(adjusted_size, 1));
            PUT(FTRP(bp), PACK(adjusted_size, 1));
            bp = NEXT_BLKP(bp);
            PUT(HDRP(bp), PACK(remainder, 0));
            PUT(FTRP(bp), PACK(remainder, 0));
            
            insert(bp, remainder);
            bp = PREV_BLKP(bp);     
        }
    }
    else {
        /* remainder <= minimum size */
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
    return bp;   
}