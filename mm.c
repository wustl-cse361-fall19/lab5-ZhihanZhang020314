/*
 ******************************************************************************
 *                                 mm.c                                       *
 *           64-bit struct-based implicit free list memory allocator          *
 *                      without coalesce functionality                        *
 *                 CSE 361: Introduction to Computer Systems                  *
 *                                                                            *
 *  ************************************************************************  *
 *                            Zhihan Zhang                                    *
 *                            WUSTL ID: 478594                                *
 *  ************************************************************************  */

/* Do not change the following! */

#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <stdbool.h>
#include <stddef.h>
#include <assert.h>
#include <stddef.h>

#include "mm.h"
#include "memlib.h"

#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif /* def DRIVER */

/* You can change anything from here onward */

/*
 * If DEBUG is defined, enable printing on dbg_printf and contracts.
 * Debugging macros, with names beginning "dbg_" are allowed.
 * You may not define any other macros having arguments.
 */
#define DEBUG // uncomment this line to enable debugging

#ifdef DEBUG
/* When debugging is enabled, these form aliases to useful functions */
#define dbg_printf(...) printf(__VA_ARGS__)
#define dbg_requires(...) assert(__VA_ARGS__)
#define dbg_assert(...) assert(__VA_ARGS__)
#define dbg_ensures(...) assert(__VA_ARGS__)
#else
/* When debugging is disnabled, no code gets generated for these */
#define dbg_printf(...)
#define dbg_requires(...)
#define dbg_assert(...)
#define dbg_ensures(...)
#endif

#define LISTSIZE 12
#define THRESHFIT 20
#define NEXTBLOCK block->payload.links.next
#define PREVBLOCK block->payload.links.prev
#define ABIT 0x2
#define SBIT 0x4
//#define checkheap(...) mm_checkheap(__VA_ARGS__)
//#define checkheap(...)  

/* Basic constants */
typedef uint64_t word_t;
static const size_t wsize = sizeof(word_t);   // word and header size (bytes)
static const size_t dsize = 2*sizeof(word_t);       // double word size (bytes)
static const size_t min_block_size = 4*sizeof(word_t); // Minimum block size
static const size_t chunksize = (1 << 12);    // requires (chunksize % 16 == 0)

static const word_t alloc_mask = 0x1;
static const word_t size_mask = ~(word_t)0xF;

typedef struct block block_t;
/* Block Structure:
 * Header contains:
 * 1. Size 
 * 2. Allocation flag
 * 3. Check previous allocation flag
 * 4. Check previous small block flag
 *
 * Payload contains:
 * a. If allocated: only data
 * b. If unallocated and size > 16 bytes:
 *    1. Pointer to next block in segregated free list
 *    2. Pointer to previous block in segregated free list 
 * c. If unallocated and size <= 16 bytes:
 *    1. Pointer to next block in small free list
 */
 
struct block
{
    /* Header contains size + allocation flag */
    word_t header;
    /*
     * We don't know how big the payload will be.  Declaring it as an
     * array of size 0 allows computing its starting address using
     * pointer notation.
     */
    union 
    {
        struct
        {
            block_t *next;
            block_t *prev;
        }links;
        char data[0];
    /*
     * We can't declare the footer as part of the struct, since its starting
     * position is unknown
     */
    }payload;

};


/* Global variables */
/* Pointer to first block */

// Total size = 8 + 12*8 + 8 = 112 bytes

static block_t *heap_start = NULL;
/* Array of pointers for segregated list */
static block_t *listHeader[LISTSIZE];
/* Header for List of small blocks */
static block_t *smallListHeader = NULL;

bool mm_checkheap(int lineno);

/* Function prototypes for internal helper routines */
static block_t *extend_heap(size_t size);
static void place(block_t *block, size_t asize);
static block_t *find_fit(size_t asize);
static block_t *coalesce(block_t *block);

static size_t max(size_t x, size_t y);
static size_t round_up(size_t size, size_t n);
static word_t pack(size_t size, bool alloc);

static size_t extract_size(word_t header);
static size_t get_size(block_t *block);
static size_t get_payload_size(block_t *block);

static bool extract_alloc(word_t header);
static bool get_alloc(block_t *block);

static void write_header(block_t *block, size_t size, bool alloc);
static void write_footer(block_t *block, size_t size, bool alloc);

static block_t *payload_to_header(void *bp);
static void *header_to_payload(block_t *block);

static block_t *find_next(block_t *block);
static word_t *find_prev_footer(block_t *block);
static block_t *find_prev(block_t *block);

//Extra functions defined by Zhihan
static int getList(size_t size);
static void listInsert(block_t *block, size_t size);
static void listDelete(block_t *block);
static void printSList();
static bool checkAlloc(block_t *block);

/* printSList: Prints the SMALL BLOCKS LIST, used only in debugging and mm_checkheap()
 */
static void printSList() //print small list
{
    block_t * ptr = smallListHeader;
   
    while (ptr != NULL)
    {
   
        ptr = ptr -> payload.links.next;
    }
}

/* getList: For a particular size argument, it returns the class which belongs to in the segregated list.
 * If size<=16, returns -1, indicating it does not belong in the segregated list.
 */

static int getList(size_t size)
{
    if ((size>16) && (size<=32))
        return 0;
    if ((size>32) && (size<=64))
        return 1;
    if ((size>64) && (size<=128))
        return 2;
    if ((size>128) && (size<=256))
        return 3;
    if ((size>256) && (size<=512))
        return 4;
    if ((size>512) && (size<=1024))
        return 5;
    if ((size>1024) && (size<=2048))
        return 6;
    if ((size>2048) && (size<=4098))
        return 7;
    if ((size>4098) && (size<=8192))
        return 8;
    if ((size>8192) && (size<=16384))
        return 9;
    if ((size>16384) && (size<=32768))
        return 10;
    if (size>32768)
        return 11;

    // Return -1 if small block is encountered
    return -1;

}

/* listInsert: For a particular block and its size taken as arguments, this function inserts the block into either the seg list or the small blocks list. 
If the size <= 16 bytes, it inserts the block into the small blocks list. 
Otherwise, it inserts the block into the seg list.
 */
static inline void listInsert(block_t *block, size_t size)
{

    // Insert into segregated list for big sizes
    // Insert into the beginning of the list
    if (size > dsize)
    {   
        PREVBLOCK = NULL;
        int sIndex = getList(size);
        NEXTBLOCK = listHeader[sIndex];
        if(listHeader[sIndex] != NULL)
            listHeader[sIndex] -> payload.links.prev = block;
        listHeader[sIndex] = block;
        return;
    }
    // Insert into small blocks list for small blocks
    // Insert into beginning of the list
    else
    {
        //printSList();
        NEXTBLOCK = smallListHeader;
        smallListHeader = block;
        //printSList();
    }    
}

/* listDelete: For a particular block and its size taken as arguments, this function deletes the block from either the seg list or the small blocks list. 
If the size <= 16 bytes, it deletes the block from the small blocks list. 
Otherwise, it deletes the block from the seg list.
 */
static inline void listDelete(block_t *block)
{ 
    size_t size = get_size(block);
    int sIndex = 0;

    block_t *blockPrev;
    block_t *ptr,*prv=NULL;
    block_t *blockNext;
    // Delete from segregated list for big sizes
    if (size > dsize)
    {
        blockNext = NEXTBLOCK;
        blockPrev = PREVBLOCK;
        if(blockPrev != NULL)
            blockPrev -> payload.links.next = blockNext;
        else
        {
            sIndex = getList(size);
            listHeader[sIndex] = blockNext;       
        }
    if (blockNext != NULL)
        blockNext -> payload.links.prev = blockPrev;
    return;
    }

    // Delete from small blocks list for small sizes
    else
    {   //printSList();
        ptr = smallListHeader;
        while (ptr != NULL)
        {
            if (ptr == block)
            {   
                if (ptr == smallListHeader)
                {
                    smallListHeader = ptr -> payload.links.next;
                    printSList(); 
                    return;
                }
                prv->payload.links.next = ptr -> payload.links.next;
                //printSList();
                return;
            }
            prv = ptr;
            ptr = ptr -> payload.links.next;
        }
      
    }   
}
/*
 * <what does mm_init do?>
 * Initializes the heap; it is run once when heap_start == NULL.
 * prior to any extend_heap operation, this is the heap:
 * start            start+8           start+16
 * INIT: | PROLOGUE_FOOTER | END_HEADER |
 * heap_listp ends up pointing to the end header.
 */
bool mm_init(void) 
{
    // Create the initial empty heap 
    word_t *start = (word_t *)(mem_sbrk(2*wsize));

    int i;

    if (start == (void *)-1) 
    {
        return false;
    }

    start[0] = pack(0, true); // Prologue footer
    start[1] = pack(0, true)|0x2; // End header
    
    // Heap starts with first "block header", currently the end footer
    heap_start = (block_t *) & (start[1]);

    for(i=0; i < LISTSIZE; i++)
        listHeader[i] = NULL;  
        smallListHeader = NULL;
    
    // Extend the empty heap with a free block of chunksize bytes
    if (extend_heap(chunksize) == NULL)
    {
        return false;
    }
    return true;
}

/*
 * <what does mmalloc do?>
 * Allocates a block with size at least (size + dsize), rounded up to the nearest 16 bytes, with a minimum of 2*dsize. 
 * Seeks a sufficiently-large unallocated block on the heap to be allocated.
 * If no such block is found, extends heap by the maximum between chunksize and (size + dsize) rounded up to the nearest 16 bytes, and then attempts to allocate all, or a part of, that memory.
 * Returns NULL on failure, otherwise returns a pointer to such block.
 * The allocated block will not be used for further allocations until freed.
 */
void *malloc(size_t size) 
{
    size_t asize;      // Adjusted block size
    size_t extendsize; // Amount to extend heap if no fit is found
    block_t *block;
    void *bp = NULL;

    if (heap_start == NULL) // Initialize heap if it isn't initialized
    {
        mm_init();
    }

    if (size == 0) // Ignore spurious request
    {
        dbg_ensures(mm_checkheap(__LINE__));
        return bp;
    }

   // Smallest Block Size = 16 bytes
   if(size <= 8)
   {
        asize = min_block_size/2;
   }

   // Block Size = 32 bytes
   else if (size <= dsize)
   {        
        asize = min_block_size;
   }

   // Round up and adjust to meet alignment requirements    
   else
        asize = round_up(size+wsize, dsize);

    // Search the free list for a fit
    block = find_fit(asize);

    // If no fit is found, request more memory, and then and place the block
    if (block == NULL)
    {  
        extendsize = max(asize, chunksize);
       
        block = extend_heap(extendsize);
        if (block == NULL) // extend_heap returns an error
        {
            return bp;
        }

    }

    place(block, asize);
    bp = header_to_payload(block);

    dbg_ensures(mm_checkheap(__LINE__));
    return bp;
} 

/*
 * <what does free do?>
 * Frees the block such that it is no longer allocated while still maintaining its size. Block will be available for use on malloc.
 */
void free(void *bp)
{
    block_t *temp;
    int abit, sbit;

    if (bp == NULL)
    {
        return;
    }

    block_t *block = payload_to_header(bp);
    size_t size = get_size(block);

    // Extract ABIT and SBIT
    abit = (block -> header) & ABIT;
    sbit = (block -> header) & SBIT;

    // Carry over ABIT and SBIT information over to the free block
    write_header(block, size+abit+sbit, false);
    write_footer(block, size, false);
    temp = find_next(block);

    // Clear ABIT in the next block to indicate free block
    temp->header = temp -> header & (~ABIT);

    //printSList();
    coalesce(block);
}

/*
 * <what does realloc do?>
 * Returns a pointer to an allocated region of at least size bytes:
 *          if ptrv is NULL, then call malloc(size);
 *          if size == 0, then call free(ptr) and returns NULL;
 *          else allocates new region of memory, copies old data to new memory, and then free old block. Returns old block if realloc fails or returns new pointer on success.
 */
void *realloc(void *ptr, size_t size)
{

    block_t *block = payload_to_header(ptr);
    size_t copysize;
    void *newptr;

    // If size == 0, then free block and return NULL
    if (size == 0)
    {
        free(ptr);
        return NULL;
    }

    // If ptr is NULL, then equivalent to malloc
    if (ptr == NULL)
    {
        return malloc(size);
    }

    // Otherwise, proceed with reallocation
    newptr = malloc(size);
    // If malloc fails, the original block is left untouched
    if (!newptr)
    {
        return NULL;
    }

    // Copy the old data
    copysize = get_payload_size(block); // gets size of old payload
    if(size < copysize)
    {
        copysize = size;
    }
    memcpy(newptr, ptr, copysize);

    // Free the old block
    free(ptr);
    
   // mm_checkheap(__LINE__);
    return newptr;
}

/*
 * <what does calloc do?>
 * Allocates a block with size at least (elements * size + dsize) through malloc, then initializes all bits in allocated memory to 0.
 * Returns NULL on failure.
 */
void *calloc(size_t elements, size_t size)
{
    void *bp;
    size_t asize = elements * size;

    if (asize/elements != size)
    {    
        // Multiplication overflowed
        return NULL;
    }
    
    bp = malloc(asize);
    if (bp == NULL)
    {
        return NULL;
    }
    // Initialize all bits to 0
    memset(bp, 0, asize);

    return bp;
}

/******** The remaining content below are helper and debug routines ********/

/*
 * <what does extend_heap do?>
 * Extends the heap with the requested number of bytes, and recreates end header. 
 * Returns a pointer to the result of coalescing the newly-created block with previous free block, 
 * if applicable, or NULL in failure.
 */
static inline  block_t *extend_heap(size_t size) 
{
    void *bp;

    void *e = mem_heap_hi();
    e = (((char *)e) - 7); 
    long EHeaderBit = (ABIT) & (*((long *)e));
    long EHeaders = (SBIT) & (*((long *)e));

    // Allocate an even number of words to maintain alignment
    size = round_up(size, dsize);
    if ((bp = mem_sbrk(size)) == (void *)-1)
    {
        return NULL;
    }
    
    // Initialize free block header/footer 
    block_t *block = payload_to_header(bp);
    write_header(block, size, false);
    write_footer(block, size, false);

    // Carry over end ABIT and SBIT
    block->header |= (EHeaderBit) | (EHeaders);
    
    // Create new end header
    block_t *block_next = find_next(block);
    block_next -> header = 0;
    write_header(block_next, 0, true);

    // Coalesce in case the previous block was free
    return coalesce(block);
}

/* checkAlloc: Checks the ABIT of current block and returns true if the previous block is allocated, false otherwise.
 */
static bool checkAlloc(block_t *block)
{
    if((block -> header) & ABIT)
        return true;
    return false;
}

/*
 * <what does coalesce do?>
 * Coalesces current block with previous and next blocks if either or both are unallocated; otherwise the block is not modified.
 * Returns pointer to the coalesced block. After coalescing, the immediate contiguous previous and next blocks must be allocated.
 */
static inline block_t *coalesce(block_t * block) 
{

    size_t size = get_size(block);
    block_t *block_next;
    block_t *block_prev, *temp; 
    block_next = find_next(block);

    // Check if previous block is a small block, assign block_prev accordingly
    if(block -> header & SBIT)
    {
        block_prev = (block_t *)(((char *)block) - dsize);
    }
    else
    block_prev = find_prev(block);
    bool prev_alloc = checkAlloc(block);
    bool next_alloc = get_alloc(block_next);

    if (prev_alloc && next_alloc)              // Case 1
    {
       
        listInsert(block,size);
  
        return block;
    }

    else if (prev_alloc && !next_alloc)        // Case 2
    {

        size += get_size(block_next); 
        listDelete(block_next);

        // If next block is small, reset SBIT of the block further next
        if(get_size(block_next) <= dsize)
        {
            temp = find_next(block_next);
            temp->header = temp -> header & (~SBIT);
        }
        block_next -> header = 0;

        // Set the ABIT since the previous block after coalescing has to be allocated
        write_header(block, size+ABIT, false);
        write_footer(block, size+ABIT, false);
        listInsert(block,size);

        return block;
    }

    else if (!prev_alloc && next_alloc)        // Case 3
    {
     
        size += get_size(block_prev);
        listDelete(block_prev);

        // Set the ABIT since the previous block after coalescing
        // has to be allocated.
        write_header(block_prev, size+ABIT, false);
        write_footer(block_prev, size+ABIT, false);

        // If this block is small, reset SBIT of the next block
        if(get_size(block)<=dsize)
        {
            temp = block_next;
            temp->header = temp -> header & (~SBIT);
        }
        block->header = 0;
        block = block_prev;
        listInsert(block,size);
    
        return block;
    }

    else                                       // Case 4
    {
      
        size += get_size(block_next) + get_size(block_prev);
        listDelete(block_prev);
        listDelete(block_next);

        // If next block is small, reset SBIT of the block further next
        if(get_size(block_next) <= dsize)
        {
            temp = find_next(block_next);
            temp->header = temp -> header & (~SBIT);
        }
        block_next->header = 0;

        // Set the ABIT since the previous block after coalescing has to be allocated
        write_header(block_prev, size+ABIT, false);
        write_footer(block_prev, size+ABIT, false);
        block->header = 0;
        block = block_prev;
        listInsert(block,size);

        return block;
    }
    return block;
}

/*
 * <what does place do?>
 * Places block with size of asize at the start of bp.
 * If the remaining size is at least the minimum block size, then split the block to the the allocated block and the remaining block as free, which is then inserted into the segregated list. 
 * Requires that the block is initially unallocated.
 */
static void place(block_t *block, size_t asize)
{
    size_t csize = get_size(block);

    // Extract ABIT and SBIT in current block
    int abit = (block -> header) & (ABIT);
    int sbit = (block -> header) & (SBIT);
   
    block_t *block_next;
    listDelete(block);
    if ((csize - asize) >= min_block_size/2)
    {
        // Carry over SBIT and ABIT to the allocated block
        write_header(block, asize+abit+sbit, true);
        block_next = find_next(block);
        block_next -> header = 0;
        // Set SBIT if a small block is allocated
        if(asize==dsize)
            sbit = SBIT;
        else
            sbit = 0;
        // Set ABIT, set/reset SBIT accordingly in the new free block
        write_header(block_next, csize-asize+ABIT+sbit, false);
        write_footer(block_next, csize-asize, false);
        coalesce(block_next);
    }

    else
    { 
        write_header(block, csize+abit, true);

        // If small block is allocated, set SBIT in next block 
        if(csize == dsize)
        {
            block_next = find_next(block);
            block_next -> header = (block_next -> header) | (SBIT);
        }
    }
   
}

/*
 * <what does find_fit do?>
 * Looks for a free block with at least asize bytes with first-fit policy. Returns NULL if none is found.
 */
static inline block_t *find_fit(size_t asize)
{
    block_t *block, *bestblk = NULL;
    int sIndex = getList(asize), i, t=0;
    size_t bsize = mem_heapsize(), tsize;

    // If size<=16, search in small blocks list
    if( sIndex==-1)
    {
        block = smallListHeader;
        while(block!=NULL)
        {   
            tsize = get_size(block);
            if(asize <= tsize)
            {
                return block;
            }
            block = NEXTBLOCK;
        }
        sIndex = 0;
    }

    // Start searching seg list from the corresponding class for asize,
    // continue over to next class if no block is found in that class.
    for (i=sIndex; i<LISTSIZE; i++)    
    {
        block = listHeader[i];
        while (block!=NULL)
        {   
            tsize = get_size(block);
            if (asize<tsize)
            {   
                // THRESHFIT limits the number of blocks to check
                // before deciding the best fit free block.
                if (t ++== THRESHFIT)
                return bestblk;
                if ((tsize-asize) < (bsize-asize))
                {
                    bsize = tsize;
                    bestblk = block;
                }
            }

            // If sizes match perfectly, return the block immediately
            else if (asize == tsize)
            {
                return block;
            }
            block = NEXTBLOCK;
        }
    }
   return bestblk;
}

/* 
 * <what does your heap checker do?>
 * Please keep modularity in mind when you're writing the heap checker!
 */
bool mm_checkheap(int line)  
{ 
    (void)line; // delete this line; it's a placeholder so that the compiler
                // will not warn you about an unused variable.
    return true;
}

/*
 * max: returns x if x > y, and y otherwise.
 */
static size_t max(size_t x, size_t y)
{
    return (x > y) ? x : y;
}


/*
 * round_up: Rounds size up to next multiple of n
 */
static size_t round_up(size_t size, size_t n)
{
    return (n * ((size + (n-1)) / n));
}

/*
 * pack: returns a header reflecting a specified size and its alloc status.
 *       If the block is allocated, the lowest bit is set to 1, and 0 otherwise.
 */
static word_t pack(size_t size, bool alloc)
{
    return alloc ? (size | 1) : size;
}


/*
 * extract_size: returns the size of a given header value based on the header
 *               specification above.
 */
static size_t extract_size(word_t word)
{
    return (word & size_mask);
}

/*
 * get_size: returns the size of a given block by clearing the lowest 4 bits
 *           (as the heap is 16-byte aligned).
 */
static size_t get_size(block_t *block)
{
    return extract_size(block->header);
}

/*
 * get_payload_size: returns the payload size of a given block, equal to
 *                   the entire block size minus the header and footer sizes.
 */
static word_t get_payload_size(block_t *block)
{
    size_t asize = get_size(block);
    return asize - wsize;
}

/*
 * extract_alloc: returns the allocation status of a given header value based
 *                on the header specification above.
 */
static bool extract_alloc(word_t word)
{
    return (bool)(word & alloc_mask);
}

/*
 * get_alloc: returns true when the block is allocated based on the
 *            block header's lowest bit, and false otherwise.
 */
static bool get_alloc(block_t *block)
{
    return extract_alloc(block->header);
}

/*
 * find_next: returns the next consecutive block on the heap by adding the
 *            size of the block.
 */
static block_t *find_next(block_t *block)
{
    block_t *block_next = (block_t *)(((char *)block) + get_size(block));
    
    return block_next;
}

/*
 * find_prev_footer: returns the footer of the previous block.
 */
static word_t *find_prev_footer(block_t *block)
{
    // Compute previous footer position as one word before the header
    return (&(block->header)) - 1;
}

/*
 * find_prev: returns the previous block position by checking the previous
 *            block's footer and calculating the start of the previous block
 *            based on its size.
 */
static block_t *find_prev(block_t *block)
{
    word_t *footerp = find_prev_footer(block);
    size_t size = extract_size(*footerp);
    return (block_t *)((char *)block - size);
}

/*
 * payload_to_header: given a payload pointer, returns a pointer to the
 *                    corresponding block.
 */
static block_t *payload_to_header(void *bp)
{
    return (block_t *)(((char *)bp) - offsetof(block_t, payload));
}

/*
 * header_to_payload: given a block pointer, returns a pointer to the
 *                    corresponding payload.
 */
static void *header_to_payload(block_t *block)
{
    return (void *)(block->payload.data);
}

/*
 * write_header: given a block and its size and allocation status,
 *               writes an appropriate value to the block header. 
 *               It also sets the SBIT and ABIT in the next block 
 *               accordingly.
 */
static void write_header(block_t *block, size_t size, bool alloc)
{
    block_t *temp;
    // If small block encountered, set SBIT of next block
    if((size & size_mask) == dsize)
    {
        temp = (block_t *)(((char*)block) + dsize);
        temp -> header = temp -> header | SBIT;
    }
    // Carry over the SBIT and pack
    block->header = pack(size|(block->header&SBIT), alloc);
    // If allocated block encountered, set ABIT of next block
    if(alloc == true)
    {
        temp = find_next(block);   
        // If prologue or end, return without doing anything
        if(temp == block)
            return;
        temp -> header = temp -> header | ABIT;
    }
}


/*
 * write_footer: given a block and its size and allocation status,
 *               writes an appropriate value to the block footer by first
 *               computing the position of the footer.
 */
static void write_footer(block_t *block, size_t size, bool alloc)
{
   
    word_t *footerp;
    // If small block encountered, return without doing anything
    if(size <= dsize)
        return;
    footerp = (word_t *)((block -> payload.data) + get_size(block) - dsize);
    *footerp = pack(size, alloc);
}
