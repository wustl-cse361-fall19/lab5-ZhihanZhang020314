/*
 * memlib.c - a module that simulates the memory system.  Needed
 * because it allows us to interleave calls from the student's malloc
 * package with the system's malloc package in libc.
 *
 * This version has been updated to enable sparse emulation of very large heaps
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <sys/mman.h>
#include <string.h>
#include <errno.h>
#include <fcntl.h>
#include <unistd.h>
#include <stdint.h>

#include "memlib.h"
#include "config.h"

/* private global variables */
static unsigned char *heap;                 /* Starting address of heap */
static unsigned char *mem_brk;              /* Current position of break */
static unsigned char *mem_max_addr;         /* Maximum allowable heap address */
static size_t mmap_length = MAX_DENSE_HEAP; /* Number of bytes allocated by mmap */
static bool show_stats = false;             /* Should program print allocation information? */
static bool stats_printed = false;          /* Has information been printed about allocation */

static void print_stats();

/* 
 * mem_init - initialize the memory system model
 */
void mem_init(){
    /* Dense allocation */
    mmap_length = MAX_DENSE_HEAP;

    int dev_zero = open("/dev/zero", O_RDWR);
    void *start = TRY_DENSE_HEAP_START;
    void *addr = mmap(start,        /* suggested start*/
                      mmap_length,  /* length */
                      PROT_WRITE,   /* permissions */
                      MAP_PRIVATE,  /* private or shared? */
                      dev_zero,            /* fd */
                      0);            /* offset */
    if (addr == MAP_FAILED) {
        fprintf(stderr, "FAILURE.  mmap couldn't allocate space for heap\n");
        exit(1);
    }
    
    heap = addr;
    mem_max_addr = heap + MAX_DENSE_HEAP;
    
    stats_printed = false;
    mem_brk = heap;
    mem_reset_brk();
}

/* 
 * mem_deinit - free the storage used by the memory system model
 */
void mem_deinit(void){
    print_stats();
    munmap(heap, mmap_length);
}

/*
 * mem_reset_brk - reset the simulated brk pointer to make an empty heap
 */
void mem_reset_brk(){
    print_stats();
    mem_brk = heap;
}

/* 
 * mem_sbrk - simple model of the sbrk function. Extends the heap 
 *                by incr bytes and returns the start address of the new area. In
 *                this model, the heap cannot be shrunk.
 */
void *mem_sbrk(intptr_t incr) {
    unsigned char *old_brk = mem_brk;

    bool ok = true;
    if (incr < 0) {
        ok = false;
        fprintf(stderr, "ERROR: mem_sbrk failed.  Attempt to expand heap by negative value %ld\n", (long) incr);
    } else if (mem_brk + incr > mem_max_addr) {
        ok = false;
        size_t alloc = mem_brk - heap + incr;
        fprintf(stderr, "ERROR: mem_sbrk failed. Ran out of memory.  Would require heap size of %zd (0x%zx) bytes\n", alloc, alloc);
    } else if (sbrk(incr) == (void*) -1) {
        ok = false;
        fprintf(stderr, "ERROR: mem_sbrk failed.  Could not allocate more heap space\n");
    }
    if (ok) {
        mem_brk += incr;
        return (void *) old_brk;
    } else {
        errno = ENOMEM;
        return (void *) -1;
    }
}

/*
 * mem_heap_lo - return address of the first heap byte
 */
void *mem_heap_lo(){
    return (void *) heap;
}

/* 
 * mem_heap_hi - return address of last heap byte
 */
void *mem_heap_hi(){
    return (void *)(mem_brk - 1);
}

/*
 * mem_heapsize() - returns the heap size in bytes
 */
size_t mem_heapsize() {
    return (size_t)(mem_brk - heap);
}

/*
 * mem_pagesize() - returns the page size of the system
 */
size_t mem_pagesize(){
    return (size_t) sysconf(_SC_PAGESIZE);
}


/*************** Private Functions *******************/


static void print_stats() {
    size_t vbytes = mem_heapsize();
    if (!show_stats || vbytes == 0 || stats_printed)
        return;
    printf("Allocated %zu heap bytes.  Max address = %p\n",
           vbytes, mem_brk);
    stats_printed = true;
}

uint64_t mem_read(const void *addr, size_t len) {
    uint64_t rdata;

    rdata = *(uint64_t *) addr;
    if (len < sizeof(uint64_t)) {
        uint64_t mask = ((uint64_t) 1 << (8 * len)) - 1;
        rdata &= mask;
    }
    return rdata;
}

/* Write lower order len bytes of val to address */
void mem_write(void *addr, uint64_t val, size_t len) {
   if (len == sizeof(uint64_t))
        *(uint64_t *) addr = val;
    else
        memcpy(addr, (void *) &val, len);
}
