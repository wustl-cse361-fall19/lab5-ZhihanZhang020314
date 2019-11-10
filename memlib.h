#include <unistd.h>
#include <stdint.h>
#include <stdbool.h>

void mem_init();               
void mem_deinit(void);
void *mem_sbrk(intptr_t incr);
void mem_reset_brk(void); 
void *mem_heap_lo(void);
void *mem_heap_hi(void);
size_t mem_heapsize(void);
size_t mem_pagesize(void);

/* Read len bytes and return value zero-extended to 64 bits */
/* Require 0 <= len <= 8 */
uint64_t mem_read(const void *addr, size_t len);

/* Write lower order len bytes of val to address */
/* Require 0 <= len <= 8 */
void mem_write(void *addr, uint64_t val, size_t len);
