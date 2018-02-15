
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
    "Group ",
    /* First member's full name */
    "Eric Brown",
    /* First member's email address */
    "ericbrown1.2018@u.northwestern.edu",
    /* Second member's full name (leave blank if none) */
    "Tyler Rodgers",
    /* Second member's email address (leave blank if none) */
    "TylerRodgers2020@u.northwestern.edu"
};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)


#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

///////////////// Additional constants and macros for use ////////////////////////


///////////////// Macros from book, page 830 /////////////////////////////////////

#define WordSize    4       //Number of bytes in word
#define DoubleSize  8       //Number of bytes in double word size
#define ChunkSize (1<<12)   //Size of the chunks for the heap
#define ReallocBuffer (1<<7)
#define ListMax     20
#define Max(x,y) ((x) > (y) ? (x) : (y))
#define Min(x,y) ((x) < (y) ? (x) : (y))  // our equivalent macro to max

#define Pack(size,alloc) ((size) | (alloc)) //allocated bit into word

// Write & Read word at p
#define Get(p) (*(unsigned int *)(p))
#define Put(p,val) (*(unsigned int *)(p) = (val) | GetTag(p)) // added get tag to book definition

#define putNotag(p,val) (*(unsigned int *)(p) = (val))  // our macro based off get and put

// Store pointers for free blocks
#define SetPointer(p,ptr) (*(unsigned int*)(p) = (unsigned int)(ptr))

//find header and footer given block
#define HeadP(bp) ((char *)(bp) - WordSize)
#define FootP(bp) ((char *)(bp) + GetSize(HeadP(bp)) - DoubleSize)

// get size and allocation from p
#define GetSize(p) (Get(p) & ~0x7)
#define GetAlloc(p) (Get(p) & 0x1)

// get address of next and previous blocks from current block
#define NextBlock(bp) ((char *)(bp) + GetSize(((char *)(bp) - WordSize)))
#define PrevBlock(bp) ((char *)(bp) - GetSize(((char *)(bp) - WordSize)))

////////////////////// End Book Macros //////////////////////

#define GetTag(p) (Get(p) & 0x2)     //grabs tag of block
#define PredPtr(ptr) ((char *)(ptr)) //get pointer for predecessor block
#define SuccPtr(ptr) ((char *)(ptr) + WordSize) //get pointer for successor block

//find address of free block's predecessor and successor on seg list
#define pred(ptr) (*(char **)(ptr))          // retrieve dereferenced pointer to free block predecessor
#define succ(ptr) (*(char **)(SuccPtr(ptr))) // retrieve dereferenced pointer to free block successor

//////////////// End Macros and constants ///////////////////////


// Helper Function Decleration
static void *extendHeap(size_t size);
static void *place(void *ptr, size_t size);
static void *coalesce(void *ptr);
static void deleteNode(void *ptr);
static void insertNode(void *ptr, size_t size);

// Global variables
void *sfl[ListMax]; // list of free segments to be searched and filled


//////////////// Start Helper Functions /////////////////////////

static void *extendHeap(size_t words)
{
////////////// from book page 831 //////////////////////
    char *ptr;
    size_t size;
    
    size = (words %2) ? (words+1) * WordSize: words * WordSize;
    if((long)(ptr = mem_sbrk(size)) == -1)
        return NULL;
    
    putNotag(HeadP(ptr),Pack(size,0));
    putNotag(FootP(ptr),Pack(size,0));
    putNotag(HeadP(NextBlock(ptr)),Pack(0,1));
    
    return coalesce(ptr);
////////////// end book page 831 reference ///////////////
}

static void insertNode(void *ptr, size_t size){
    int list = 0;
    void *search_ptr =ptr;
    void *insert_ptr = NULL;
    
    //Selected seglist
    for(list = 0; (list <ListMax-1) && (size>1); list++){
        size >>=1;
    }
    
    search_ptr = sfl[list];
    while ((search_ptr != NULL) && (size > GetSize(HeadP(search_ptr)))) {
        insert_ptr = search_ptr;
        search_ptr = pred(search_ptr);
    }
    
    if (search_ptr == NULL){
        if (insert_ptr == NULL){
            SetPointer(PredPtr(ptr),NULL);
            SetPointer(SuccPtr(ptr),NULL);
            sfl[list] = ptr;
        } else{
            SetPointer(PredPtr(ptr),NULL);
            SetPointer(SuccPtr(ptr), insert_ptr);
            SetPointer(PredPtr(insert_ptr),ptr);
        }
    }else{
        if(insert_ptr == NULL){
            SetPointer(PredPtr(ptr), search_ptr);
            SetPointer(SuccPtr(search_ptr),ptr);
            SetPointer(SuccPtr(ptr),NULL);
            sfl[list] = ptr;
        }else{
            SetPointer(PredPtr(ptr), search_ptr);
            SetPointer(SuccPtr(search_ptr),ptr);
            SetPointer(SuccPtr(ptr), insert_ptr);
            SetPointer(PredPtr(insert_ptr),ptr);
        }
    }
    
    return;
}


static void deleteNode(void *ptr) {
    int list;
    size_t size = GetSize(HeadP(ptr));
    
    for(list =0; (list < ListMax - 1) && (size >1); list++) {
        size >>=1;
    }
    
    if (pred(ptr) == NULL){
        if (succ(ptr) == NULL){
            sfl[list] = NULL;
        } else {
            SetPointer(PredPtr(succ(ptr)),NULL);
        }
    } else {
        if(succ(ptr) == NULL) {
            SetPointer(SuccPtr(pred(ptr)),NULL);
            sfl[list] = pred(ptr);
        }else{
            SetPointer(SuccPtr(pred(ptr)),succ(ptr));
            SetPointer(PredPtr(succ(ptr)),pred(ptr));
        }
    }
    
    return;
}


static void *coalesce(void *ptr){
////////////////////// Book Page 833 /////////////////////
    
    size_t prev_alloc = GetAlloc(FootP(PrevBlock(ptr)));
    size_t next_alloc = GetAlloc(HeadP(NextBlock(ptr)));
    size_t size = GetSize(HeadP(ptr));
    
    // Create case value for switch based on 4 potential coalescing cases
    if(prev_alloc && next_alloc){
        return ptr;
    }
    else if (prev_alloc && !next_alloc){
        size += GetSize(HeadP(NextBlock(ptr)));
        Put(HeadP(ptr), Pack(size,0));
        Put(FootP(ptr),Pack(size,0));
    }else if(!prev_alloc && next_alloc){
        size += GetSize(HeadP(PrevBlock(ptr)));
        Put(FootP(ptr),Pack(size,0));
        Put(HeadP(PrevBlock(ptr)), Pack(size,0));
        ptr = PrevBlock(ptr);
    }else{
        size += GetSize(HeadP(PrevBlock(ptr))) + GetSize(FootP(NextBlock(ptr)));
        Put(HeadP(PrevBlock(ptr)), Pack(size,0));
        Put(FootP(NextBlock(ptr)), Pack(size,0));
        ptr = PrevBlock(ptr);
    }

    
    return ptr;
    ////////////////// End book /////////////////////////////
}

static void *place(void *ptr, size_t asize){
//////////////// From book page 857 //////////////////////
     size_t csize = GetSize(HeadP(ptr));
    
     if ((csize - asize) >= (2*DoubleSize)) {
     Put(HeadP(ptr), Pack(asize, 1));
     Put(FootP(ptr), Pack(asize, 1));
     ptr = NextBlock(ptr);
     Put(HeadP(ptr), Pack(csize-asize, 0));
     Put(FootP(ptr), Pack(csize-asize, 0));
     }
     else {
     Put(HeadP(ptr), Pack(csize, 1));
     Put(FootP(ptr), Pack(csize, 1));
     }
////////////////// END BOOK  /////////////////////////////////
}

////////////////////// End Helper Functions /////////////////////////


/*
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    ///////// from book code page 831 /////////
    char *heap_start;
    //allocate memorty in the initial heap
    if ((heap_start = mem_sbrk(4*WordSize)) ==(void*)-1)
        return -1;
    //Create alignment padding, start header/footer and end header
    putNotag(heap_start,0);
    putNotag(heap_start + (1*WordSize), Pack(DoubleSize,1));
    putNotag(heap_start + (2*WordSize), Pack(DoubleSize,1));
    putNotag(heap_start + (3*WordSize), Pack(0,1));
    
    if(extendHeap(ChunkSize/WordSize) == NULL)
        return -1;
    return 0;
    //////// end book code reference /////////////
}

/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    ///////////// adapted from book page 834 ////////////
    size_t adjsize;
    size_t extsize;
    void *ptr = NULL;
    
    if (size == 0)
        return NULL;
    if (size <= DoubleSize){
        adjsize = 2*DoubleSize;
    }else{
        adjsize = ALIGN(size + DoubleSize);
    }
    //////////// end adaptation /////////////////////////
    
    // following section similar to book's "static void *find_fit(size_t asize) function //
    size_t searchsize = adjsize;
    // search free block in list
    int list;
    for(list =0; list < ListMax; list++){
        if((list == ListMax -1) || ((searchsize<=1) && (sfl[list] != NULL))){
            ptr = sfl[list];
            while((ptr != NULL) && ((adjsize > GetSize(HeadP(ptr))) || (GetTag(HeadP(ptr)))))
            {
                ptr=pred(ptr);
            }
            if (ptr != NULL)
                break;
        }
        searchsize >>=1;
    }
    
    ///////// Directly from book page 834 ////////////
    if (ptr == NULL) {
        extsize = Max(adjsize, ChunkSize);
        
        if((ptr = extendHeap(extsize))==NULL)
            return NULL;
    }
    
    ptr = place(ptr,adjsize);
    
    return ptr;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{
    ////// book page 833 /////////////////
    size_t size = GetSize(HeadP(ptr));
    Put(HeadP(ptr), Pack(size,0));
    Put(FootP(ptr),Pack(size,0));
    coalesce(ptr);
    ///////end book page 833 /////////////
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *newPtr = ptr;
    size_t newSize = size;
    int remain;
    int extsize;
    int blockBuffer;
    
    if(size ==0)
        return NULL;
    
    if(newSize > DoubleSize){
        newSize= ALIGN(size + DoubleSize);
    }else{
        newSize = 2 * DoubleSize;
    }
    // create overhead requirements
    newSize+=ReallocBuffer;
    // get block buffer
    blockBuffer = GetSize(HeadP(ptr)) - newSize;
    // perform allocation when overhead too small
    if(blockBuffer <0){
        if(GetAlloc(HeadP(NextBlock(ptr))) || GetSize(HeadP(NextBlock(ptr)))){
            newPtr = mm_malloc(newSize - DoubleSize);
            memcpy(newPtr, ptr, Min(size,newSize));
            mm_free(ptr);
        }else{
            remain = GetSize(HeadP(ptr)) + GetSize(HeadP(NextBlock(ptr))) - newSize;
            if(remain <0) {
                extsize = Max(-remain, ChunkSize);
                if(extendHeap(extsize) == NULL)
                    return NULL;
                remain += extsize;
            }
            deleteNode(NextBlock(ptr));
            putNotag(HeadP(ptr), Pack(newSize + remain, 1));
            putNotag(FootP(ptr), Pack(newSize + remain, 1));
        }
        blockBuffer = GetSize(HeadP(newPtr)) - newSize;
    }
    
    if(blockBuffer< 2*ReallocBuffer)
        Get(HeadP(NextBlock(newPtr))) |= 0x2;
    
    return newPtr;
    
}














