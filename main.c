/*
 * 一个简要的方法说明：
 * 1.使用分离空闲表组织空闲块
 * 2.维护了分离空闲表有序以使得first fit即best fit
 * 3.调整了一些参数
 * 4.加入一些小的策略，比如分配块的时候如果有较大剩余就分割块，等等
 * 5.关于realloc：分类讨论，详见函数注释
 * 具体策略及实现请看程序中的注释
 */


#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>


#include "mm.h"
#include "memlib.h"
 
 /* If you want debugging output, use the following macro.  When you hand
 * in, remove the #define DEBUG line.*/
 #define DEBUG
 #ifdef DEBUG
 # define dbg_printf(...) printf(__VA_ARGS__)
 #else
 # define dbg_printf(...)
 #endif

/* do not change the following! */
#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif /* def DRIVER */

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(p) (((size_t)(p) + (ALIGNMENT-1)) & ~0x7)

/*
 * If NEXT_FIT defined use next fit search, else use first-fit search
 */
#define NEXT_FITx
#define DEBUG_MODEx

/* Basic constants and macros */
#define WSIZE       4       /* Word and header/footer size (bytes) */
#define DSIZE       8       /* Double word size (bytes) */
/* 这里改了一下CHUNKSIZE */
#define CHUNKSIZE  (1<<10)  /* Extend heap by this amount (bytes) */

#define MAX(x, y) ((x) > (y)? (x) : (y))
#define MIN(x, y) ((x) < (y)? (x) : (y))

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)  ((size) | (alloc))

/* Global variables */
static char *heap_listp = 0;  /* Pointer to first block */
static char *init_heap_listp = 0;  /* Pointer to first block */
#define null init_heap_listp

/* Read and write a word at address p */
static inline unsigned int GET(void *p)       {return *(unsigned int *)(p);}
static inline void PUT(void *p, unsigned int val)  {*(unsigned int*)p = val;}
static inline unsigned int GET_OFF(void *ptr){return (unsigned int)((char*)ptr-null); }
static inline void* GET_ADDR(unsigned int p){return (char*)(null+p);}
static inline void PUT_OFF(void *p,void *ptr){*(unsigned int*)p = GET_OFF(ptr);}

/* Read the size and allocated fields from address p */
static inline unsigned int GET_SIZE(void *p)  {return GET(p) & ~0x7;}
static inline unsigned int GET_ALLOC(void *p) {return GET(p) & 0x1;}

/* Given block ptr bp, compute address of its header and footer */
static inline void* HDRP(void *ptr)       {return (char *)(ptr) - WSIZE;}
static inline void* FTRP(void *ptr)       {return (char *)(ptr) + GET_SIZE(HDRP(ptr)) - DSIZE;}

/* Given block ptr bp, compute address of next and previous blocks */
static inline void* NEXT_BLKP(void *ptr)  {return (char *)(ptr) + GET_SIZE(((char *)(ptr) - WSIZE));}
static inline void* PREV_BLKP(void *ptr)  {return (char *)(ptr) - GET_SIZE(((char *)(ptr) - DSIZE));}



/* 2^0,2^0~2^1,2^1~2^2,2^2~2^3,...,2^14~ */
#define LISTMAX 16
/* 当前节点前后节点地址 */
static inline void* PRED_PTR(void *ptr) {return GET_ADDR(*(unsigned int*)ptr);}
static inline void* SUCC_PTR(void *ptr) {return GET_ADDR(*(unsigned int*)(ptr+WSIZE));}


/* 分离空闲表 */
/* 这里由于handout里说不能定义全局数组，所以定义了一个结构体 */
struct _sfl{
    void *segregated_free_lists[LISTMAX];
}sfl;

/* 一些重要的功能函数 */
/* 扩展堆 */
static void *extend_heap(size_t size);
/* 合并相邻的Free block */
static void *coalesce(void *ptr);
/* 在prt所指向的free block块中allocate size大小的块，如果剩下的空间大于2*DWSIZE，则将其分离后放入Free list */
static void *place(void *ptr, size_t size);
/* 将ptr所指向的free block插入到分离空闲表中 */
static void insert_node(void *ptr, size_t size);
/* 将ptr所指向的块从分离空闲表中删除 */
static void delete_node(void *ptr);

/*
 * extend_heap - Extend heap with free block and return its block pointer
 */
static void *extend_heap(size_t size)
{
    void *ptr=NULL;
    
    /* 对齐 */
    size = ALIGN(size);
    
    if ((long)(ptr = mem_sbrk(size)) == -1)
        return NULL;
    
    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(ptr), PACK(size, 0));         /* Free block header */
    PUT(FTRP(ptr), PACK(size, 0));         /* Free block footer */
    PUT(HDRP(NEXT_BLKP(ptr)), PACK(0, 1)); /* New epilogue header */
    
    /* 放入分离空闲表中 */
    insert_node(ptr, size);
    
    /* Coalesce if the previous block was free */
    return coalesce(ptr);
}


/*
 * coalesce - Boundary tag coalescing. Return ptr to coalesced block
 */
static void *coalesce(void *ptr)
{
    size_t prev_alloc = GET_ALLOC(HDRP(PREV_BLKP(ptr)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(ptr)));
    size_t size = GET_SIZE(HDRP(ptr));
    
    if (prev_alloc && next_alloc) {            /* Case 1 */
        return ptr;
    }
    
    else if (prev_alloc && !next_alloc) {      /* Case 2 */
        delete_node(ptr);
        delete_node(NEXT_BLKP(ptr));
        size += GET_SIZE(HDRP(NEXT_BLKP(ptr)));
        PUT(HDRP(ptr), PACK(size, 0));
        PUT(FTRP(ptr), PACK(size,0));
    }
    
    else if (!prev_alloc && next_alloc) {      /* Case 3 */
        delete_node(ptr);
        delete_node(PREV_BLKP(ptr));
        size += GET_SIZE(HDRP(PREV_BLKP(ptr)));
        PUT(FTRP(ptr), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(ptr)), PACK(size, 0));
        ptr = PREV_BLKP(ptr);
    }
    
    else {                                     /* Case 4 */
        delete_node(ptr);
        delete_node(PREV_BLKP(ptr));
        delete_node(NEXT_BLKP(ptr));
        size += GET_SIZE(HDRP(PREV_BLKP(ptr))) + GET_SIZE(FTRP(NEXT_BLKP(ptr)));
        PUT(HDRP(PREV_BLKP(ptr)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(ptr)), PACK(size, 0));
        ptr = PREV_BLKP(ptr);
    }
    
    /* 将合并好的块放入分离空闲表 */
    insert_node(ptr, size);
    
    return ptr;
}


/*
 * place - Place block of asize bytes at start of free block bp
 *         and split if remainder would be at least minimum block size
 */
const unsigned int Bound=104;
static void *place(void *ptr, size_t size)
{
    size_t csize = GET_SIZE(HDRP(ptr));
    size_t rest=csize - size;
    
    /* 从分离空闲表去除将使用的块 */
    delete_node(ptr);
    
    /* 剩余足够大，分割块 */
    if (rest >= (2*DSIZE)) {
        /* 尽量让大块连在一起以降低外部碎片产生的可能性 */
        /* 小块往“下”放 */
        if(size<Bound){
            PUT(HDRP(ptr), PACK(size, 1));
            PUT(FTRP(ptr), PACK(size, 1));
            void *nptr=NEXT_BLKP(ptr);
            PUT(HDRP(nptr), PACK(rest, 0));
            PUT(FTRP(nptr), PACK(rest, 0));
            insert_node(nptr, rest);
        }
        /* 大块往“上”放 */
        else{
            PUT(HDRP(ptr), PACK(rest, 0));
            PUT(FTRP(ptr), PACK(rest, 0));
            void *nptr=NEXT_BLKP(ptr);
            PUT(HDRP(nptr), PACK(size, 1));
            PUT(FTRP(nptr), PACK(size, 1));
            insert_node(ptr, rest);
            ptr=nptr;
        }
    }
    /* 否则直接把整个块用掉 */
    else {
        PUT(HDRP(ptr), PACK(csize, 1));
        PUT(FTRP(ptr), PACK(csize, 1));
    }
    
    return ptr;
}


/*
 * insert_node - 向分离空闲表中添加节点
 */

/* 找到符合的大小区间对应的表 */
static void find_list(int _size,int *_listnum){
    while(*_listnum<LISTMAX-1&&_size>1){
        _size>>=1;
        (*_listnum)++;
    }
}
/* 寻找表中合适位置 */
static void find_place(int _listnum,size_t _size,void **_pred_ptr,void **_succ_ptr){
    void *succ_ptr=sfl.segregated_free_lists[_listnum];
    void *pred_ptr=null;
    
    while(succ_ptr!=null&&GET_SIZE(HDRP(succ_ptr))<_size){
        pred_ptr=succ_ptr;
        succ_ptr=SUCC_PTR(succ_ptr);
    }
    *_pred_ptr=pred_ptr;
    *_succ_ptr=succ_ptr;
}

static void insert_node(void *ptr, size_t size){
    /* 找到符合的大小区间对应的表 */
    int listnum=0;
    find_list(size, &listnum);
    
    /* 找到表中合适的位置 */
    void *pred_ptr=null;
    void *succ_ptr=null;
    find_place(listnum, size, &pred_ptr, &succ_ptr);
    
    /* 插入 */
    /* 分情况 */
    /* case1:首次插入 */
    if(succ_ptr==null&&pred_ptr==null){
        PUT(ptr, 0);
        PUT((char*)ptr+WSIZE, 0);
        sfl.segregated_free_lists[listnum] = ptr;
    }
    else if(succ_ptr!=null){
        /* case2:开头插入 */
        if(pred_ptr==null){
            PUT_OFF(succ_ptr, ptr);
            PUT(ptr, 0);
            PUT_OFF((char*)ptr+WSIZE, succ_ptr);
            sfl.segregated_free_lists[listnum] = ptr;
        }
        /* case3:中间插入 */
        else{
            PUT_OFF((char*)pred_ptr+WSIZE, ptr);
            PUT_OFF(ptr, pred_ptr);
            PUT_OFF((char*)ptr+WSIZE, succ_ptr);
            PUT_OFF(succ_ptr, ptr);
        }
    }
    /* case4:尾部插入 */
    else{
        PUT_OFF((char*)pred_ptr+WSIZE, ptr);
        PUT_OFF(ptr, pred_ptr);
        PUT((char*)ptr+WSIZE, 0);
    }
}



/*
 * delete_node - 删除分离空闲表中某节点
 */
static void delete_node(void *ptr){
    /* 找到符合的大小区间对应的表 */
    int listnum=0;
    size_t size=GET_SIZE(HDRP(ptr));
    find_list(size, &listnum);
    /* 删除 */
    /* 分情况 */
    /* case1:仅剩的元素 */
    if(SUCC_PTR(ptr)==null&&PRED_PTR(ptr)==null){
        sfl.segregated_free_lists[listnum] = null;
    }
    else if (SUCC_PTR(ptr)!=null){
        /* case2:开头元素 */
        if(PRED_PTR(ptr)==null){
            PUT(SUCC_PTR(ptr), 0);
            sfl.segregated_free_lists[listnum] = SUCC_PTR(ptr);
        }
        /* case3:中间元素 */
        else{
            PUT_OFF((char*)PRED_PTR(ptr)+WSIZE, SUCC_PTR(ptr));
            PUT_OFF(SUCC_PTR(ptr), PRED_PTR(ptr));
        }
    }
    /* case4:尾部元素 */
    else{
        PUT((char*)PRED_PTR(ptr)+WSIZE, 0);
    }
}


/*
 * Initialize: return -1 on error, 0 on success.
 */
const int INITSIZE=1<<5;
int mm_init(void) {
    
    /* Create the initial empty heap */
    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1)
        return -1;

    PUT(heap_listp, 0);                          /* Alignment padding */
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1)); /* Prologue header */
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1)); /* Prologue footer */
    PUT(heap_listp + (3*WSIZE), PACK(0, 1));     /* Epilogue header */
    
    init_heap_listp=heap_listp;
    heap_listp += (2*WSIZE);
    
    /* 初始化分离空闲表 */
    for(int i=0;i<LISTMAX;i++)
        sfl.segregated_free_lists[i]=null;
    
    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    /* 这里尝试改了改初始化的块大小...好像有点用 */
    if (extend_heap(INITSIZE) == NULL)
        return -1;
    return 0;
}


/*
 * malloc
 */
void *malloc (size_t size) {
    size_t asize;      /* Adjusted block size */
    size_t extendsize; /* Amount to extend heap if no fit */
    
    if (heap_listp == 0){
        mm_init();
    }
    
    /* Ignore spurious requests */
    if (size == 0)
        return NULL;
    /* Adjust block size to include overhead and alignment reqs. */
    if (size <= DSIZE)
        asize = 2*DSIZE;
    else
        asize = ALIGN(size+DSIZE);
    
    /* 寻找合适的表 */
    int listnum=0;
    find_list(asize, &listnum);
    
    /* 寻找合适的位置 */
    void *ptr=null;
    void *useless_ptr=null;
    find_place(listnum, asize, &useless_ptr, &ptr);
    
    /* 最合适的表里没有就往更大的块的表中找找 */
    if(ptr==null){
        while(listnum<LISTMAX-1){
            listnum++;
            ptr=sfl.segregated_free_lists[listnum];
            if(ptr!=null)
                break;
        }
    }
    
    /* 没有合适的就扩展堆 */
    if(ptr==null){
        extendsize = MAX(asize,CHUNKSIZE);
        if ((ptr = extend_heap(extendsize)) == NULL)
            return NULL;
    }
    
    ptr=place(ptr, asize);
    
    return ptr;
}

/*
 * free
 */
void free (void *ptr) {
    if (ptr == 0)
        return;
    
    size_t size = GET_SIZE(HDRP(ptr));
    if (heap_listp == 0){
        mm_init();
    }
    
    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));
    
    /* 插入分离空闲表 */
    insert_node(ptr, size);
    
    coalesce(ptr);
}


/*
 * realloc - you may want to look at mm-naive.c
 */
void *realloc(void *ptr, size_t size) {
    
    /* If oldptr is NULL, then this is just malloc. */
    if(ptr == NULL||ptr==null) {
        return mm_malloc(size);
    }
    
    size_t oldsize=GET_SIZE(HDRP(ptr));
    void *newptr;
    
    /* If size == 0 then this is just free, and we return NULL. */
    if(size == 0) {
        mm_free(ptr);
        return 0;
    }
    
    /* 对齐 */
    if (size <= DSIZE)
    {
        size = 2 * DSIZE;
    }
    else
    {
        size = ALIGN(size + DSIZE);
    }
    
    
    int rest=oldsize-size;
    
    /* 原本的块就够了，那就用原来的块 */
    if(rest>=0){
        /* 剩余足够大，分割块 */
        if (rest >= (2*DSIZE)) {
            PUT(HDRP(ptr), PACK(size, 1));
            PUT(FTRP(ptr), PACK(size, 1));
            void *nptr=NEXT_BLKP(ptr);
            PUT(HDRP(nptr), PACK(rest, 0));
            PUT(FTRP(nptr), PACK(rest, 0));
            insert_node(nptr, rest);
        }
        return ptr;
    }
    
    /* 原本的块不够 */
    /* 加上地址连续后面的块够大，那就把两块连起来 */
    else if(!GET_ALLOC(HDRP(NEXT_BLKP(ptr)))&&rest+(int)GET_SIZE(HDRP(NEXT_BLKP(ptr)))>=0){
        size=oldsize+GET_SIZE(HDRP(NEXT_BLKP(ptr)));
        delete_node(NEXT_BLKP(ptr));
        PUT(HDRP(ptr), PACK(size, 1));
        PUT(FTRP(ptr), PACK(size, 1));
        return ptr;
    }
    /* 当前块在堆顶，直接扩展堆 */
    else if(!GET_SIZE(HDRP(NEXT_BLKP(ptr)))){
        if (extend_heap(MAX(-rest, CHUNKSIZE)) == NULL)
            return NULL;
        if(-rest>=CHUNKSIZE){
            delete_node(NEXT_BLKP(ptr));
            PUT(HDRP(ptr), PACK(size, 1));
            PUT(FTRP(ptr), PACK(size, 1));
        }
        /* 扩展较需要更多，把多余部分加入分离空闲表 */
        else{
            rest=oldsize+GET_SIZE(HDRP(NEXT_BLKP(ptr)))-size;
            delete_node(NEXT_BLKP(ptr));
            PUT(HDRP(ptr), PACK(size, 1));
            PUT(FTRP(ptr), PACK(size, 1));
            PUT(HDRP(NEXT_BLKP(ptr)), PACK(rest, 1));
            PUT(FTRP(NEXT_BLKP(ptr)), PACK(rest, 1));
            insert_node(NEXT_BLKP(ptr), rest);
        }
        return ptr;
    }
    /* 其他情况，扩展堆复制过去 */
    else{
        newptr = mm_malloc(size);
        memcpy(newptr, ptr, oldsize);
        mm_free(ptr);
        return newptr;
    }
}

/*
 * calloc - you may want to look at mm-naive.c
 * This function is not tested by mdriver, but it is
 * needed to run the traces.
 */
void *calloc (size_t num, size_t size) {
    void *ptr=NULL;
    if((ptr=malloc(num*size))==NULL)
        return NULL;
    else{
        memset(ptr, 0, num*size-DSIZE);
        void *tmp_ptr=ptr;
        for(unsigned int i=0;i<num;i++){
            PUT((char*)tmp_ptr-WSIZE, PACK(size, 1));
            PUT((char*)tmp_ptr+size-DSIZE, PACK(size, 1));
            tmp_ptr=(char*)tmp_ptr+size;
        }
        return ptr;
    }
}


/*
 * Return whether the pointer is in the heap.
 * May be useful for debugging.
 */
static int in_heap(const void *p) {
    return p <= mem_heap_hi() && p >= mem_heap_lo();
}

/*
 * Return whether the pointer is aligned.
 * May be useful for debugging.
 */
static int aligned(const void *p) {
    return (size_t)ALIGN(p) == (size_t)p;
}

/*
 * mm_checkheap
 */
void mm_checkheap(int lineno)
{
    lineno=lineno; // keep gcc happy
    void *tmp_ptr=heap_listp;
    while(GET_SIZE(HDRP(tmp_ptr))!=0)
    {
        if(GET_ALLOC(HDRP(tmp_ptr))!=GET_ALLOC(FTRP(tmp_ptr))
           ||GET_SIZE(HDRP(tmp_ptr))!=GET_SIZE(FTRP(tmp_ptr)))
        {
            fprintf(stderr,"Idiot! Heap error!\n");
            return;
        }
        tmp_ptr=FTRP(tmp_ptr)+DSIZE;
    }
}

