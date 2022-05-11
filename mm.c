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
    "jungle",
    /* First member's full name */
    "Haein Kim",
    /* First member's email address */
    "kimhi1640@gmail.com",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};



/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)

/* 메모리 할당 시 기본적으로 header와 footer를 위해 필요한 더블워드만큼의 메모리 크기 */
#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/*
    기본 상수와 매크로
*/

/* 기본 단위인 word, double word, 새로 할당받는 힙의 크기 CHUNKSIZE를 정의한다 */
#define WSIZE       4       /* Word and header/footer size (bytes) */
#define DSIZE       8       /* Double word size (bytes) */
#define MINIMUM     16      /* Initial Prologue block size, header, footer, PREC, SUCC */
#define CHUNKSIZE   (1<<12) // 초기 가용 블록과 힙 확장을 위한 기본 크기

#define MAX(x, y) ((x) > (y) ? (x) : (y))               // 최댓값 구하는 함수 매크로

/* 헤더와 푸터에 저장할 수 있는 값(전체 사이즈와 할당 여부 인코딩 된 값) 리턴 */
#define PACK(size, alloc)   ((size) | (alloc))   

/* 인자 p가 참조하는 워드 값 리턴 혹은 저장*/
#define GET(p)          (*(unsigned int*)(p))           // 주소값 p에 있는 값 리턴
#define PUT(p, val)     (*(unsigned int*)(p) = (val))   // 주소값 p에 val 저장 

/* 헤더 또는 푸터를 가리키는 포인터를 인자로 전체 블럭 size, 할당 여부 비트 리턴 */
#define GET_SIZE(p)     (GET(p) & ~0x7)                 // 전체 블럭 크기 리턴 (헤더 + 데이터 + 푸터)
#define GET_ALLOC(p)    (GET(p) & 0x1)                  // 할당 여부 리턴 (할당 시 1, 가용 시 0)    

/* 블록 포인터 bp를 인자로 받아 블록의 header와 footer의 주소를 반환한다 */
#define HDRP(bp)    ((char*)(bp) - WSIZE) 
#define FTRP(bp)    ((char*)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* 블록 포인터 bp를 인자로 받아 이후, 이전 블록의 주소를 리턴한다 */
#define NEXT_BLKP(bp)   ((char*)(bp) + GET_SIZE(((char*)(bp) - WSIZE))) // (char*)(bp) + GET_SIZE(지금 블록의 헤더값)
#define PREV_BLKP(bp)   ((char*)(bp) - GET_SIZE(((char*)(bp) - DSIZE))) // (char*)(bp) - GET_SIZE(이전 블록의 풋터값)

/* Free List 상에서의 이전, 이후 블록의 포인터를 리턴한다. */
#define PREV_FREEP(bp)  (*(void**)(bp))             // 이전 블록의 bp
#define SUCC_FREEP(bp)  (*(void**)(bp + WSIZE))     // 이후 블록의 bp


/* define searching method for find suitable free blocks to allocate*/
// #define NEXT_FIT  // define하면 next_fit, 안 하면 first_fit으로 탐색

/* global variable & functions */
static char* heap_listp = NULL; // 항상 프롤로그 블럭을 가리키는 정적 전역 변수
static char* free_listp = NULL; // free list의 맨 첫 블록을 가리키는 포인터

/* 함수 프로토타입 선언 */
static void* extend_heap(size_t words);
static void* coalesce(void* bp);
static void* find_fit(size_t asize);
static void place(void* bp, size_t newsize);

int mm_init(void);
void *mm_malloc(size_t size);
void mm_free(void *bp);
void *mm_realloc(void *ptr, size_t size);


/* 
 * mm_init - initialize the malloc package.
 * 최초 가용 블럭으로 힙을 생성하기
 */
int mm_init(void)
{
    /* 6words 크기의 빈 가용 리스트 초기화 */
    /* padding, prol_header, prol_footer, PREC, SUCC, epil_header */
    if ((heap_listp = mem_sbrk(6*WSIZE)) == (void*)-1){ // 추가적인 힙 메모리 할당 에러 발생 시 -1 반환
        return -1;
    }

    PUT(heap_listp, 0);                             // 미사용 패딩 워드
    PUT(heap_listp + (1*WSIZE), PACK(MINIMUM, 1));  // 프롤로그 헤더
    PUT(heap_listp + (2*WSIZE), NULL);              // PREC 포인터 NULL로 초기화 -> freelist에서 이전 블럭의 bp 메모리 주소를 가짐
    PUT(heap_listp + (3*WSIZE), NULL);              // SUCC 포인터 NULL로 초기화 -> freelist에서 다음 블럭의 bp 메모리 주소를 가짐
    PUT(heap_listp + (4*WSIZE), PACK(MINIMUM, 1));  // 프롤로그 푸터
    PUT(heap_listp + (5*WSIZE), PACK(0, 1));        // 에필로그 헤더

    free_listp = heap_listp + 2*WSIZE; // free_listp 포인터는 탐색의 시작점
                                       // static char* free_listp = &(변수) <= 즉 free_listp 포인터는 변수의 주소값을 value로 가짐
                                       // heap_listp + 2WSIZE가 주소값임
                                       // 나중에 free_listp라는 변수만 쓰고 활용한다면, 변수에 저장되어 있는 주소값을 가지고 옴
                                       // 예시: putFreeBlock(void *bp) 함수의 SUCC_FREEP(bp) = free_listp; 


    /* CHUNKSIZE 바이트의 가용한 블럭만큼 비어있는 힙을 늘려줌 */
    if (extend_heap(CHUNKSIZE / WSIZE) == NULL){
        return -1;
    }

    return 0;
}


/* 새 가용 블럭으로 힙 확장 */
static void* extend_heap(size_t words)
{
    char* bp;
    size_t size;

    /* 정렬 유지 위해 8의 배수로 반올림하여 추가적인 힙 공간 요청 */
    size = (words % 2) ? (words + 1) * WSIZE : (words) * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1) {
        // 더블 워드 정렬에 따라 메모리를 mem_sbrk 함수를 이용해 할당받음
        // 새 메모리의 첫 부분을 bp로 둔다. 주소값은 int로는 못 받아서 long으로 casting한 듯.
        return NULL;
    }
    /* 새 가용 블록의 header와 footer를 정해주고 epilogue block을 가용 블록 맨 끝으로 옮긴다. */
    PUT(HDRP(bp), PACK(size, 0));  // 헤더. 할당 안 해줬으므로 0으로.
    PUT(FTRP(bp), PACK(size, 0));  // 풋터.
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));  // 새 에필로그 헤더

    /* 만약 이전 블록이 가용 블록이라면 연결시킨다. */
    return coalesce(bp);
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    size_t asize;       // Adjusted block size
    size_t extendsize;  // Amount for extend heap if there is no fit
    char* bp;

    // 가짜 요청 spurious request 무시
    if (size == 0)
        return NULL;

    // 요청 사이즈에 header와 footer를 위한 dword 공간(SIZE_T_SIZE)을 추가한 후 align해준다.
    asize = ALIGN(size + SIZE_T_SIZE);  

    // 할당할 가용 리스트를 찾아 필요하다면 분할해서 할당한다!
    if ((bp = find_fit(asize)) != NULL){  // first fit으로 추적한다.
        place(bp, asize);  // 필요하다면 분할하여 할당한다.
        return bp;
    }

    // 만약 맞는 크기의 가용 블록이 없다면 새로 힙을 늘려서 새 힙에 메모리를 할당한다.
    extendsize = MAX(asize, CHUNKSIZE);  // 둘 중 더 큰 값으로 사이즈를 정한다.
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL) 
        return NULL;
    place(bp, asize);
    return bp;
}


/*
    coalesce(bp) : 해당 가용 블록을 앞뒤 가용 블록과 연결하고 연결된 가용 블록의 주소를 리턴한다.
*/
static void* coalesce(void* bp){
    // 직전 블록의 footer, 직후 블록의 header를 보고 가용 여부를 확인.
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));  // 직전 블록 가용 여부
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));  // 직후 블록 가용 여부
    size_t size = GET_SIZE(HDRP(bp));

    // case 1 : 직전, 직후 블록이 모두 할당 -> 해당 블록만 free list에 넣어주면 된다.

    // case 2 : 직전 블록 할당, 직후 블록 가용
    if(prev_alloc && !next_alloc){
        removeBlock(NEXT_BLKP(bp));    // free 상태였던 직후 블록을 free list에서 제거한다.
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }

    // case 3 : 직전 블록 가용, 직후 블록 할당
    else if(!prev_alloc && next_alloc){
        removeBlock(PREV_BLKP(bp));    // 직전 블록을 free list에서 제거한다.
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        bp = PREV_BLKP(bp); 
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));  
    }

    // case 4 : 직전, 직후 블록 모두 가용
    else if (!prev_alloc && !next_alloc) {
        removeBlock(PREV_BLKP(bp));
        removeBlock(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        bp = PREV_BLKP(bp);
        PUT(HDRP(bp), PACK(size, 0));  
        PUT(FTRP(bp), PACK(size, 0));  
    }

    // 연결된 새 가용 블록을 free list에 추가한다.
    putFreeBlock(bp);

    return bp;
}


/*
    first_fit : 힙의 맨 처음부터 탐색하여 요구하는 메모리 공간보다 큰 가용 블록의 주소를 반환한다.
*/
static void* find_fit(size_t asize){
    /* First-fit */
    void* bp;

    // free list의 맨 뒤는 프롤로그 블록이다. Free list에서 유일하게 할당된 블록이므로 얘를 만나면 탐색 종료.
    for (bp = free_listp; GET_ALLOC(HDRP(bp)) != 1; bp = SUCC_FREEP(bp)){
        if(asize <= GET_SIZE(HDRP(bp))){
            return bp;
        }
    }

    // 못 찾으면 NULL을 리턴한다.
    return NULL;

}


/*
    place(bp, size)
    : 요구 메모리를 할당할 수 있는 가용 블록을 할당한다. 이 때 분할이 가능하면 분할한다.
*/
static void place(void* bp, size_t asize){
    // 현재 할당할 수 있는 후보 가용 블록의 주소
    size_t csize = GET_SIZE(HDRP(bp));

    // 할당될 블록이므로 free list에서 없애준다.
    removeBlock(bp);

    // 분할이 가능한 경우
    if ((csize - asize) >= (2*DSIZE)){
        // 앞의 블록은 할당 블록으로
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        // 뒤의 블록은 가용 블록으로 분할한다.
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize-asize, 0));
        PUT(FTRP(bp), PACK(csize-asize, 0));

        // free list 첫번째에 분할된 블럭을 넣는다.
        putFreeBlock(bp);
    }
    else{
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

/*
    putFreeBlock(bp) : 새로 반환되거나 생성된 가용 블록을 free list의 첫 부분에 넣는다.
*/
void putFreeBlock(void* bp){
    SUCC_FREEP(bp) = free_listp;
    PREV_FREEP(bp) = NULL;
    PREV_FREEP(free_listp) = bp;
    free_listp = bp;
}

/*
    removeBlock(bp) : 할당되거나 연결되는 가용 블록을 free list에서 없앤다.
*/
void removeBlock(void *bp){
    // free list의 첫번째 블록을 없앨 때
    if (bp == free_listp){
        PREV_FREEP(SUCC_FREEP(bp)) = NULL;
        free_listp = SUCC_FREEP(bp);
    }
    // free list 안에서 없앨 때
    else{
        SUCC_FREEP(PREV_FREEP(bp)) = SUCC_FREEP(bp);
        PREV_FREEP(SUCC_FREEP(bp)) = PREV_FREEP(bp);
    }
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp)
{
    // 해당 블록의 size를 알아내 header와 footer의 정보를 수정한다.
    size_t size = GET_SIZE(HDRP(bp));

    // header와 footer를 설정
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));

    // 만약 앞뒤의 블록이 가용 상태라면 연결한다.
    coalesce(bp);
}


/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr;  // 크기를 조절하고 싶은 힙의 시작 포인터
    void *newptr;        // 크기 조절 뒤의 새 힙의 시작 포인터
    size_t copySize;     // 복사할 힙의 크기
    
    newptr = mm_malloc(size);
    if (newptr == NULL)
      return NULL;

    // copySize = *(size_t *)((char *)oldptr - SIZE_T_SIZE);
    copySize = GET_SIZE(HDRP(oldptr));

    // 원래 메모리 크기보다 적은 크기를 realloc하면 크기에 맞는 메모리만 할당되고 나머지는 안 된다. 
    if (size < copySize)
      copySize = size;

    memcpy(newptr, oldptr, copySize);  // newptr에 oldptr를 시작으로 copySize만큼의 메모리 값을 복사한다.
    mm_free(oldptr);  // 기존의 힙을 반환한다.
    return newptr;
}
