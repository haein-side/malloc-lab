/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 * 
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  
 * 블럭이 할당될 때 블럭 포인터를 증가시키면서 할당됨
 * A block is pure payload. There are no headers or
 * footers.  
 * 블럭은 순수하게 전송되는 데이터(payload), 헤더나 푸터가 없음
 * Blocks are never coalesced or reused. Realloc is
 * implemented directly using mm_malloc and mm_free.
 * 블럭은 연결되거나 재사용되지 않음
 * 리얼록의 경우 mm_malloc 또는 mm_free가 적용됨
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

/* Basic constants and macros */
#define WSIZE 4 
#define DSIZE 8
#define CHUNKSIZE (1 << 12)                         // 초기 가용 블록과 힙 확장을 위한 기본 크기

#define MAX(x, y) ((x) > (y)? (x) : (y))

/* Pack a size and allocted bit into a word */
/* 헤더와 푸터에 저장할 수 있는 값(전체 사이즈와 할당 여부 인코딩 된 값) 리턴 */
#define PACK(size, alloc) ((size) | (alloc))

/* Read and write a word at address p */
/* 인자 p가 참조하는 워드 값 리턴 혹은 저장*/
#define GET(p) (*(unsigned int *)(p))              // 주소값 p에 있는 값 리턴
#define PUT(p, val) (*(unsigned int *)(p) = (val)) // 주소값 p에 val 저장 

/* Read the size and allocated fields from address p */
/* 헤더 또는 푸터를 가리키는 포인터를 인자로 전체 블럭 size, 할당 여부 비트 리턴 */
#define GET_SIZE(p) (GET(p) & ~0x7)                 // 전체 블럭 크기 리턴 (헤더 + 데이터 + 푸터)
#define GET_ALLOC(p) (GET(p) & 0x1)                 // 할당 여부 리턴 (할당 시 1, 가용 시 0)

/* Given block ptr bp, compute address of its header and footer */
/* 헤더 또는 푸터의 포인터 */
#define HDRP(bp) ((char *)(bp) - WSIZE)             // 헤더를 가리키는 포인터 리턴
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) // 푸터를 가리키는 포인터 리턴

/* Given block ptr bp, compute address of next and previous blocks */
/* 다음과 이전 블록의 블록 포인터를 리턴 */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE))) // 다음 블럭의 블럭 포인터
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE))) // 이전 블럭의 블럭 포인터

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

// 프롤로그 블럭을 가리키는 변수
static void *heap_listp = NULL;

// 함수 프로토타입 선언
int mm_init(void);
void *mm_malloc(size_t size);
void mm_free(void *ptr);
void *mm_realloc(void *ptr, size_t size);
static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);

/* 
 * mm_init - initialize the malloc package.
 * 최초 가용 블럭으로 힙을 생성하기
 */
int mm_init(void)
{
    /* 비어있는 힙 초기화 */
    if((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1){ // 추가적인 힙 메모리 할당 에러 발생 시 -1 반환
        return -1;
    }
    
    PUT(heap_listp, 0);                                 // 미사용 패딩 워드
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1));        // 프롤로그 헤더
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1));        // 프롤로그 푸터
    PUT(heap_listp + (3*WSIZE), PACK(0, 1));            // 에필로그 헤더
    heap_listp += (2*WSIZE);

    /* CHUNKSIZE 바이트의 가용한 블럭만큼 비어있는 힙을 늘려줌 */
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL){
        return -1;
    }
    return 0;
}

/* 새 가용 블럭으로 힙 확장 */
static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    /* 정렬 유지 위해 8의 배수로 반올림하여 추가적인 힙 공간 요청 */
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1){
        return NULL;
    }

    /* 새로 할당한 블록의 헤더, 푸터, 에필로그 헤더를 초기화 */
    PUT(HDRP(bp), PACK(size, 0));                       // 헤더
    PUT(FTRP(bp), PACK(size, 0));                       // 푸터
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));            // 에필로그 헤더

    /* 이전 블럭이 가용상태이면 연결 */
    return coalesce(bp);

}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 * mm_malloc 가용 리스트에서 블럭 확장하기
 */
void *mm_malloc(size_t size)
{
    size_t asize;       // 조정된 블럭 사이즈
    size_t extendsize;  // 맞지 않을 때 늘려준 힙의 양
    char *bp;

    // 가짜 요청을 무시
    if (size == 0){
        return NULL;
    }

    // 오버헤드와 정렬 조건을 맞추기 위해 블럭 사이즈 조정
    if (size <= DSIZE){
        asize = 2 * DSIZE;
    } else {
        asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);
    }

    // 적절한 가용 블럭을 가용 리스트에서 검색하여 요청 블럭을 가용 블럭의 시작 부분에 배치
    if ((bp = find_fit(asize)) != NULL){
        place(bp, asize);
        return bp;
    } 

    // 잘 맞는 가용블럭을 찾지 못할 때, 블럭에 더 메모리를 늘려서 배치
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL){
        return NULL;
    }
    place(bp, asize);
    return bp;

}

/* 묵시적 가용 리스트에서 크기가 적합한 가용 블럭 검색 수행 */
static void *find_fit(size_t asize){

    /* First-fit search */
    void *bp;

    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)){
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))){
            return bp;
        }
    }

    return NULL; /* No fit */
  
    // 내가 짰던 코드
    // char *bp = heap_listp + (4*WSIZE); // 예외처리 필요할 듯
    // while (힙의 전체 길이 >= FTRP(bp) + WSIZE){ // 힙의 전체 길이 어떻게?
    //     if (GET_ALLOC(HDRP(bp)) == 1){
    //         bp = NEXT_BLKP(bp);
    //     } else {
    //         if (GET_SIZE(HDRP(bp)) >= asize){
    //             return (void *) bp;
    //         }
    //     }
    // }
}

/* 요청한 블럭을 가용 블럭의 시작부분에 배치 = 즉 할당된 상태인 1로 만들어주기 */
static void place(void *bp, size_t asize){
    size_t csize = GET_SIZE(HDRP(bp));  // 할당된 전체 크기

    if ((csize - asize) >= (2*DSIZE)){  // 할당된 전체 크기 - 조정된 크기 >= 최소 블럭 크기 
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize - asize, 0));
        PUT(FTRP(bp), PACK(csize - asize, 0));
    }
    else {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

/*
 * mm_free - Freeing a block does nothing.
 * ptr 포인터가 가리키는 블럭을 반환하고 가용하게 연결
 */
void mm_free(void *ptr)
{
    size_t size = GET_SIZE(HDRP(ptr));

    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));
    coalesce(ptr);
}

/* 경계 태그 연결을 사용해서 인접 가용 블럭들과 통합 */
static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc){
        return bp;
    }
    else if (prev_alloc && !next_alloc){
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    else if (!prev_alloc && next_alloc){
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    else {
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    } 
    return bp;
    
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */

// void *mm_realloc(void *bp, size_t size){
//     if(size <= 0){ 
//         mm_free(bp);
//         return 0;
//     }
//     if(bp == NULL){
//         return mm_malloc(size); 
//     }
//     void *newp = mm_malloc(size); 
//     if(newp == NULL){
//         return 0;
//     }
//     size_t oldsize = GET_SIZE(HDRP(bp));
//     if(size < oldsize){
//     	oldsize = size; 
// 	}
//     memcpy(newp, bp, oldsize); 
//     mm_free(bp);
//     return newp;
// }

void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;
    newptr = mm_malloc(size);
    if (newptr == NULL)
        return NULL;
    copySize = GET_SIZE(HDRP(oldptr));
    if (size < copySize)
    {
        copySize = size;
    }
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}





