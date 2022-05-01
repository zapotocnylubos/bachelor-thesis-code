#include <stdio.h>

#include "min_heap.h"

void signalizeInvalidInput() {
    printf("Invalid input\n");
}

typedef struct _Vertex {
    
} Vertex;

typedef struct _Edge {
    
} Edge;

typedef struct _LinkedNode {

} LinkedNode;

/*@
    assigns \nothing;
*/
int main() {
    int verticesCount;
    if (scanf("%d", &verticesCount) != 1) {
        signalizeInvalidInput();
        return 1;
    }

    int *vertices = (int *) malloc (verticesCount * sizeof());

    for()

    int arr[100] = {2, 3, 5, 1, 4};
    Heap heap = HeapBuild(arr, 5, 100);
    // printHeap(heap);

    /*@
        loop invariant 0 <= HeapElementsCount(heap);
        loop assigns heap, HeapElements(heap)[0 .. HeapElementsCount(\at(heap, Pre)) - 1];
        loop variant HeapElementsCount(heap);
    */
    while (heap.elementsCount > 0) {
        // printf("M: %d\n", HeapFindMin(heap));
        heap = HeapExtractMin(heap);
        // printHeap(heap);
    }

    int input;
    while (heap.elementsCount < heap.elementsCapacity && scanf("%d", &input) == 1) {
        heap = HeapInsert(heap, input);
        // printf("M: %d\n", HeapFindMin(heap));
        // printHeap(heap);
    }

    if (heap.elementsCount == heap.elementsCapacity) {
        // printf("You have exceeded allocated capacity\n");
        return 1;
    }

    while (heap.elementsCount > 0) {
        // printf("M: %d\n", HeapFindMin(heap));
        heap = HeapExtractMin(heap);
        // printHeap(heap);
    }

    return 0;
}
