#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "min_heap.h"

typedef struct _Vertex Vertex;

typedef struct {
    int toVertexId;
    int weight;
} Edge;

typedef enum {
    NOT_FOUND, 
    OPENED, 
    CLOSED
} VertexState;

struct _Vertex {
    int id;
    VertexState state;
};

typedef struct _VertexListNode {
    Edge edge;
    struct _VertexListNode *next;
} VertexListNode;

typedef struct _VertexList {
    Vertex vertex;
    VertexListNode *neighbors;
    int predecesorVertexId;
} VertexList;

int isValidVertexId(int vertexId, int verticesCount) {
    return (0 <= vertexId) && (vertexId < verticesCount);
}

void printVertices(VertexList *vertices, int verticesCount) {
    for(int i = 0; i < verticesCount; i++) {
        printf("%d: ", i);

        int isFirst = 1;
        VertexListNode *node = vertices[i].neighbors;
        while (node != NULL) {
            if(!isFirst) {
                printf(", ");
            }

            printf("->%d[%d]", node->edge.toVertexId, node->edge.weight);
            node = node->next;
            isFirst = 0;
        }

        printf("\n");
    }
}

int main (int argc, char *argv[]) {
    int interactive = 0;

    if (argc > 1 && 0 == strcmp(argv[1], "--interactive")) {
        interactive = 1;
    }

    if (interactive) {
        printf("Count of verticies:\n");
    }

    int verticesCount;
    if (scanf("%d", &verticesCount) != 1) {
        return 1;
    }

    VertexList *vertices = (VertexList *) malloc (verticesCount * sizeof(VertexList));
    if (vertices == NULL) {
        return 2;
    }

    if (interactive) {
        printf("Start vertex index:\n");
    }

    int startVertexId;
    if (scanf("%d", &startVertexId) != 1 || !isValidVertexId(startVertexId, verticesCount)) {
        return 1;
    }

    if (interactive) {
        printf("End vertex index:\n");
    }

    int endVertexId;
    if (scanf("%d", &endVertexId) != 1 || !isValidVertexId(endVertexId, verticesCount)) {
        return 1;
    }

    if (interactive) {
        printf("Start entering edges:\n");
        printf("<from-index> <to-index> <weight>\n");
    }

    int fromVertexId, toVertexId, weight;
    while (
        scanf("%d %d %d", &fromVertexId, &toVertexId, &weight) == 3 
        && isValidVertexId(fromVertexId, verticesCount) 
        && isValidVertexId(toVertexId, verticesCount)
    ) {
        Edge edge = { .toVertexId = toVertexId, .weight = weight };
        
        VertexListNode *listNode = (VertexListNode *) malloc (sizeof(VertexListNode));
        if (listNode == NULL) {
            return 2;
        }

        listNode->edge = edge;
        listNode->next = vertices[fromVertexId].neighbors;

        vertices[fromVertexId].neighbors = listNode;
    }

    if (interactive) {
        printf("Vertices:\n");
        printVertices(vertices, verticesCount);
    }




    // // for()

    // int arr[100] = {2, 3, 5, 1, 4};
    // Heap heap = HeapBuild(arr, 5, 100);
    // // printHeap(heap);

    // /*@
    //     loop invariant 0 <= HeapElementsCount(heap);
    //     loop assigns heap, HeapElements(heap)[0 .. HeapElementsCount(heap) - 1];
    //     loop variant HeapElementsCount(heap);
    // */
    // while (heap.elementsCount > 0) {
    //     // printf("M: %d\n", HeapFindMin(heap));
    //     heap = HeapExtractMin(heap);
    //     // printHeap(heap);
    // }

    // int input;
    // while (heap.elementsCount < heap.elementsCapacity && scanf("%d", &input) == 1) {
    //     heap = HeapInsert(heap, input);
    //     // printf("M: %d\n", HeapFindMin(heap));
    //     // printHeap(heap);
    // }

    // if (heap.elementsCount == heap.elementsCapacity) {
    //     // printf("You have exceeded allocated capacity\n");
    //     return 1;
    // }

    // while (heap.elementsCount > 0) {
    //     // printf("M: %d\n", HeapFindMin(heap));
    //     heap = HeapExtractMin(heap);
    //     // printHeap(heap);
    // }

    return 0;
}
