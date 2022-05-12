#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <limits.h>

#include "min_heap.h"

typedef struct {
    int toVertexId;
    int weight;
} Edge;

typedef struct _VertexListNode {
    Edge edge;
    struct _VertexListNode *next;
} VertexListNode;

typedef struct _VertexList {
    HeapElement *vertex;
    VertexListNode *neighbors;

    int extracted;
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

            printf("%d[%d]", node->edge.toVertexId, node->edge.weight);
            node = node->next;
            isFirst = 0;
        }

        printf("\n");
    }
}

void printShortesPath(VertexList *vertices, int endVertexId) {
    if(endVertexId == -1) {
        return;
    }

    printShortesPath(vertices, vertices[endVertexId].predecesorVertexId);
    printf("%d\n", endVertexId);
}

/*
 * Usage:
 * 	./shortest_path [--interactive]
 *
 * Input:
 * 	<count_of_verticies>
 * 	<start_vertex_index>
 * 	<end_vertex_index>
 * 	(<from-index> <to-index> <weight>)*
 * 
 * Output:
 * 	Indexes of vertices representing shortes path
 * 	from start vertex to end vertex.
 */
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
    while (scanf("%d %d %d", &fromVertexId, &toVertexId, &weight) == 3) {
        if (!isValidVertexId(fromVertexId, verticesCount)
            || !isValidVertexId(toVertexId, verticesCount)
            || weight < 0
        ) {
            printf("Invalid input\n");
            return 1;
        }

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

    HeapElement *heapElements = (HeapElement *) malloc (verticesCount * sizeof(HeapElement));
    
    for (int i = 0; i < verticesCount; i++) {
        HeapElement *element = heapElements + i;
        element->index = i;
        element->id = i;
        element->value = INT_MAX;
        
        vertices[i].vertex = element;
        vertices[i].extracted = 0;
        vertices[i].predecesorVertexId = -1;
    }

    vertices[startVertexId].vertex->value = 0;

    Heap heap = HeapBuild(heapElements, verticesCount, verticesCount);
    
    while (0 < heap.elementsCount) {
        HeapElement v = HeapFindMin(heap);
        heap = HeapExtractMin(heap);
        vertices[v.id].extracted = 1;

        VertexListNode *w = vertices[v.id].neighbors;
        while (w != NULL) {
            if (!vertices[w->edge.toVertexId].extracted 
                && vertices[w->edge.toVertexId].vertex->value > vertices[v.id].vertex->value + w->edge.weight
            ) {
                vertices[w->edge.toVertexId].predecesorVertexId = v.id;
                HeapElement element = *vertices[w->edge.toVertexId].vertex;
                element.value = vertices[v.id].vertex->value + w->edge.weight;
                HeapChange(heap, w->edge.toVertexId, element);
            }

            w = w->next;
        }
    }

    if (interactive) {
        printf("Shortes path:\n");
    }

    printShortesPath(vertices, endVertexId);
    
    return 0;
}
