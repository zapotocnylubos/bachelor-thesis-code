#include <stdlib.h>
#include <stdio.h>

//                  root at 0           root at 1
// Left child       2 * index + 1       2 * index
// Right child      2 * index + 2       2 * index + 1
// Parent           (index - 1) / 2     index / 2

typedef struct {
    int *elements;
    int elementsCount;
    int elementsCapacity;
} Heap;

/*@
    logic int * HeapElements         (Heap *heap)            = heap->elements;
    logic int   HeapElementsCount    (Heap *heap)            = heap->elementsCount;
    logic int   HeapElementsCapacity (Heap *heap)            = heap->elementsCapacity;
    logic int   HeapElementValue     (Heap *heap, integer i) = heap->elements[i];
*/

/*@
    logic integer Parent     (integer child)  = (child - 1) / 2;
    logic integer LeftChild  (integer parent) = 2 * parent + 1;
    logic integer RightChild (integer parent) = 2 * parent + 2;
*/

/*@
    predicate IsLeftChild(integer child, integer parent) =
        LeftChild(parent) == child;

    predicate IsRightChild(integer child, integer parent) =
        RightChild(parent) == child;

    predicate IsChild(integer child, integer parent) =
        IsLeftChild(child, parent) || IsRightChild(child, parent);

    predicate IsParent(integer parent, integer child) =
        IsChild(child, parent);
*/

/*@
    inductive IsDescendant(integer descendant, integer ancestor, Heap *heap) {
        case children:
            \forall integer child, Heap *heap;
                0 < child < HeapElementsCount(heap) ==>
                    IsDescendant(child, Parent(child), heap);

        case descendants:
            \forall integer ancestor, element, Heap *heap;
                0 <= ancestor < element < HeapElementsCount(heap) ==>
                    IsDescendant(Parent(element), ancestor, heap) ==> 
                        IsDescendant(element, ancestor, heap);
    }
*/

/*@
    predicate ValidHeap(Heap *heap) =
        \valid(heap)
        && 0 < HeapElementsCount(heap)
        && \valid(HeapElements(heap) + (0 .. HeapElementsCount(heap) - 1))
        && \forall integer ancestor, element;
            0 <= ancestor < element < HeapElementsCount(heap) ==>
                IsDescendant(element, ancestor, heap) ==>
                    HeapElementValue(heap, ancestor) <= HeapElementValue(heap, element);
*/

/*@
    requires ValidHeap(heap);
    
    ensures \exists integer i;
        0 <= i < HeapElementsCount(heap) ==>
            \result == HeapElementValue(heap, i);
    
    ensures \forall integer i;
        0 <= i < HeapElementsCount(heap) ==>
            IsDescendant(i, 0, heap) ==>
                \result <= HeapElementValue(heap, i);
    
    assigns \nothing;
*/
int HeapFindMin(Heap *heap) {
    return heap->elements[0];
}

/*@
    requires child > 0;
    ensures \result == Parent(child);
    assigns \nothing;
*/
int HeapParent(int child) {
    return (child - 1) / 2;
}

/*@
    requires parent >= 0;
    ensures \result == LeftChild(parent);
    assigns \nothing;
*/
int HeapLeftChild(int parent) {
    return (2 * parent) + 1;   
}

/*@
    requires parent >= 0;
    ensures \result == RightChild(parent);
    assigns \nothing;
*/
int HeapRightChild(int parent) {
    return (2 * parent) + 2;
}

void HeapBubbleUp(Heap *heap, int index) {
    while (index > 0) {
        int parent = HeapParent(index);

        if (heap->elements[parent] <= heap->elements[index]){
            return;
        }

        int tmp = heap->elements[parent];
        heap->elements[parent] = heap->elements[index];
        heap->elements[index] = tmp;

        index = parent;
    }
}

void HeapInsert(Heap *heap, int element) {
    int index = heap->elementsCount;

    if (++heap->elementsCount > heap->elementsCapacity) {
        heap->elementsCapacity = 2 * heap->elementsCount;
        heap->elements = (int *) realloc(heap->elements, heap->elementsCapacity);
    }

    heap->elements[index] = element;
    HeapBubbleUp(heap, index);
}

int HeapHasLeftChild(Heap *heap, int index) {
    return HeapLeftChild(index) < heap->elementsCount;
}

int HeapHasRightChild(Heap *heap, int index) {
    return HeapRightChild(index) < heap->elementsCount;
}

int HeapHasChild(Heap *heap, int index) {
    return HeapHasLeftChild(heap, index) || HeapHasRightChild(heap, index);
}

int HeapHasBothChildren(Heap *heap, int index) {
    return HeapHasLeftChild(heap, index) && HeapHasRightChild(heap, index);
}

int HeapGetLowerChild(Heap *heap, int index) {
    int leftChild = HeapLeftChild(index);
    int rightChild = HeapRightChild(index);

    if (HeapHasBothChildren(heap, index)) {
        if (heap->elements[leftChild] < heap->elements[rightChild]) {
            return leftChild;
        }

        return rightChild;
    }

    if (HeapHasLeftChild(heap, index)) {
        return leftChild;
    }

    return rightChild;
}

void HeapBubbleDown(Heap *heap, int index) {
    while (HeapHasChild(heap, index)) {
        int child = HeapGetLowerChild(heap, index);

        if (heap->elements[index] <= heap->elements[child]){
            return;
        }

        int tmp = heap->elements[child];
        heap->elements[child] = heap->elements[index];
        heap->elements[index] = tmp;

        index = child;
    }
}

void HeapExtractMin(Heap *heap) {
    int last = heap->elementsCount - 1;

    int tmp = heap->elements[0];
    heap->elements[0] = heap->elements[last];
    heap->elements[last] = tmp;

    heap->elementsCount--;
    HeapBubbleDown(heap, 0);
}

Heap *HeapBuild() {
    Heap *heap = (Heap *) malloc (sizeof(Heap));
    heap->elementsCount = 0;
    heap->elementsCapacity = 0;
    return heap;
}

int main() {
    Heap *heap = HeapBuild();
    HeapInsert(heap, 3);
    HeapInsert(heap, 2);
    HeapInsert(heap, 1);
    printf("%d\n", HeapFindMin(heap));
    HeapExtractMin(heap);
    printf("%d\n", HeapFindMin(heap));
    HeapExtractMin(heap);
    printf("%d\n", HeapFindMin(heap));
    HeapExtractMin(heap);
}