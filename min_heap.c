//                  root at 0           root at 1
// Left children    2 * index + 1       2 * index
// Right children   2 * index + 2       2 * index + 1
// Parent           (index - 1) / 2     index / 2

typedef struct {
    int *elements;
    int count;
    int capacity;
} Heap;

/*@
    logic int * HeapElements{L}(Heap *heap) = heap->elements;
    logic int   HeapElementsCount{L}(Heap *heap) = heap->count;
    logic int   HeapElementsCapacity{L}(Heap *heap) = heap->capacity;
    logic int   HeapElementValue{L}(Heap *heap, integer i) = heap->elements[i];
*/

/*@
    predicate IsLeftChildren(integer children, integer parent) =
        (2 * parent + 1) == children;

    predicate IsRightChildren(integer children, integer parent) =
        (2 * parent + 2) == children;

    predicate IsChildren(integer children, integer parent) =
        IsLeftChildren(children, parent) || IsRightChildren(children, parent);
*/

/*@
    predicate ValidHeapArrangement(Heap *heap) =
        \valid(heap)
        && \valid(HeapElements(heap) + (0 .. HeapElementsCount(heap) - 1))
        && 0 <= HeapElementsCount(heap)
        && \forall integer x, y;
            0 <= x < HeapElementsCount(heap)
            && 0 <= y < HeapElementsCount(heap) ==>
                IsChildren(y, x) <==>
                    HeapElementValue(heap, x) <= HeapElementValue(heap, y);
*/

/*@
    requires ValidHeapArrangement(heap);
    assigns \nothing;
    ensures \forall integer i;
        0 <= i < HeapElementsCount(heap) ==>
            \result <= HeapElementValue(heap, i);
*/
int HeapFindMin(Heap *heap) {
    return heap->elements[0];
}