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
    logic integer Parent(integer children) = (children - 1) / 2;
    logic integer LeftChildren(integer parent) = 2 * parent + 1;
    logic integer RightChildren(integer parent) = 2 * parent + 2;
*/

/*@
    predicate IsLeftChildren(integer children, integer parent) =
        LeftChildren(parent) == children;

    predicate IsRightChildren(integer children, integer parent) =
        RightChildren(parent) == children;

    predicate IsChildren(integer children, integer parent) =
        IsLeftChildren(children, parent) || IsRightChildren(children, parent);

    predicate IsParent(integer parent, integer children) =
        IsChildren(children, parent);
*/

/*@
    inductive IsDescendant(integer descendant, integer ancestor, Heap *heap) {
        case children:
            \forall integer i, Heap *heap;
                0 < i < HeapElementsCount(heap) ==>
                    IsDescendant(i, Parent(i), heap);

        case descendants:
            \forall integer i, integer ancestor, Heap *heap;
                0 <= ancestor < i < HeapElementsCount(heap) ==>
                    IsDescendant(Parent(i), ancestor, heap) ==> 
                        IsDescendant(i, ancestor, heap);
    }
*/

/*@
    predicate ValidHeap(Heap *heap) =
        \valid(heap)
        && 0 < HeapElementsCount(heap)
        && \valid(HeapElements(heap) + (0 .. HeapElementsCount(heap) - 1))
        && \forall integer ancestor, children;
            0 <= ancestor < children < HeapElementsCount(heap) ==>
                IsDescendant(children, ancestor, heap) ==>
                    HeapElementValue(heap, ancestor) <= HeapElementValue(heap, children);
*/

/*@
    requires ValidHeap(heap);

    assigns \nothing;
    
    ensures \exists integer i;
        HeapElementValue(heap, i) == \result;
    ensures \forall integer i;
        0 <= i < HeapElementsCount(heap) ==>
            IsDescendant(i, 0, heap) ==>
                \result <= HeapElementValue(heap, i);
*/
int HeapFindMin(Heap *heap) {
    return heap->elements[0];
}
