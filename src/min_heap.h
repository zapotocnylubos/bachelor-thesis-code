#ifndef ZAPOTOCNYLUBOS_MIN_HEAP_H
#define ZAPOTOCNYLUBOS_MIN_HEAP_H

typedef struct _Heap {
    int *elements;
    int elementsCount;
    int elementsCapacity;
} Heap;

/*@
    logic int *HeapElements(Heap heap) = heap.elements;
    logic int HeapElementsCount(Heap heap) = heap.elementsCount;
    logic int HeapElementsCapacity(Heap heap) = heap.elementsCapacity;
    logic int HeapElementValue(Heap heap, integer i) = heap.elements[i];
*/

/*@
    logic integer Parent(integer child) = (child - 1) / 2;
    logic integer LeftChild(integer parent) = 2 * parent + 1;
    logic integer RightChild(integer parent) = 2 * parent + 2;
*/

/*@
    predicate IsLeftChild(integer child, integer parent) = LeftChild(parent) == child;
    predicate IsRightChild(integer child, integer parent) = RightChild(parent) == child;
    predicate IsParent(integer parent, integer child) = Parent(child) == parent;

    predicate IsChild(integer child, integer parent) = 
        IsLeftChild(child, parent) || IsRightChild(child, parent);
*/

/*@
    predicate HasHeapProperty(Heap heap, integer parent, integer child) = 
        HeapElementValue(heap, parent) <= HeapElementValue(heap, child);
*/

/*@
    predicate ValidHeap(Heap heap) =
        \forall integer ancestor, descendant;
            0 <= ancestor < descendant < HeapElementsCount(heap)
            && IsParent(ancestor, descendant) ==>
                HasHeapProperty(heap, ancestor, descendant);
*/

// ------------------------------------------------------------

/*@
    requires 0 < HeapElementsCount(heap);
    requires \valid(HeapElements(heap) + (0 .. HeapElementsCount(heap) - 1));
    requires ValidHeap(heap);
    
    assigns \nothing;

    ensures extreme_exists:
        \exists integer i;
            0 <= i < HeapElementsCount(heap) ==>
                \result == HeapElementValue(heap, i);
    
    ensures correct_extreme:
        \forall integer i;
            0 < i < HeapElementsCount(heap) ==>
                HasHeapProperty(heap, 0, i);
*/
int HeapFindMin(Heap heap);

/*@
    requires 0 <= HeapElementsCount(heap) < HeapElementsCapacity(heap);
    requires \valid(HeapElements(heap) + (0 .. HeapElementsCapacity(heap) - 1));
    requires ValidHeap(heap);

    assigns HeapElements(heap)[0..HeapElementsCount(heap)];

    ensures count_increase: HeapElementsCount(\result) == HeapElementsCount(heap) + 1;
    ensures ValidHeap(\result);
*/
Heap HeapInsert(Heap heap, int element);

/*@
    requires 0 < HeapElementsCount(heap);
    requires \valid(HeapElements(heap) + (0 .. HeapElementsCount(heap) - 1));
    requires ValidHeap(heap);

    assigns HeapElements(heap)[0 .. HeapElementsCount(heap) - 1];

    ensures count_decrease: HeapElementsCount(\result) == HeapElementsCount(heap) - 1;
    ensures ValidHeap(\result);
*/
Heap HeapExtractMin(Heap heap);

/*@
    requires 0 <= elementsCount <= elementsCapacity;
    requires \valid(elements + (0 .. elementsCount - 1));

    assigns elements[0 .. elementsCount - 1];

    ensures count_same: HeapElementsCount(\result) == elementsCount;
    ensures capacity_same: HeapElementsCapacity(\result) == elementsCapacity;
    ensures ValidHeap(\result);
*/
Heap HeapBuild(int *elements, int elementsCount, int elementsCapacity);

#endif //ZAPOTOCNYLUBOS_MIN_HEAP_H