#ifndef ZAPOTOCNYLUBOS_MIN_HEAP_H
#define ZAPOTOCNYLUBOS_MIN_HEAP_H

typedef struct _HeapElement {
    int index;

    int id;
    int value;
} HeapElement;

/*@
    logic int HeapElementIndex(HeapElement element) = element.index;
    logic int HeapElementId(HeapElement element) = element.id;
    logic int HeapElementValue(HeapElement element) = element.value;
*/

typedef struct _Heap {
    HeapElement *elements;
    int elementsCount;
    int elementsCapacity;
} Heap;

/*@
    logic HeapElement *HeapElements(Heap heap) = heap.elements;
    logic int HeapElementsCount(Heap heap) = heap.elementsCount;
    logic int HeapElementsCapacity(Heap heap) = heap.elementsCapacity;

    logic int HeapElementIndex(Heap heap, integer i) = HeapElementIndex(heap.elements[i]);
    logic int HeapElementId(Heap heap, integer i) = HeapElementId(heap.elements[i]);
    logic int HeapElementValue(Heap heap, integer i) = HeapElementValue(heap.elements[i]);
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
                \result == HeapElements(heap)[i];

    ensures correct_extreme:
        \forall integer i;
            0 < i < HeapElementsCount(heap) ==>
                HasHeapProperty(heap, 0, i);
*/
HeapElement HeapFindMin(Heap heap);

/*@
    requires 0 <= HeapElementsCount(heap) < HeapElementsCapacity(heap);
    requires \valid(HeapElements(heap) + (0 .. HeapElementsCapacity(heap) - 1));
    requires ValidHeap(heap);
    requires correctly_indexed: HeapElementIndex(element) == HeapElementsCount(heap);

    assigns HeapElements(heap)[0..HeapElementsCount(heap)];

    ensures count_increase: HeapElementsCount(\result) == HeapElementsCount(heap) + 1;
    ensures ValidHeap(\result);
*/
Heap HeapInsert(Heap heap, HeapElement element);

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
    requires \valid(HeapElements(heap) + (0 .. HeapElementsCount(heap) - 1));
    requires 0 <= index < HeapElementsCount(heap);
    requires ValidHeap(heap);

    assigns HeapElements(heap)[0 .. HeapElementsCount(heap) - 1];

    ensures value_changed:
        \exists integer i;
            0 <= i < HeapElementsCount(heap) ==>
                HeapElementValue(element) == HeapElementValue(heap, i);
    ensures ValidHeap(heap);
*/
void HeapChange(Heap heap, int index, HeapElement element);

/*@
    requires 0 <= elementsCount <= elementsCapacity;
    requires \valid(elements + (0 .. elementsCount - 1));
    requires correctly_indexed:
        \forall integer i;
            0 <= i < elementsCount ==>
                HeapElementIndex(elements[i]) == i;

    assigns elements[0 .. elementsCount - 1];

    ensures count_same: HeapElementsCount(\result) == elementsCount;
    ensures capacity_same: HeapElementsCapacity(\result) == elementsCapacity;
    ensures ValidHeap(\result);
*/
Heap HeapBuild(HeapElement *elements, int elementsCount, int elementsCapacity);

#endif //ZAPOTOCNYLUBOS_MIN_HEAP_H