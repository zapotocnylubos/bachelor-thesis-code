#include <stdlib.h>
#include <stdio.h>
#include <limits.h>
#include <math.h>

#include "min_heap.h"

/*@
    ensures \result == \floor(x);
*/
extern double floor(double x);

/*@
    ensures \result == \ceil(x);
*/
extern double ceil(double x);

/*@
    logic integer HeapInternalNodeCount(Heap heap) = \floor(HeapElementsCount(heap) / 2);
    logic integer HeapExternalNodeCount(Heap heap) = \ceil(HeapElementsCount(heap) / 2);
*/

/*@
    predicate HeapHasParent(Heap heap, integer child) =
        0 < child < HeapElementsCount(heap);

    predicate HeapHasLeftChild(Heap heap, integer parent) =
        0 < LeftChild(parent) < HeapElementsCount(heap);

    predicate HeapHasRightChild(Heap heap, integer index) =
        0 < RightChild(index) < HeapElementsCount(heap);

    predicate HeapHasChild(Heap heap, integer index) =
        HeapHasLeftChild(heap, index)
        || HeapHasRightChild(heap, index);

    predicate HeapHasBothChildren(Heap heap, integer index) =
        HeapHasLeftChild(heap, index) && HeapHasRightChild(heap, index);
*/

/*@
    lemma heap_propetry_transitive_left_child:
        \forall Heap heap, integer element;
            0 < element < HeapElementsCount(heap)
            && HasHeapProperty(heap, Parent(element), element)
            && HeapHasLeftChild(heap, element)
            && HasHeapProperty(heap, element, LeftChild(element)) ==>
                HasHeapProperty(heap, Parent(element), LeftChild(element));

    lemma heap_propetry_transitive_right_child:
        \forall Heap heap, integer element;
            0 < element < HeapElementsCount(heap)
            && HasHeapProperty(heap, Parent(element), element)
            && HeapHasRightChild(heap, element)
            && HasHeapProperty(heap, element, RightChild(element)) ==>
                HasHeapProperty(heap, Parent(element), RightChild(element));
*/

/*@
    predicate HeapCutHeapPropertyLeftChild(Heap heap, integer index) = 
        HeapHasParent(heap, index)
        && HeapHasLeftChild(heap, index) ==>
            HasHeapProperty(heap, Parent(index), LeftChild(index));

    predicate HeapCutHeapPropertyRightChild(Heap heap, integer index) =
        HeapHasParent(heap, index)
        && HeapHasRightChild(heap, index) ==>
            HasHeapProperty(heap, Parent(index), RightChild(index));
*/


// ------------------------------------------------------------

/*@
    assigns \nothing;

    ensures \result == HeapElementValue(element);
*/
int _HeapElementValue(HeapElement element) {
    return element.value;
}

/*@
    requires \valid(HeapElements(heap) + (0 .. HeapElementsCount(heap) - 1));
    requires 0 <= index < HeapElementsCount(heap);

    assigns \nothing;

    ensures \result == HeapElementValue(heap, index);
*/
int HeapElementValue(Heap heap, int index) {
    return _HeapElementValue(heap.elements[index]);
}

/*@
    requires \valid(a);
    requires \valid(b);

    assigns *a, *b;

    ensures *a == \old(*b);
    ensures *b == \old(*a);
*/
void swapi(int *a, int *b) {
    int tmp = *a;
    *a = *b;
    *b = tmp;
}

/*@
    requires \valid(a);
    requires \valid(b);
    requires \separated(a, b);

    assigns *a, *b;

    ensures *a == \old(*b);
    ensures *b == \old(*a);
*/
void swapHeapElements(HeapElement *a, HeapElement *b) {
    HeapElement tmp = *a;
    *a = *b;
    *b = tmp;
}

/*@
    requires 0 <= a < HeapElementsCount(heap);
    requires 0 <= b < HeapElementsCount(heap);
    requires \valid(HeapElements(heap) + a);
    requires \valid(HeapElements(heap) + b);

    assigns HeapElements(heap)[a], HeapElements(heap)[b];

    ensures indexes_swapped_a:
        HeapElementIndex(heap, a) == \old(HeapElementIndex(heap, a));
    
    ensures indexes_swapped_b:
        HeapElementIndex(heap, b) == \old(HeapElementIndex(heap, b));

    ensures HeapElementId(heap, a) == \old(HeapElementId(heap, b));
    ensures HeapElementId(heap, b) == \old(HeapElementId(heap, a));

    ensures HeapElementValue(heap, a) == \old(HeapElementValue(heap, b));
    ensures HeapElementValue(heap, b) == \old(HeapElementValue(heap, a));
*/
void HeapSwap(Heap heap, int a, int b) {
    if (a != b) {
        swapi(&(heap.elements[a].index), &(heap.elements[b].index));
        swapHeapElements(heap.elements + a, heap.elements + b);
    }
}

/*@
    requires 0 <= HeapElementsCount(heap);

    assigns \nothing;

    ensures \result == HeapInternalNodeCount(heap);
*/
int HeapInternalNodeCount(Heap heap) {
    return floor(heap.elementsCount / 2);
}

/*@
    requires 0 <= HeapElementsCount(heap);

    assigns \nothing;

    ensures \result == HeapExternalNodeCount(heap);
*/
int HeapExternalNodeCount(Heap heap) {
    return ceil(heap.elementsCount / 2);
}

/*@
    requires 0 < child;

    assigns \nothing;

    ensures \result == Parent(child);
    ensures 0 <= \result < child;
*/
int HeapParent(int child) {
    return (child - 1) / 2;
}

/*@
    requires 0 <= parent;
    requires LeftChild(parent) < INT_MAX;

    assigns \nothing;

    ensures \result == LeftChild(parent);
*/
int HeapLeftChild(int parent) {
    return (2 * parent) + 1;
}

/*@
    requires 0 <= parent;
    requires RightChild(parent) < INT_MAX;

    assigns \nothing;

    ensures \result == RightChild(parent);
*/
int HeapRightChild(int parent) {
    return (2 * parent) + 2;
}

/*@
    requires 0 <= child;

    assigns \nothing;

    behavior has_parent:
        assumes HeapHasParent(heap, child);
        ensures \result == 1;

    behavior has_no_parent:
        assumes !HeapHasParent(heap, child);
        ensures \result == 0;

    complete behaviors;
    disjoint behaviors;
*/
int HeapHasParent(Heap heap, int child) {
    return 0 < child && child < heap.elementsCount;
}

/*@
    requires 0 <= parent < HeapElementsCount(heap);

    assigns \nothing;

    behavior has_left_child:
        assumes HeapHasLeftChild(heap, parent);
        ensures \result == 1;

    behavior has_no_left_child:
        assumes !HeapHasLeftChild(heap, parent);
        ensures \result == 0;

    complete behaviors;
    disjoint behaviors;
*/
int HeapHasLeftChild(Heap heap, int parent) {
    return parent < HeapInternalNodeCount(heap);
}

/*@
    requires 0 <= parent < HeapElementsCount(heap);

    assigns \nothing;

    behavior has_right_child:
        assumes HeapHasRightChild(heap, parent);
        ensures \result == 1;

    behavior has_no_right_child:
        assumes !HeapHasRightChild(heap, parent);
        ensures \result == 0;

    complete behaviors;
    disjoint behaviors;
*/
int HeapHasRightChild(Heap heap, int parent) {
    return HeapHasLeftChild(heap, parent) && HeapRightChild(parent) < heap.elementsCount;
}

/*@
    requires 0 <= parent < HeapElementsCount(heap);

    assigns \nothing;

    behavior has_child:
        assumes HeapHasChild(heap, parent);
        ensures \result == 1;

    behavior has_no_child:
        assumes !HeapHasChild(heap, parent);
        ensures \result == 0;

    complete behaviors;
    disjoint behaviors;
*/
int HeapHasChild(Heap heap, int parent) {
    // In a binary heap, the left child must always be created before the right child
    return HeapHasLeftChild(heap, parent);
}

/*@
    requires 0 <= parent < HeapElementsCount(heap);

    assigns \nothing;

    behavior has_both_children:
        assumes HeapHasBothChildren(heap, parent);
        ensures \result == 1;

    behavior has_less_children:
        assumes !HeapHasBothChildren(heap, parent);
        ensures \result == 0;

    complete behaviors;
    disjoint behaviors;
*/
int HeapHasBothChildren(Heap heap, int parent) {
    return HeapHasLeftChild(heap, parent) && HeapHasRightChild(heap, parent);
}

/*@
    requires \valid(HeapElements(heap) + (0 .. HeapElementsCount(heap) - 1));
    requires 0 <= parent < HeapElementsCount(heap);
    requires HeapHasChild(heap, parent);

    assigns \nothing;

    ensures HeapHasLeftChild(heap, parent) ==>
        HeapElementValue(heap, \result) <= HeapElementValue(heap, LeftChild(parent));

    ensures HeapHasRightChild(heap, parent) ==>
        HeapElementValue(heap, \result) <= HeapElementValue(heap, RightChild(parent));

    behavior has_both_children_left_lower:
        assumes HeapHasBothChildren(heap, parent)
                && HeapElementValue(heap, LeftChild(parent)) < HeapElementValue(heap, RightChild(parent));
        ensures \result == LeftChild(parent);

    behavior has_both_children_right_lower:
        assumes HeapHasBothChildren(heap, parent)
                && HeapElementValue(heap, RightChild(parent)) < HeapElementValue(heap, LeftChild(parent));
        ensures \result == RightChild(parent);

    behavior has_both_children_same:
        assumes HeapHasBothChildren(heap, parent)
                && HeapElementValue(heap, LeftChild(parent)) == HeapElementValue(heap, RightChild(parent));
        ensures \result == LeftChild(parent);

    behavior has_only_left_child:
        assumes !HeapHasBothChildren(heap, parent)
                && HeapHasLeftChild(heap, parent);
        ensures \result == LeftChild(parent);

    complete behaviors;
    disjoint behaviors;
*/
int HeapLowerChild(Heap heap, int parent) {
    int leftChild = HeapLeftChild(parent);
    int rightChild = HeapRightChild(parent);

    if (HeapHasBothChildren(heap, parent)) {
        if (HeapElementValue(heap, leftChild) <= HeapElementValue(heap, rightChild)) {
            return leftChild;
        }

        return rightChild;
    }

    return leftChild;
}

/*@
    // alt-ergo or cvc4 are not able to prove this implication on more
    // than ~80 elements. Z3 is able to prove this implication, but
    // having no need for Z3 in whole codebase, axiom was chosen to keep
    // code simplified

    axiomatic heap_structure_and_heap_property {
        axiom root_is_extreme:
            \forall Heap heap;
                ValidHeap(heap) ==>
                    \forall integer index;
                        0 <= index < HeapElementsCount(heap) ==>
                            HasHeapProperty(heap, 0, index);
    }
*/

HeapElement HeapFindMin(Heap heap) {
    return heap.elements[0];
}

/*@
    predicate HeapUpperChildCut(Heap heap, integer index) =
        \forall integer ancestor, descendant;
            0 <= ancestor < descendant < HeapElementsCount(heap)
            && descendant < index
            && IsParent(ancestor, descendant) ==>
                HasHeapProperty(heap, ancestor, descendant);

    predicate HeapLowerChildCut(Heap heap, integer index) =
        \forall integer ancestor, descendant;
            0 <= ancestor < descendant < HeapElementsCount(heap)
            && index < descendant
            && IsParent(ancestor, descendant) ==>
                HasHeapProperty(heap, ancestor, descendant);
*/

/*@
    requires \valid(HeapElements(heap) + (0 .. HeapElementsCount(heap) - 1));
    requires 0 <= index < HeapElementsCount(heap);
    requires HeapUpperChildCut(heap, index);
    requires HeapLowerChildCut(heap, index);
    requires HeapCutHeapPropertyLeftChild(heap, index);
    requires HeapCutHeapPropertyRightChild(heap, index);

    assigns HeapElements(heap)[0 .. HeapElementsCount(heap) - 1];

    ensures ValidHeap(heap);
*/
void HeapBubbleUp(Heap heap, int index) {
    int parent;

    /*@
        loop invariant 0 <= index < HeapElementsCount(heap);
        loop invariant HeapUpperChildCut(heap, index);
        loop invariant HeapLowerChildCut(heap, index);
        loop invariant HeapCutHeapPropertyLeftChild(heap, index);
        loop invariant HeapCutHeapPropertyRightChild(heap, index);

        loop assigns index, parent, HeapElements(heap)[0 .. HeapElementsCount(heap) - 1];

        loop variant index;
    */
    while (HeapHasParent(heap, index)) {
        parent = HeapParent(index);

        if (HeapElementValue(heap, parent) <= HeapElementValue(heap, index)) {
            break;
        }

        /*
            These asserts help provers to prove these loop invariants:
            - 'HeapUpperChildCut'
        */

        /*@ assert heap_cut_parent_heap_property_right_child:
                IsLeftChild(index, parent)
                && HeapHasRightChild(heap, parent) ==>
                    HasHeapProperty(heap, parent, RightChild(parent));
        */

        /*@ assert heap_cut_parent_heap_property_left_child:
                IsRightChild(index, parent) ==>
                    HasHeapProperty(heap, parent, LeftChild(parent));
        */

        HeapSwap(heap, index, parent);

        index = parent;
    }
}

/*@
    predicate HeapUpperParentCut(Heap heap, integer index) =
        \forall integer ancestor, descendant;
            0 <= ancestor < index
            && ancestor < descendant < HeapElementsCount(heap)
            && IsParent(ancestor, descendant) ==>
                HasHeapProperty(heap, ancestor, descendant);

    predicate HeapLowerParentCut(Heap heap, integer index) =
        \forall integer ancestor, descendant;
            index < ancestor < HeapElementsCount(heap)
            && ancestor < descendant < HeapElementsCount(heap)
            && IsParent(ancestor, descendant) ==>
                HasHeapProperty(heap, ancestor, descendant);
*/

/*@
    requires \valid(HeapElements(heap) + (0 .. HeapElementsCount(heap) - 1));
    requires 0 <= index < HeapElementsCount(heap);
    requires HeapLowerParentCut(heap, index);

    assigns HeapElements(heap)[0 .. HeapElementsCount(heap) - 1];

    ensures partially_valid_heap:
        \forall integer ancestor, descendant;
            index <= ancestor < descendant < HeapElementsCount(heap)
            && IsParent(ancestor, descendant) ==>
                HasHeapProperty(heap, ancestor, descendant);

    behavior full_repair:
        assumes HeapUpperParentCut(heap, index);

        // cannot use predicate here, frama-c yield different proof results

        assumes heap_cut_heap_property_left_child:
            HeapHasParent(heap, index)
            && HeapHasLeftChild(heap, index) ==>
                HasHeapProperty(heap, Parent(index), LeftChild(index));

        assumes heap_cut_heap_property_right_child:
            HeapHasParent(heap, index)
            && HeapHasRightChild(heap, index) ==>
                HasHeapProperty(heap, Parent(index), RightChild(index));

        ensures ValidHeap(heap);
*/
void HeapBubbleDown(Heap heap, int index) {
    int child;

    /*@
        loop invariant 0 <= index < HeapElementsCount(heap);

        loop invariant partial_heap_upper_parent_cut:
            \forall integer ancestor, descendant;
                \at(index, Pre) <= ancestor < index
                && ancestor < descendant < HeapElementsCount(heap)
                && IsParent(ancestor, descendant) ==>
                    HasHeapProperty(heap, ancestor, descendant);

        loop invariant HeapLowerParentCut(heap, index);

        loop invariant partial_heap_parent_cut_heap_property_left_child:
            HeapHasParent(heap, index)
            && \at(index, Pre) <= Parent(index)
            && HeapHasLeftChild(heap, index) ==>
                HasHeapProperty(heap, Parent(index), LeftChild(index));

        loop invariant partial_heap_parent_cut_heap_property_right_child:
            HeapHasParent(heap, index)
            && \at(index, Pre) <= Parent(index)
            && HeapHasRightChild(heap, index) ==>
                HasHeapProperty(heap, Parent(index), RightChild(index));

        loop assigns index, child, HeapElements(heap)[0 .. HeapElementsCount(heap) - 1];

        for full_repair:
            loop invariant HeapUpperParentCut(heap, index);
            loop invariant HeapCutHeapPropertyLeftChild(heap, index);
            loop invariant HeapCutHeapPropertyRightChild(heap, index);

        loop variant HeapElementsCount(heap) - index;
    */
    while (HeapHasChild(heap, index)) {
        child = HeapLowerChild(heap, index);

        if (HeapElementValue(heap, index) <= HeapElementValue(heap, child)) {
            break;
        }

        /*
            These asserts help provers to prove these loop invariants:
            - '[partial_]heap_cut_heap_property_left_child'
            - '[partial_]heap_cut_heap_property_right_child'
        */

        //@ assert HeapHasLeftChild(heap, child) ==> HasHeapProperty(heap, child, LeftChild(child));
        //@ assert HeapHasRightChild(heap, child) ==> HasHeapProperty(heap, child, RightChild(child));

        HeapSwap(heap, index, child);

        index = child;
    }
}

Heap HeapInsert(Heap heap, HeapElement element) {
    int index = heap.elementsCount;

    heap.elements[index] = element;
    heap.elementsCount++;

    HeapBubbleUp(heap, index);

    return heap;
}

Heap HeapExtractMin(Heap heap) {
    int last = heap.elementsCount - 1;

    HeapSwap(heap, 0, last);

    heap.elementsCount--;

    if (0 < heap.elementsCount) {
        HeapBubbleDown(heap, 0);
    }

    return heap;
}

/*@
    requires \valid(HeapElements(heap) + (0 .. HeapElementsCount(heap) - 1));
    requires 0 <= index < HeapElementsCount(heap);
    requires HeapElementValue(element) <= HeapElementValue(heap, index);
    requires ValidHeap(heap);

    assigns HeapElements(heap)[0 .. HeapElementsCount(heap) - 1];

    ensures value_changed:
        \exists integer i;
            0 <= i < HeapElementsCount(heap) ==>
                HeapElementValue(element) == HeapElementValue(heap, i);
    ensures ValidHeap(heap);
*/
void HeapDecrease(Heap heap, int index, HeapElement element) {
    element.index = index;
    heap.elements[index] = element;

    HeapBubbleUp(heap, index);
}

/*@
    requires \valid(HeapElements(heap) + (0 .. HeapElementsCount(heap) - 1));
    requires 0 <= index < HeapElementsCount(heap);
    requires HeapElementValue(heap, index) <= HeapElementValue(element);
    requires ValidHeap(heap);

    assigns HeapElements(heap)[0 .. HeapElementsCount(heap) - 1];

    ensures value_changed:
        \exists integer i;
            0 <= i < HeapElementsCount(heap) ==>
                HeapElementValue(element) == HeapElementValue(heap, i);
    ensures ValidHeap(heap);
*/
void HeapIncrease(Heap heap, int index, HeapElement element) {
    element.index = index;
    heap.elements[index] = element;

    HeapBubbleDown(heap, index);
}

void HeapChange(Heap heap, int index, HeapElement element) {
    if (_HeapElementValue(element) < HeapElementValue(heap, index)) {
        HeapDecrease(heap, index, element);
        return;
    }

    HeapIncrease(heap, index, element);
}

Heap HeapBuild(HeapElement *elements, int elementsCount, int elementsCapacity) {
    Heap heap;
    heap.elements = elements;
    heap.elementsCount = elementsCount;
    heap.elementsCapacity = elementsCapacity;

    /*@
        loop invariant -1 <= index <= ((int)\floor(HeapElementsCount(heap) / 2)) - 1;

        loop invariant partially_valid_heap:
            \forall integer ancestor, descendant;
                index < ancestor < descendant < HeapElementsCount(heap)
                && IsParent(ancestor, descendant) ==>
                    HasHeapProperty(heap, ancestor, descendant);

        loop assigns index, HeapElements(heap)[0 .. HeapElementsCount(heap) - 1];
        loop variant index;
    */
    for (int index = HeapInternalNodeCount(heap) - 1; index >= 0; index--) {
        HeapBubbleDown(heap, index);
    }

    return heap;
}
