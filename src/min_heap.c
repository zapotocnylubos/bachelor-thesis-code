#include <stdlib.h>
#include <stdio.h>
#include <limits.h>
#include <math.h>

/*@
    ensures \result == \floor(x);
*/
extern double floor(double x);

/*@
    ensures \result == \ceil(x);
*/
extern double ceil(double x);

//                  root at 0           root at 1
// Left child       2 * index + 1       2 * index
// Right child      2 * index + 2       2 * index + 1
// Parent           (index - 1) / 2     index / 2

typedef struct _Heap {
    int *elements;
    int elementsCount;
    int elementsCapacity;
} Heap;

/*@
    logic int * HeapElements         (Heap heap)            = heap.elements;
    logic int   HeapElementsCount    (Heap heap)            = heap.elementsCount;
    logic int   HeapElementsCapacity (Heap heap)            = heap.elementsCapacity;
    logic int   HeapElementValue     (Heap heap, integer i) = heap.elements[i];
*/

/*@
    logic integer Parent     (integer child)  = (child - 1) / 2;
    logic integer LeftChild  (integer parent) = 2 * parent + 1;
    logic integer RightChild (integer parent) = 2 * parent + 2;
*/

/*@
    logic integer HeapInternalNodeCount(Heap heap) = \floor(HeapElementsCount(heap) / 2);
    logic integer HeapExternalNodeCount(Heap heap) = \ceil(HeapElementsCount(heap) / 2);
*/

/*@
    predicate HasHeapProperty(Heap heap, integer parent, integer child) = 
        HeapElementValue(heap, parent) <= HeapElementValue(heap, child);

    // predicate ValidHeap(Heap heap) =
    //     \forall integer parent, child;
    //         0 <= parent < child < HeapElementsCount(heap) ==>
    //             HasHeapProperty(heap, parent, child);
*/

/*@
    predicate HeapHasParent(Heap heap, integer index) =
        0 <= Parent(index) < HeapElementsCount(heap);

    predicate HeapHasLeftChild(Heap heap, integer index) =
        0 < LeftChild(index) < HeapElementsCount(heap);
    
    predicate HeapHasRightChild(Heap heap, integer index) =
        0 < RightChild(index) < HeapElementsCount(heap);

    predicate HeapHasChild(Heap heap, integer index) =
        HeapHasLeftChild(heap, index)
        || HeapHasRightChild(heap, index);

    predicate HeapHasBothChildren(Heap heap, integer index) =
        HeapHasLeftChild(heap, index) && HeapHasRightChild(heap, index);
*/

/*@
    predicate IsLeftChild(integer child, integer parent) =
        LeftChild(parent) == child;

    predicate IsRightChild(integer child, integer parent) =
        RightChild(parent) == child;

    predicate IsChild(integer child, integer parent) =
        IsLeftChild(child, parent) || IsRightChild(child, parent);

    predicate IsParent(integer parent, integer child) =
        parent == Parent(child);
*/


/*@
    requires \valid(a) && \valid(b);
    assigns *a, *b;
    ensures *a == \old(*b) && *b == \old(*a);
*/
void swap(int *a, int *b) {
    int tmp = *a;
    *a = *b;
    *b = tmp;
}

/*@
    requires 0 <= HeapElementsCount(heap);

    assigns \nothing;

    ensures \result == HeapInternalNodeCount(heap);
*/
inline int HeapInternalNodeCount(Heap heap) {
    return floor(heap.elementsCount / 2);
}

/*@
    requires 0 <= HeapElementsCount(heap);

    assigns \nothing;

    ensures \result == HeapExternalNodeCount(heap);
*/
inline int HeapExternalNodeCount(Heap heap) {
    return ceil(heap.elementsCount / 2);
}

/*@
    requires 0 < child;

    assigns \nothing;

    ensures \result == Parent(child);
    ensures 0 <= \result < child;
*/
inline int HeapParent(int child) {
    return (child - 1) / 2;
}

/*@
    requires 0 <= parent;
    requires LeftChild(parent) < INT_MAX;

    assigns \nothing;

    ensures \result == LeftChild(parent);
*/
inline int HeapLeftChild(int parent) {
    return (2 * parent) + 1;   
}

/*@
    requires 0 <= parent;
    requires RightChild(parent) < INT_MAX;

    assigns \nothing;

    ensures \result == RightChild(parent);
*/
inline int HeapRightChild(int parent) {
    return (2 * parent) + 2;
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
inline int HeapHasLeftChild(Heap heap, int parent) {
    return (0 <= parent) && (parent < HeapInternalNodeCount(heap));
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
inline int HeapHasRightChild(Heap heap, int parent) {
    return HeapHasLeftChild(heap, parent) && (HeapRightChild(parent) < heap.elementsCount);
}

/*@
    requires 0 <= parent < HeapElementsCount(heap);
    // requires LeftChild(parent) < INT_MAX;
    // requires RightChild(parent) < INT_MAX;

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
    return HeapHasLeftChild(heap, parent) || HeapHasRightChild(heap, parent);
}

/*@
    requires 0 <= parent < HeapElementsCount(heap);
    requires LeftChild(parent) < INT_MAX;
    requires RightChild(parent) < INT_MAX;

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

    behavior has_only_right_child:
        assumes !HeapHasBothChildren(heap, parent)
                && HeapHasRightChild(heap, parent);
        ensures \result == RightChild(parent);
    
    complete behaviors;
    disjoint behaviors;
*/
int HeapLowerChild(Heap heap, int parent) {
    int leftChild = HeapLeftChild(parent);
    int rightChild = HeapRightChild(parent);

    if (HeapHasBothChildren(heap, parent)) {
        if (heap.elements[leftChild] <= heap.elements[rightChild]) {
            return leftChild;
        }

        return rightChild;
    }

    if (HeapHasLeftChild(heap, parent)) {
        return leftChild;
    }

    return rightChild;
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
    predicate HeapCutParent(Heap heap, integer from, integer to) = 
        \forall integer ancestor, descendant;
            from <= ancestor < to
            && ancestor < descendant < HeapElementsCount(heap)
            && IsParent(ancestor, descendant) ==>
                HasHeapProperty(heap, ancestor, descendant);
    
    predicate HeapUpperCutParent(Heap heap, integer index) = HeapCutParent(heap, 0, index);
    predicate HeapLowerCutParent(Heap heap, integer index) = HeapCutParent(heap, index + 1, HeapElementsCount(heap));
*/

/*@
    requires \valid(HeapElements(heap) + (0 .. HeapElementsCount(heap) - 1));
    requires 0 <= index < HeapElementsCount(heap);

    requires HeapLowerParentCut(heap, index);

    assigns HeapElements(heap)[0 .. HeapElementsCount(heap) - 1];

    // ensures HeapLowerParentCut(heap, index);

    ensures partially_repaired_heap:
        \forall integer ancestor, descendant;
            index <= ancestor < descendant < HeapElementsCount(heap)
            && IsParent(ancestor, descendant) ==>
                HasHeapProperty(heap, ancestor, descendant);

    behavior full_repair:
        assumes \forall integer ancestor, descendant;
            0 <= ancestor < index
            && ancestor < descendant < HeapElementsCount(heap)
            && IsParent(ancestor, descendant) ==>
                HasHeapProperty(heap, ancestor, descendant);

        assumes grandparent_heap_property_left_grandchild:
            HeapHasParent(heap, index) 
            && HeapHasLeftChild(heap, index) ==> 
                HasHeapProperty(heap, Parent(index), LeftChild(index));

        assumes grandparent_heap_property_right_grandchild:
            HeapHasParent(heap, index) 
            && HeapHasRightChild(heap, index) ==> 
                HasHeapProperty(heap, Parent(index), RightChild(index));

        // ensures HeapUpperParentCut(heap, index);

        ensures repaired_heap: 
            \forall integer ancestor, descendant;
                0 <= ancestor < descendant < HeapElementsCount(heap)
                && IsParent(ancestor, descendant) ==>
                    HasHeapProperty(heap, ancestor, descendant);            
*/
void HeapBubbleDown(Heap heap, int index) {
    int child;

    /*@
        loop invariant 0 <= index < HeapElementsCount(heap);

        loop invariant \forall integer ancestor, descendant;
            \at(index, Pre) <= ancestor < index
            && ancestor < descendant < HeapElementsCount(heap)
            && IsParent(ancestor, descendant) ==>
                HasHeapProperty(heap, ancestor, descendant);

        loop invariant HeapLowerParentCut(heap, index);

        loop invariant
            HeapHasParent(heap, index)
            && \at(index, Pre) <= Parent(index) ==> 
                \forall integer ancestor, descendant;        
                    Parent(index) <= ancestor < index
                    && ancestor < descendant < HeapElementsCount(heap)
                    && IsParent(ancestor, descendant) ==>
                        HasHeapProperty(heap, ancestor, descendant);            
        
        loop invariant grandparent_heap_property_left_grandchild:
            HeapHasParent(heap, index)
            && \at(index, Pre) <= Parent(index)
            && HeapHasLeftChild(heap, index) ==> 
                HasHeapProperty(heap, Parent(index), LeftChild(index));            

        loop invariant grandparent_heap_property_right_grandchild:
            HeapHasParent(heap, index)
            && \at(index, Pre) <= Parent(index)
            && HeapHasRightChild(heap, index) ==> 
                HasHeapProperty(heap, Parent(index), RightChild(index));
        
        loop assigns index, child, HeapElements(heap)[0 .. HeapElementsCount(heap) - 1];

        for full_repair:
            loop invariant HeapUpperParentCut(heap, index);

            loop invariant 
                HeapHasParent(heap, index) ==> 
                    \forall integer ancestor, descendant;        
                        Parent(index) <= ancestor < index
                        && ancestor < descendant < HeapElementsCount(heap)
                        && IsParent(ancestor, descendant) ==>
                            HasHeapProperty(heap, ancestor, descendant);

            loop invariant
                HeapHasParent(heap, index)
                && HeapHasLeftChild(heap, index) ==> 
                    HasHeapProperty(heap, Parent(index), LeftChild(index));

            loop invariant
                HeapHasParent(heap, index)
                && HeapHasRightChild(heap, index) ==> 
                    HasHeapProperty(heap, Parent(index), RightChild(index));
            
        loop variant HeapElementsCount(heap) - index;        
    */
    while (HeapHasChild(heap, index)) {
        child = HeapLowerChild(heap, index);

        if (heap.elements[index] <= heap.elements[child]) {
            break;
        }

        /* 
            These asserts help provers to prove these loop invariants:
            - 'grandparent_heap_property_left_grandchild'
            - 'grandparent_heap_property_right_grandchild'
        */

        //@ assert HeapHasLeftChild(heap, child) ==> HasHeapProperty(heap, child, LeftChild(child));
        //@ assert HeapHasRightChild(heap, child) ==> HasHeapProperty(heap, child, RightChild(child));

        swap(heap.elements + index, heap.elements + child);

        index = child;
    }

}

/*@
    //requires 0 < HeapElementsCount(heap);
    requires \valid(HeapElements(heap) + (0 .. HeapElementsCount(heap) - 1));
    requires \forall integer child;
                0 < child < HeapElementsCount(heap) ==> 
                    HasHeapProperty(heap, Parent(child), child);

    assigns HeapElements(heap)[0 .. HeapElementsCount(heap) - 1];

    ensures count_decrease: HeapElementsCount(\result) == HeapElementsCount(heap) - 1;
    ensures \forall integer ancestor, descendant;
        0 <= ancestor < descendant < HeapElementsCount(\result)
        && IsParent(ancestor, descendant) ==>
            HasHeapProperty(\result, ancestor, descendant);
*/
Heap HeapExtractMin(Heap heap) {
    // int last = heap.elementsCount - 1;

    // int tmp = heap.elements[0];
    // heap.elements[0] = heap.elements[last];
    // heap.elements[last] = tmp;

    // heap.elementsCount--;

    //@ assert \false;

    // if (0 < heap.elementsCount) {
    //     HeapBubbleDown(heap, 0);
    // }

    // //@ assert \false;

    return heap;
}

/*@
    requires 0 < HeapElementsCount(heap);
    // requires \valid(HeapElements(heap) + (0 .. HeapElementsCount(heap) - 1));
    requires \forall integer ancestor, descendant;
        0 <= ancestor < descendant < HeapElementsCount(heap)
        && IsParent(ancestor, descendant) ==>
            HasHeapProperty(heap, ancestor, descendant);
*/
int t(Heap heap) {
    //@ assert \false;
    return 0;
}

/*@
    requires 1 < HeapElementsCount(heap);
    // requires \valid(HeapElements(heap) + (0 .. HeapElementsCount(heap) - 1));
    requires \forall integer ancestor, descendant;
        0 <= ancestor < descendant < HeapElementsCount(heap)
        && IsParent(ancestor, descendant) ==>
            HasHeapProperty(heap, ancestor, descendant);
*/
int tt(Heap heap) {
    //@ assert \false;
    return 0;
}


/*@
    requires 0 <= elementsCount;
    requires \valid(elements + (0 .. elementsCount - 1));

    assigns elements[0 .. elementsCount - 1];

    ensures 
        \forall integer ancestor, descendant;
            0 <= ancestor < descendant < HeapElementsCount(\result)
            && IsParent(ancestor, descendant) ==>
                HasHeapProperty(\result, ancestor, descendant);
*/
Heap HeapBuild(int *elements, int elementsCount, int elementsCapacity) {
    Heap heap;
    heap.elements = elements;
    heap.elementsCount = elementsCount;
    heap.elementsCapacity = elementsCapacity;

    /*@
        loop invariant -1 <= i <= ((int)\floor(HeapElementsCount(heap) / 2)) - 1;

        loop invariant 
            \forall integer ancestor, descendant;
                i < ancestor < descendant < HeapElementsCount(heap)
                && IsParent(ancestor, descendant) ==>
                    HasHeapProperty(heap, ancestor, descendant);

        loop assigns i, HeapElements(heap)[0 .. HeapElementsCount(heap) - 1];
        loop variant i;
    */
    for (int i = ((int)floor(heap.elementsCount / 2)) - 1; i >= 0; i--) {
        HeapBubbleDown(heap, i);
    }
    
    return heap;
}