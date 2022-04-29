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

    predicate ValidHeap(Heap heap) =
        \forall integer parent, child;
            0 <= parent < child < HeapElementsCount(heap) ==>
                HasHeapProperty(heap, Parent(child), child);
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
        IsChild(child, parent);
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
        \forall integer parent, child;
            0 <= parent < index
            && 0 < child < HeapElementsCount(heap)
            && IsParent(parent, child) ==>
                HasHeapProperty(heap, parent, child);

    predicate HeapLowerParentCut(Heap heap, integer index) =
        \forall integer parent, child;
            index < parent < HeapElementsCount(heap)
            && 0 < child < HeapElementsCount(heap)
            && IsParent(parent, child) ==>
                HasHeapProperty(heap, parent, child);
*/

/*@
    predicate HeapCutParent(Heap heap, integer from, integer to) = 
        \forall integer parent, child;
            from <= parent < to
            && parent < child < HeapElementsCount(heap)
            && IsParent(parent, child) ==>
                HasHeapProperty(heap, parent, child);
    
    predicate HeapUpperCutParent(Heap heap, integer index) = HeapCutParent(heap, 0, index);
    predicate HeapLowerCutParent(Heap heap, integer index) = HeapCutParent(heap, index + 1, HeapElementsCount(heap));
*/

/*@
    requires \valid(HeapElements(heap) + (0 .. HeapElementsCount(heap) - 1));
    requires 0 <= index < HeapElementsCount(heap);

    requires HeapUpperParentCut(heap, index);
    requires HeapLowerParentCut(heap, index);

    requires grandparent_heap_property_left_grandchild:
        HeapHasParent(heap, index)
        && HeapHasLeftChild(heap, index) ==> 
            HasHeapProperty(heap, Parent(index), LeftChild(index));

    requires grandparent_heap_property_right_grandchild:
        HeapHasParent(heap, index)
        && HeapHasRightChild(heap, index) ==> 
            HasHeapProperty(heap, Parent(index), RightChild(index));

    assigns HeapElements(heap)[0 .. HeapElementsCount(heap) - 1];

    //ensures HeapLowerParentCut(heap, index);
    ensures partially_repaired_heap:
        \forall integer parent, child;
            0 <= parent < child < HeapElementsCount(heap)
            && IsParent(parent, child) ==>
                HasHeapProperty(heap, parent, child);

    // behavior full_repair:
    //     assumes HeapUpperParentCut(heap, index);

    //     assumes grandparent_heap_property_left_grandchild:
    //         HeapHasParent(heap, index) && HeapHasLeftChild(heap, index) ==> 
    //             HasHeapProperty(heap, Parent(index), LeftChild(index));

    //     assumes grandparent_heap_property_right_grandchild:
    //         HeapHasParent(heap, index) && HeapHasRightChild(heap, index) ==> 
    //             HasHeapProperty(heap, Parent(index), RightChild(index));

    //     ensures repaired_heap: ValidHeap(heap);            
*/
void HeapBubbleDown(Heap heap, int index) {
    int child;

    /*@
        loop invariant 0 <= index < HeapElementsCount(heap);

        loop invariant HeapUpperParentCut(heap, index);
        loop invariant HeapLowerParentCut(heap, index);

        loop invariant
            HeapHasParent(heap, index) ==> 
                \forall integer parent, child_2;        
                    Parent(index) <= parent < index
                    && parent < child_2 < HeapElementsCount(heap)
                    && IsParent(parent, child_2) ==>
                        HasHeapProperty(heap, parent, child_2);

        // loop invariant 
        //     HeapHasParent(heap, index)
        //     && HeapHasLeftChild(heap, Parent(index)) ==> 
        //         HasHeapProperty(heap, Parent(index), LeftChild(Parent(index)));

        // loop invariant 
        //     HeapHasParent(heap, index)
        //     && HeapHasRightChild(heap, Parent(index)) ==> 
        //         HasHeapProperty(heap, Parent(index), RightChild(Parent(index)));

        loop invariant grandparent_heap_property_left_grandchild:
            HeapHasParent(heap, index)
            && HeapHasLeftChild(heap, index) ==> 
                HasHeapProperty(heap, Parent(index), LeftChild(index));
        
        loop invariant grandparent_heap_property_right_grandchild:
            HeapHasParent(heap, index)
            && HeapHasRightChild(heap, index) ==> 
                HasHeapProperty(heap, Parent(index), RightChild(index));

        // for full_repair:
        //     loop invariant HeapUpperParentCut(heap, index);

        // for full_repair: 
        //     loop invariant
        //         HeapHasParent(heap, index)
        //         && HeapHasLeftChild(heap, index) ==> 
        //             HasHeapProperty(heap, Parent(index), LeftChild(index));

        // for full_repair: 
        //     loop invariant 
        //         HeapHasParent(heap, index)
        //         && HeapHasRightChild(heap, index) ==> 
        //             HasHeapProperty(heap, Parent(index), RightChild(index));

        loop assigns index, child, HeapElements(heap)[0 .. HeapElementsCount(heap) - 1];
        loop variant HeapElementsCount(heap) - index;
    */
    while (HeapHasChild(heap, index)) {
        child = HeapLowerChild(heap, index);

        if (heap.elements[index] <= heap.elements[child]) {
            break;
        }

        //@ assert HeapHasLeftChild(heap, child) ==> HasHeapProperty(heap, child, LeftChild(child));
        //@ assert HeapHasRightChild(heap, child) ==> HasHeapProperty(heap, child, RightChild(child));

        swap(heap.elements + index, heap.elements + child);

        index = child;
    }

    // assert \false;
}
