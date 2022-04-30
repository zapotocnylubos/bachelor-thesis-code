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
    predicate HeapHasParent(Heap heap, integer index) =
        0 <= Parent(index) < HeapElementsCount(heap);

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
    predicate HasHeapProperty(Heap heap, integer parent, integer child) = 
        HeapElementValue(heap, parent) <= HeapElementValue(heap, child);

    predicate ValidHeap(Heap heap) =
        \forall integer ancestor, descendant;
            0 <= ancestor < descendant < HeapElementsCount(heap)
            && IsParent(ancestor, descendant) ==>
                HasHeapProperty(heap, ancestor, descendant);
*/


/*@
    requires \valid(a);
    requires \valid(b);

    assigns *a, *b;
    
    ensures *a == \old(*b);
    ensures *b == \old(*a);
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
        if (heap.elements[leftChild] <= heap.elements[rightChild]) {
            return leftChild;
        }

        return rightChild;
    }

    return leftChild;
}

/*@ 
    predicate HeapChildCut(Heap heap, integer index) =
        \forall integer parent, child;
            0 <= parent < child < HeapElementsCount(heap)
            && child != index
            && IsParent(parent, child) ==>
                HeapElementValue(heap, parent) <= HeapElementValue(heap, child);

        // \forall integer ancestor, descendant;
        //     0 <= ancestor < descendant < HeapElementsCount(heap)
        //     && descendant != index
        //     && IsParent(ancestor, descendant) ==>
        //         HasHeapProperty(heap, ancestor, descendant);

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
    requires HeapChildCut(heap, index);
    // requires HeapUpperChildCut(heap, index);
    // requires HeapLowerChildCut(heap, index);

    // requires heap_cut_valid_heap_property_left_child:
    //     HeapHasParent(heap, index)
    //     && IsLeftChild(index, Parent(index))
    //     && HeapHasRightChild(heap, index) ==> 
    //         HasHeapProperty(heap, Parent(index), RightChild(index));

    // requires heap_cut_valid_heap_property_right_child:
    //     HeapHasParent(heap, index) 
    //     && IsRightChild(index, Parent(index)) ==> 
    //         HasHeapProperty(heap, Parent(index), LeftChild(index));

    assigns HeapElements(heap)[0 .. HeapElementsCount(heap) - 1];

    ensures ValidHeap(heap);
*/
void HeapBubbleUp(Heap heap, int index) {
    int parent;
    
    /*@
        loop invariant 0 <= index < HeapElementsCount(heap);
        loop invariant HeapChildCut(heap, index);

        // loop invariant HeapUpperChildCut(heap, index);
        // loop invariant HeapLowerChildCut(heap, index);

        // loop invariant 
        //     HeapHasParent(heap, index)
        //     && IsLeftChild(index, Parent(index))
        //     && HeapHasRightChild(heap, index) ==> 
        //         HasHeapProperty(heap, Parent(index), RightChild(index));

        // loop invariant
        //     HeapHasParent(heap, index) 
        //     && IsRightChild(index, Parent(index)) ==> 
        //         HasHeapProperty(heap, Parent(index), LeftChild(index));

        // loop invariant heap_cut_valid_heap_property_left_child:
        //     HeapHasParent(heap, index)
        //     && HeapHasLeftChild(heap, index) ==> 
        //         HasHeapProperty(heap, Parent(index), LeftChild(index));

        // loop invariant heap_cut_valid_heap_property_right_child:
        //     HeapHasParent(heap, index)
        //     && HeapHasRightChild(heap, index) ==> 
        //         HasHeapProperty(heap, Parent(index), RightChild(index));

        loop assigns index, parent, HeapElements(heap)[0 .. HeapElementsCount(heap) - 1];
        
        loop variant index;
    */
    while (HeapHasParent(heap, index)) {
        parent = HeapParent(index);

        if (heap.elements[parent] <= heap.elements[index]) {
            break;
        }

        /* assert HeapHasParent(heap, index)
            && IsLeftChild(index, Parent(index))
            && HeapHasRightChild(heap, index) ==> 
                HasHeapProperty(heap, Parent(index), RightChild(index));
        */

        /* assert HeapHasParent(heap, index) 
            && IsRightChild(index, Parent(index)) ==> 
                HasHeapProperty(heap, Parent(index), LeftChild(index));
        */

        // assert index == LeftChild(parent) && HeapHasRightChild(heap, index) ==> HasHeapProperty(heap, parent, RightChild(parent));
        // assert index == RightChild(parent) ==> HasHeapProperty(heap, parent, LeftChild(parent));

        // assert HeapHasLeftChild(heap, parent) ==> HasHeapProperty(heap, index, LeftChild(parent));
        // assert HeapHasRightChild(heap, parent) ==> HasHeapProperty(heap, index, RightChild(parent));
        
        int tmp = heap.elements[parent];
        heap.elements[parent] = heap.elements[index];
        heap.elements[index] = tmp;
        // swap(heap.elements + index, heap.elements + parent);

        // assert HeapHasLeftChild(heap, parent) ==> HasHeapProperty(heap, parent, LeftChild(parent));
        // assert HeapHasRightChild(heap, parent) ==> HasHeapProperty(heap, parent, RightChild(parent));

        // assert HeapHasParent(heap, parent) && HeapHasLeftChild(heap, parent) ==> HasHeapProperty(heap, Parent(parent), LeftChild(parent));
        // assert HeapHasParent(heap, parent) && HeapHasRightChild(heap, parent) ==> HasHeapProperty(heap, Parent(parent), RightChild(parent));

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

        assumes heap_cut_valid_heap_property_left_child:
            HeapHasParent(heap, index) 
            && HeapHasLeftChild(heap, index) ==> 
                HasHeapProperty(heap, Parent(index), LeftChild(index));

        assumes heap_cut_valid_heap_property_right_child:
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

        loop invariant partial_heap_cut_valid_heap_property_left_child:
            HeapHasParent(heap, index)
            && \at(index, Pre) <= Parent(index)
            && HeapHasLeftChild(heap, index) ==> 
                HasHeapProperty(heap, Parent(index), LeftChild(index));            

        loop invariant partial_heap_cut_valid_heap_property_right_child:
            HeapHasParent(heap, index)
            && \at(index, Pre) <= Parent(index)
            && HeapHasRightChild(heap, index) ==> 
                HasHeapProperty(heap, Parent(index), RightChild(index));
        
        loop assigns index, child, HeapElements(heap)[0 .. HeapElementsCount(heap) - 1];

        for full_repair:
            loop invariant HeapUpperParentCut(heap, index);

            loop invariant heap_cut_valid_heap_property_left_child:
                HeapHasParent(heap, index)
                && HeapHasLeftChild(heap, index) ==> 
                    HasHeapProperty(heap, Parent(index), LeftChild(index));

            loop invariant heap_cut_valid_heap_property_right_child:
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
            - '[partial_]heap_cut_valid_heap_property_left_child'
            - '[partial_]heap_cut_valid_heap_property_right_child'
        */

        //@ assert HeapHasLeftChild(heap, child) ==> HasHeapProperty(heap, child, LeftChild(child));
        //@ assert HeapHasRightChild(heap, child) ==> HasHeapProperty(heap, child, RightChild(child));

        swap(heap.elements + index, heap.elements + child);

        index = child;
    }
}

/*@
    requires 0 < HeapElementsCount(heap);
    requires \valid(HeapElements(heap) + (0 .. HeapElementsCount(heap) - 1));
    requires ValidHeap(heap);

    assigns HeapElements(heap)[0 .. HeapElementsCount(heap) - 1];

    ensures count_decrease: HeapElementsCount(\result) == HeapElementsCount(heap) - 1;
    ensures ValidHeap(\result);
*/
Heap HeapExtractMin(Heap heap) {
    int last = heap.elementsCount - 1;

    int tmp = heap.elements[0];
    heap.elements[0] = heap.elements[last];
    heap.elements[last] = tmp;

    heap.elementsCount--;

    if (0 < heap.elementsCount) {
        HeapBubbleDown(heap, 0);
    }

    return heap;
}

/*@
    requires 0 <= elementsCount <= elementsCapacity;
    requires \valid(elements + (0 .. elementsCount - 1));

    assigns elements[0 .. elementsCount - 1];

    ensures ValidHeap(\result);
*/
Heap HeapBuild(int *elements, int elementsCount, int elementsCapacity) {
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
    for (int index = ((int)floor(heap.elementsCount / 2)) - 1; index >= 0; index--) {
        HeapBubbleDown(heap, index);
    }
    
    return heap;
}

// void printHeap(Heap heap) {
//     printf("P:\t");
//     for(int i = 0; i < heap.elementsCount; i++) {
//         printf("%d ", heap.elements[i]);
//     }
//     printf("\n");
// }

// int main() {
//     int arr[5] = {2, 3, 5, 1, 4};
//     Heap heap = HeapBuild(arr, 5, 5);
//     printHeap(heap);
    
//     printf("%d\n", heap.elements[0]);
//     heap = HeapExtractMin(heap);
//     printHeap(heap);

//     printf("%d\n", heap.elements[0]);
//     heap = HeapExtractMin(heap);
//     printHeap(heap);

//     printf("%d\n", heap.elements[0]);
//     heap = HeapExtractMin(heap);
//     printHeap(heap);

//     printf("%d\n", heap.elements[0]);
//     heap = HeapExtractMin(heap);
//     printHeap(heap);

//     printf("%d\n", heap.elements[0]);
//     heap = HeapExtractMin(heap);
//     printHeap(heap);
// }




/*@
predicate testBU4(Heap heap, integer index) = 
    \forall integer parent, child;
        0 <= parent < child < HeapElementsCount(heap)
            && child != index
            && IsParent(parent, child) ==>
                HeapElementValue(heap, parent) <= HeapElementValue(heap, child);
*/

/*@
    requires \valid(HeapElements(heap) + (0 .. HeapElementsCount(heap) - 1));
    requires 0 <= index < HeapElementsCount(heap);
    
    requires testBU4(heap, index);

    assigns HeapElements(heap)[0 .. HeapElementsCount(heap) - 1];

    ensures same_count: HeapElementsCount(\result) == HeapElementsCount(heap);
    ensures repaired_heap:
        \forall integer parent, child;
            0 <= parent < child < HeapElementsCount(\result) ==>
                IsParent(parent, child) ==>
                    HeapElementValue(\result, parent) <= HeapElementValue(\result, child);
*/
Heap testBubbleUpBrokenHeapRepair4(Heap heap, int index) {
    int parent;
    
    /*@
        loop invariant 0 <= index < HeapElementsCount(heap);
        loop invariant testBU4(heap, index);
        loop assigns index, parent, HeapElements(heap)[0 .. HeapElementsCount(heap) - 1];
        loop variant index;
    */
    while (0 < index) {
        parent = HeapParent(index);
        if (heap.elements[parent] <= heap.elements[index]) {
            break;
        }
        int tmp = heap.elements[index];
        heap.elements[parent] = heap.elements[index];
        heap.elements[parent] = tmp;

        index = parent;
    }

    //@ assert \false;

    return heap;
}