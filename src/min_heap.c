#include <stdlib.h>
#include <stdio.h>

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
    logic int * HeapElements         (Heap *heap)            = heap->elements;
    logic int   HeapElementsCount    (Heap *heap)            = heap->elementsCount;
    logic int   HeapElementsCapacity (Heap *heap)            = heap->elementsCapacity;
    logic int   HeapElementValue     (Heap *heap, integer i) = heap->elements[i];
*/

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
    predicate HasLeftChild(Heap *heap, integer index) =
        LeftChild(index) < HeapElementsCount(heap);
    
    predicate HasRightChild(Heap *heap, integer index) =
        RightChild(index) < HeapElementsCount(heap);

    predicate HasBothChildren(Heap *heap, integer index) =
        HasLeftChild(heap, index) && HasRightChild(heap, index);
*/

/*@
    predicate HasLeftChild(Heap heap, integer index) =
        LeftChild(index) < HeapElementsCount(heap);
    
    predicate HasRightChild(Heap heap, integer index) =
        RightChild(index) < HeapElementsCount(heap);

    predicate HasBothChildren(Heap heap, integer index) =
        HasLeftChild(heap, index) && HasRightChild(heap, index);
*/

/*@
    predicate IsParent(Heap heap, integer parent, integer child) =
        0 <= parent < HeapElementsCount(heap)
        && 0 < child < HeapElementsCount(heap)
        && IsParent(parent, child);
*/

// /*@
//     predicate HasHeapProperty(Heap *heap, integer parent, integer child) =
//         IsDescendant(a, Parent(child), heap)
//         && HeapElementValue(heap, ancestor) <= HeapElementValue(heap, element);
// */

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
    
    inductive IsDescendant(Heap heap, integer descendant, integer ancestor) {
        case children:
            \forall Heap heap, integer child;
                0 < child < HeapElementsCount(heap) ==>
                    IsDescendant(heap, child, Parent(child));

        case descendants:
            \forall Heap heap, integer ancestor, element;
                0 <= ancestor < element < HeapElementsCount(heap) ==>
                    IsDescendant(heap, Parent(element), ancestor) ==> 
                        IsDescendant(heap, element, ancestor);
    }


    inductive IsAncestor(integer ancestor, integer descendant, Heap *heap) {
        case left_child:
            \forall integer parent, Heap *heap;
                0 <= parent < HeapElementsCount(heap) ==>
                    HasLeftChild(heap, parent) ==>
                        IsAncestor(parent, LeftChild(parent), heap);
        
        case right_child:
            \forall integer parent, Heap *heap;
                0 <= parent < HeapElementsCount(heap) ==>
                    HasRightChild(heap, parent) ==>
                        IsAncestor(parent, RightChild(parent), heap);

        case left_descendants:
            \forall integer element, descendant, Heap *heap;
                0 <= element < LeftChild(element) < descendant < HeapElementsCount(heap) ==>
                    IsAncestor(LeftChild(element), descendant, heap) ==> 
                        IsAncestor(element, descendant, heap);
        
        case right_descendants:
            \forall integer element, descendant, Heap *heap;
                0 <= element < RightChild(element) < descendant < HeapElementsCount(heap) ==>
                    IsAncestor(RightChild(element), descendant, heap) ==> 
                        IsAncestor(element, descendant, heap);
    }

    inductive HeapValidSubtree(Heap *heap, integer index) {
        case leafs:
            \forall Heap *heap, integer leaf;
                \floor(HeapElementsCount(heap) / 2) <= leaf < HeapElementsCount(heap) ==>
                    HeapValidSubtree(heap, leaf);

        // case root:
        //     \forall Heap *heap;
        //         HeapValidSubtree(heap, 1) ==> HeapValidSubtree(heap, 0);

        case left_child_only:
            \forall Heap *heap, integer parent;
                0 <= parent < \floor(HeapElementsCount(heap) / 2) ==>
                    (
                        HasLeftChild(heap, parent) 
                        && HeapValidSubtree(heap, LeftChild(parent))
                        && HeapElementValue(heap, parent) <= HeapElementValue(heap, LeftChild(parent))
                    ) ==>
                        HeapValidSubtree(heap, parent);
        
        // case both_children:
        //     \forall Heap *heap, integer parent ;
        //         0 <= parent < HeapElementsCount(heap) ==>
        //             (
        //             HasBothChildren(heap, parent) 
        //             && HeapValidSubtree(heap, LeftChild(parent))
        //             && HeapElementValue(heap, parent) <= HeapElementValue(heap, LeftChild(parent))
        //             && HeapValidSubtree(heap, RightChild(parent))
        //             && HeapElementValue(heap, parent) <= HeapElementValue(heap, RightChild(parent))
        //             ) ==> 
        //                 HeapValidSubtree(heap, parent);
    }
*/

/*@
    predicate ValidHeapFrom(Heap *heap, integer index) = 
        \valid(heap)
        && 0 <= index < HeapElementsCount(heap)
        && \valid(HeapElements(heap) + (0 .. HeapElementsCount(heap) - 1))
        && \forall integer ancestor, element;
            index <= ancestor < element < HeapElementsCount(heap) ==>
                IsDescendant(element, ancestor, heap) ==>
                    HeapElementValue(heap, ancestor) <= HeapElementValue(heap, element);

    predicate ValidHeap(Heap *heap) =
        \valid(heap)
        && 0 < HeapElementsCount(heap)
        && \valid(HeapElements(heap) + (0 .. HeapElementsCount(heap) - 1))
        && \forall integer ancestor, element;
            0 <= ancestor < element < HeapElementsCount(heap) ==>
                IsDescendant(element, ancestor, heap) ==>
                    HeapElementValue(heap, ancestor) <= HeapElementValue(heap, element);

    predicate FilledHeap(Heap *heap) = 
        \valid(heap)
        && 0 < HeapElementsCount(heap) <= HeapElementsCapacity(heap)
        && \valid(HeapElements(heap) + (0 .. HeapElementsCapacity(heap) - 1));
        // && \forall integer ancestor, element;
        //     0 <= ancestor < element < HeapElementsCount(heap) ==>
        //         IsDescendant(element, ancestor, heap) ==>
        //             HeapElementValue(heap, ancestor) <= HeapElementValue(heap, element);
    
    // predicate FilledHeap(Heap *heap, integer defective) = 
    //     \valid(heap)
    //     && 0 < HeapElementsCount(heap) <= HeapElementsCapacity(heap)
    //     && \valid(HeapElements(heap) + (0 .. HeapElementsCapacity(heap) - 1))
    //     && \forall integer ancestor, element;
    //         (0 <= ancestor < element < HeapElementsCount(heap) && element != defective) ==>
    //             IsDescendant(element, ancestor, heap) ==>
    //                 HeapElementValue(heap, ancestor) <= HeapElementValue(heap, element);


    predicate EmptyHeap(Heap *heap) =
        \valid(heap)
        && HeapElementsCount(heap) == 0;
*/

/*@
    requires FilledHeap(heap);
    
    ensures \exists integer i;
        0 <= i < HeapElementsCount(heap) ==>
            \result == HeapElementValue(heap, i);
    
    ensures \forall integer i;
        0 <= i < HeapElementsCount(heap) ==>
            \result <= HeapElementValue(heap, i);
    
    assigns \nothing;
*/
int HeapFindMin(Heap *heap) {
    return heap->elements[0];
}

/*@
    requires 0 < child < HeapElementsCount(heap);

    assigns \nothing;

    ensures \result == Parent(child);
    ensures 0 <= \result < child;
*/
size_t HeapParent(Heap heap, int child) {
    if (child <= 0 || child >= heap.elementsCount) {
        exit(1);
    }
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

/*@
    requires \valid(HeapElements(heap) + (0 .. HeapElementsCount(heap) - 1));
    requires 0 <= index < HeapElementsCount(heap);

    requires ok: 
        \forall integer ancestor, descendant;
            0 <= ancestor < descendant < HeapElementsCount(heap)
            && descendant != index
            && IsDescendant(heap, descendant, ancestor) ==>
                HeapElementValue(heap, ancestor) <= HeapElementValue(heap, descendant);

    // requires \forall integer ancestor, descendant;
    //         0 <= ancestor < descendant < HeapElementsCount(heap)
    //         && IsDescendant(heap, descendant, ancestor) ==>
    //             HeapElementValue(heap, ancestor) <= HeapElementValue(heap, descendant);

    // requires \forall integer ancestor, descendant;
    //         0 <= ancestor < descendant <= index
    //         && IsDescendant(heap, descendant, ancestor) ==>
    //             HeapElementValue(heap, ancestor) <= HeapElementValue(heap, descendant);
    
    // requires \forall integer ancestor, descendant;
    //         index <= ancestor < descendant < HeapElementsCount(heap)
    //         && IsDescendant(heap, descendant, ancestor) ==>
    //             HeapElementValue(heap, ancestor) <= HeapElementValue(heap, descendant);

    assigns HeapElements(heap)[0 .. HeapElementsCount(heap) - 1];

    //assigns \nothing;

    ensures \forall integer ancestor, descendant;
            0 <= ancestor < descendant < HeapElementsCount(heap)
            && IsDescendant(heap, descendant, ancestor) ==>
                HeapElementValue(heap, ancestor) <= HeapElementValue(heap, descendant);
*/
void HeapBubbleUp(Heap heap, int index) {
    int parent = index;
    
    /*@
        loop invariant 0 <= parent <= index < HeapElementsCount(heap);

        loop invariant \forall integer ancestor, descendant;
            0 <= ancestor < descendant < HeapElementsCount(heap)
            && !IsDescendant(heap, descendant, ancestor)
            && IsDescendant(heap, descendant, ancestor) ==>
                HeapElementValue(heap, ancestor) <= HeapElementValue(heap, descendant);

        loop invariant \forall integer ancestor, descendant;
            index <= ancestor < descendant < HeapElementsCount(heap)
            && IsDescendant(heap, ancestor, index)
            && IsDescendant(heap, descendant, ancestor) ==>
                HeapElementValue(heap, ancestor) <= HeapElementValue(heap, descendant);

        // loop invariant \forall integer ancestor, descendant;
        //     index <= ancestor < descendant < HeapElementsCount(heap)
        //     && IsDescendant(heap, descendant, ancestor) ==>
        //         HeapElementValue(heap, ancestor) <= HeapElementValue(heap, descendant);
        
        loop assigns index, parent, HeapElements(heap)[0 .. HeapElementsCount(heap) - 1];
        loop variant index;
    */
    while (index > 0) {
        parent = HeapParent(heap, index);
        
        // heap.elements[index] = 0;
        // heap.elements[parent] = 0;

        // if (heap.elements[parent] <= heap.elements[index]) {
        //     break;
        // }

        // swap (&heap.elements[parent], &heap.elements[index]);

        index = parent;
    }
}

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
    // requires EmptyHeap(heap) || FilledHeap(heap);
    requires EmptyHeap(heap);
    ensures count_increase: HeapElementsCount{Post}(heap) == HeapElementsCount{Pre}(heap) + 1;
    ensures count_bounded:  HeapElementsCount{Post}(heap) <= HeapElementsCapacity{Post}(heap);
    ensures FilledHeap{Post}(heap);
*/
void HeapInsert(Heap *heap, int element) {
    int index = heap->elementsCount;

    if (!heap->elements) {
        heap->elementsCount = 0;
        heap->elementsCapacity = 10;
        heap->elements = (int *) malloc (10 * sizeof(int));
        if (!heap->elements) {
            exit(1);
        }
    }

    if (heap->elementsCount + 1 >= heap->elementsCapacity) {
        heap->elementsCapacity = 2 * heap->elementsCount;
        heap->elements = (int *) realloc(heap->elements, heap->elementsCapacity * sizeof(int));
        if (!heap->elements) {
            exit(1);
        }
    }

    heap->elements[index] = element;
    heap->elementsCount++;

    // HeapBubbleUp(heap, index);
}

/*@
    requires \valid(heap);
    requires index >= 0;

    assigns \nothing;

    behavior has_left_child:
        assumes LeftChild(index) < HeapElementsCount(heap);
        ensures \result == 1;

    behavior has_no_left_child:
        assumes LeftChild(index) >= HeapElementsCount(heap);
        ensures \result == 0;
    
    complete behaviors;
    disjoint behaviors;
*/
int HeapHasLeftChild(Heap *heap, int index) {
    return HeapLeftChild(index) < heap->elementsCount;
}

/*@
    requires \valid(heap);
    requires index >= 0;

    assigns \nothing;

    behavior has_right_child:
        assumes RightChild(index) < HeapElementsCount(heap);
        ensures \result == 1;

    behavior has_no_right_child:
        assumes RightChild(index) >= HeapElementsCount(heap);
        ensures \result == 0;
    
    complete behaviors;
    disjoint behaviors;
*/
int HeapHasRightChild(Heap *heap, int index) {
    return HeapRightChild(index) < heap->elementsCount;
}

/*@
    requires \valid(heap);
    requires index >= 0;

    assigns \nothing;

    behavior has_child:
        assumes LeftChild(index) < HeapElementsCount(heap) 
                || RightChild(index) < HeapElementsCount(heap);
        ensures \result == 1;

    behavior has_no_childen:
        assumes LeftChild(index) >= HeapElementsCount(heap) 
                && RightChild(index) >= HeapElementsCount(heap);
        ensures \result == 0;
    
    complete behaviors;
    disjoint behaviors;
*/
int HeapHasChild(Heap *heap, int index) {
    return HeapHasLeftChild(heap, index) || HeapHasRightChild(heap, index);
}

/*@
    requires \valid(heap);
    requires index >= 0;

    assigns \nothing;

    behavior has_both_children:
        assumes LeftChild(index) < HeapElementsCount(heap) 
                && RightChild(index) < HeapElementsCount(heap);
        ensures \result == 1;

    behavior has_less_children:
        assumes LeftChild(index) >= HeapElementsCount(heap) 
                || RightChild(index) >= HeapElementsCount(heap);
        ensures \result == 0;
    
    complete behaviors;
    disjoint behaviors;
*/
int HeapHasBothChildren(Heap *heap, int index) {
    return HeapHasLeftChild(heap, index) && HeapHasRightChild(heap, index);
}

/*@
    requires \valid(heap);
    requires index >= 0;
    requires LeftChild(index) < HeapElementsCount(heap)
             || RightChild(index) < HeapElementsCount(heap);

    assigns \nothing;

    behavior has_both_children_left_lower:
        assumes LeftChild(index) < HeapElementsCount(heap) 
                && RightChild(index) < HeapElementsCount(heap)
                && HeapElementValue(heap, LeftChild(index)) < HeapElementValue(heap, RightChild(index));
        ensures \result == LeftChild(index);

    behavior has_both_children_right_lower:
        assumes LeftChild(index) < HeapElementsCount(heap) 
                && RightChild(index) < HeapElementsCount(heap)
                && HeapElementValue(heap, RightChild(index)) < HeapElementValue(heap, LeftChild(index));
        ensures \result == RightChild(index);

    behavior has_both_children_same:
        assumes LeftChild(index) < HeapElementsCount(heap) 
                && RightChild(index) < HeapElementsCount(heap)
                && HeapElementValue(heap, LeftChild(index)) == HeapElementValue(heap, RightChild(index));
        ensures \result == LeftChild(index);

    behavior has_only_left_child:
        assumes LeftChild(index) < HeapElementsCount(heap) 
                && RightChild(index) >= HeapElementsCount(heap);
        ensures \result == LeftChild(index);

    behavior has_only_right_child:
        assumes RightChild(index) < HeapElementsCount(heap) 
                && LeftChild(index) >= HeapElementsCount(heap);
        ensures \result == RightChild(index);
    
    complete behaviors;
    disjoint behaviors;
*/
int HeapGetLowerChild(Heap *heap, int index) {
    int leftChild = HeapLeftChild(index);
    int rightChild = HeapRightChild(index);

    if (HeapHasBothChildren(heap, index)) {
        if (heap->elements[leftChild] <= heap->elements[rightChild]) {
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

/*@
    ensures EmptyHeap(\result);
*/
Heap *HeapBuild() {
    Heap *heap = (Heap *) malloc(sizeof(Heap));
    if (!heap) {
        exit(1);
    }

    heap->elements = NULL;
    heap->elementsCount = 0;
    heap->elementsCapacity = 0;
    return heap;
}

int main() {
    Heap *heap = HeapBuild();

    
    HeapInsert(heap, 3);
    // HeapInsert(heap, 2);
    // HeapInsert(heap, 1);

    /*@ assert HeapValidSubtree(heap, 0); */
    /*@ assert HeapValidSubtree(heap, 1); */
    /*@ assert HeapValidSubtree(heap, 2); */


    // HeapInsert(heap, 10);
    // HeapInsert(heap, 10);
    // HeapInsert(heap, 10);
    // HeapInsert(heap, 10);
    // HeapInsert(heap, 10);
    // HeapInsert(heap, 10);
    // HeapInsert(heap, 10);
    // HeapInsert(heap, 10);
    // HeapInsert(heap, 10);
    // HeapInsert(heap, 10);
    // HeapInsert(heap, 10);
    // HeapInsert(heap, 10);

    printf("%d\n", HeapHasLeftChild(heap, 0));
    printf("%d\n", HeapHasLeftChild(heap, 1));
    printf("%d\n", HeapHasLeftChild(heap, 2));

    while (heap->elementsCount > 0) {
        printf("%d\n", HeapFindMin(heap));
        HeapExtractMin(heap);
    }
}

/*@
  requires \valid(array + (0 .. length-1));
  assigns  array[0 .. length-1];
  ensures  \forall size_t i; 0 <= i < length ==> array[i] == 0;
*/
void reset(int* array, size_t length){ 
/*@
    loop invariant 0 <= i <= length;
    loop invariant \forall size_t j; 0 <= j < i ==> array[j] == 0;
    //loop invariant \forall size_t j; 0 <= j < i ==> array[j] == 0;
    loop assigns i, array[0 .. length-1];
    loop variant length-i;
*/
for(size_t i = 0; i < length; ++i) array[i] = 0;

}

/*@
    requires \valid(heap)
        && HeapElementsCount(heap) > 5
        && \valid(HeapElements(heap) + (0 .. HeapElementsCount(heap) - 1));
*/
void testIsDescendant(Heap *heap) {
    //@ assert IsDescendant(1, 0, heap);
    //@ assert IsDescendant(2, 0, heap);
    //@ assert IsDescendant(3, 0, heap);
    //@ assert IsDescendant(4, 0, heap);
    //@ assert IsDescendant(5, 0, heap);

    //@ assert IsDescendant(1, 0, heap);
    //@ assert IsDescendant(2, 0, heap);

    //@ assert IsDescendant(3, 1, heap);
    //@ assert IsDescendant(4, 1, heap);
    //@ assert IsDescendant(5, 2, heap);

    //@ assert !IsDescendant(1, 2, heap);
    //@ assert !IsDescendant(2, 1, heap);
    //@ assert !IsDescendant(3, 2, heap);
    //@ assert !IsDescendant(4, 2, heap);
    //@ assert !IsDescendant(5, 1, heap);
}

/*@
    requires \valid(heap)
        && HeapElementsCount(heap) > 5
        && \valid(HeapElements(heap) + (0 .. HeapElementsCount(heap) - 1));
*/
void testIsAncestor(Heap *heap) {
    //@ assert IsAncestor(0, 1, heap);
    //@ assert IsAncestor(0, 2, heap);
    //@ assert IsAncestor(0, 3, heap);
    //@ assert IsAncestor(0, 4, heap);
    //@ assert IsAncestor(0, 5, heap);

    //@ assert IsAncestor(1, 3, heap);
    //@ assert IsAncestor(1, 4, heap);

    //@ assert IsAncestor(2, 5, heap);

    //@ assert !IsAncestor(1, 5, heap);
    //@ assert !IsAncestor(2, 3, heap);
    //@ assert !IsAncestor(2, 4, heap);

    //@ assert !IsAncestor(0, 0, heap);
}

/*@
    requires \valid(heap)
        && 0 <= HeapElementsCount(heap)
        && \valid_read(HeapElements(heap) + (0 .. HeapElementsCount(heap) - 1));
    
    assigns \nothing;
*/
void testHeapTraversal(Heap *heap) {
    /*@
        loop invariant 0 <= i <= heap->elementsCount;

        loop assigns i;
        
        loop variant heap->elementsCount-i;
    */
    for (int i = 0; i < heap->elementsCount; i++) {
        printf("%d\n", heap->elements[i]);
    }
}

/*@
  requires 0 < child;
  assigns \nothing;
  ensures 0 <= \result < child;
*/
size_t test_heap_array_traversal_next(size_t child) {
    return (child - 1) / 2;
}

/*@
    requires 0 <= bound < size;
*/
void test_heap_array_traversal(size_t bound, size_t size){
    // size_t i = bound;
    /*@
        loop invariant 0 <= bound < size;
        loop assigns bound;
        loop variant bound;
    */
    while(bound > 0) {
        bound = test_heap_array_traversal_next(bound);
    }
}

/*@
  requires 0 < child;
  assigns \nothing;
  ensures \result == Parent(child);
  ensures 0 <= \result < child;
*/
size_t testHeapArrayTraversalNext(size_t child) {
    return (child - 1) / 2;
}

/*@
    requires 0 <= bound < size;
    requires \valid(arr) && \valid(arr + (0..size-1));
    assigns arr[0..size-1];
*/
void testHeapArrayTraversal(int bound, int size, int *arr){
    // size_t i = bound;
    int a = 0;
    int parent = bound;
    /*@
        loop invariant 0 <= bound < size;
        //loop invariant 0 <= parent < size;
        loop assigns bound, parent, arr[0..size-1];
        loop variant bound;
    */
    while(bound > 0) {
        parent = testHeapArrayTraversalNext(bound);
        arr[bound] = 0;
        arr[parent] = 0;
        bound = parent;
    }
}

/*@
    requires 0 <= index < heap->elementsCount;
    requires \valid(heap) 
        && \valid(&heap->elementsCount) 
        && \valid(heap->elements + (0..heap->elementsCount-1));
    assigns heap->elements[0..heap->elementsCount-1];
*/
void testHeapStructTraversalNotProvable(struct _Heap *heap, int index){
    int bound = index;
    //int size = heap->elementsCount; // Whaaat? needed variable???
    // assert 0 <= bound < size;

    int *arr = heap->elements;
    int parent = bound;
    /*@
        loop invariant 0 <= bound < (heap->elementsCount);
        //loop invariant 0 <= parent < (heap->elementsCount);
        loop assigns bound, parent, arr[0..(heap->elementsCount)-1];
        loop variant bound;
    */
    while(bound > 0) {
        parent = testHeapArrayTraversalNext(bound);
        arr[bound] = 0;
        arr[parent] = 0;
        bound = parent;
    }
}

/*@
    requires 0 <= index < heap.elementsCount;
    requires \valid(heap.elements + (0..heap.elementsCount-1));
    assigns heap.elements[0..heap.elementsCount-1];
*/
void testHeapStructTraversalProvableStack(struct _Heap heap, int index){
    int bound = index;
    //int size = heap->elementsCount; // Whaaat? needed variable???
    // assert 0 <= bound < size;

    int *arr = heap.elements;
    int parent = bound;
    /*@
        loop invariant 0 <= bound < (heap.elementsCount);
        //loop invariant 0 <= parent < (heap.elementsCount);
        loop assigns bound, parent, arr[0..(heap.elementsCount)-1];
        loop variant bound;
    */
    while(bound > 0) {
        parent = testHeapArrayTraversalNext(bound);
        arr[bound] = 0;
        arr[parent] = 0;
        bound = parent;
    }
}

/*@
    requires 0 <= index < heap->elementsCount;
    requires \valid(heap) 
        && \valid(&heap->elementsCount) 
        && \valid(heap->elements + (0..heap->elementsCount-1));
    assigns heap->elements[0..heap->elementsCount-1];
*/
void testHeapStructTraversalProvableGhost(struct _Heap *heap, int index){
    int bound = index;
    //int size = heap->elementsCount; // Whaaat? needed variable???
    // assert 0 <= bound < size;

    int *arr = heap->elements;
    int parent = bound;
    
    //@ ghost int size = heap->elementsCount;
    /*@
        loop invariant 0 <= bound < (size);
        //loop invariant 0 <= parent < (size);
        loop assigns bound, parent, arr[0..(size)-1];
        loop variant bound;
    */
    while(bound > 0) {
        parent = testHeapArrayTraversalNext(bound);
        arr[bound] = 0;
        arr[parent] = 0;
        bound = parent;
    }
}

/*@
    requires HeapElementsCount(heap) == 21;
    requires index == 20;

    requires \valid(HeapElements(heap) + (0 .. HeapElementsCount(heap) - 1));
    requires 0 <= index < HeapElementsCount(heap);

    requires broken_index:
        \forall integer ancestor, descendant;
            0 <= ancestor <= descendant < HeapElementsCount(heap)
            && descendant != index
            && IsDescendant(heap, descendant, ancestor) ==>
                HeapElementValue(heap, ancestor) <= HeapElementValue(heap, descendant);

    assigns \nothing;
*/
void testBubbleUpBrokenHeap(Heap heap, int index) {
    //@ assert IsDescendant(heap, 2, 0);
    //@ assert HeapElementValue(heap, 0) <= HeapElementValue(heap, 2);

    //@ assert IsDescendant(heap, 5, 0);
    //@ assert HeapElementValue(heap, 0) <= HeapElementValue(heap, 5);

    //@ assert IsDescendant(heap, 6, 0);
    //@ assert HeapElementValue(heap, 0) <= HeapElementValue(heap, 6);

    //@ assert IsDescendant(heap, 11, 0);
    //@ assert HeapElementValue(heap, 0) <= HeapElementValue(heap, 11);

    //@ assert IsDescendant(heap, 12, 0);
    //@ assert HeapElementValue(heap, 0) <= HeapElementValue(heap, 12);

    //@ assert IsDescendant(heap, 13, 0);
    //@ assert HeapElementValue(heap, 0) <= HeapElementValue(heap, 13);

    //@ assert IsDescendant(heap, 14, 0);
    //@ assert HeapElementValue(heap, 0) <= HeapElementValue(heap, 14);

    //@ assert IsDescendant(heap, 20, 9);
    // assert HeapElementValue(heap, 9) <= HeapElementValue(heap, 20);

    //@ assert IsDescendant(heap, 20, 4);
    // assert HeapElementValue(heap, 4) <= HeapElementValue(heap, 20);
}

/*@
    predicate Y(integer x) = 
        \exists integer y;
            -100 < y < 0 ==>
                y == -x;
*/


/*@
    requires \valid(HeapElements(heap) + (0 .. HeapElementsCount(heap) - 1));
    requires 0 < index < HeapElementsCount(heap);
    
    requires \forall integer element;
        0 < element < index ==>
            HeapElementValue(heap, Parent(element)) <= HeapElementValue(heap, element);

    requires \forall integer element;
        index < element < HeapElementsCount(heap) ==>
            HeapElementValue(heap, Parent(element)) <= HeapElementValue(heap, element);


    assigns HeapElements(heap)[0 .. HeapElementsCount(heap) - 1];

    ensures repaired_heap:
        \forall integer element;
            0 < element < HeapElementsCount(heap) ==>
                HeapElementValue(heap, Parent(element)) <= HeapElementValue(heap, element);
*/
void testBubbleUpBrokenHeapRepair2(Heap heap, int index) {
    //@ assert HasLeftChild(heap, index) ==> HeapElementValue(heap, index) <= HeapElementValue(heap, LeftChild(index));
    //@ assert HasRightChild(heap, index) ==> HeapElementValue(heap, index) <= HeapElementValue(heap, RightChild(index));

    // assert IsParent(heap, 0, 1);
    // assert IsParent(heap, 0, 2);

    // assert IsParent(heap, 1, 3);
    // assert IsParent(heap, 1, 4);
    
    // assert IsParent(heap, 2, 5);
    // assert IsParent(heap, 2, 6);

    // assert IsParent(heap, 3, 7);
    // assert IsParent(heap, 3, 8);

    // assert IsParent(heap, 4, 9);
    // assert IsParent(heap, 4, 10);

    // assert IsParent(heap, 5, 11);
    // assert IsParent(heap, 5, 12);

    // assert IsParent(heap, 6, 13);
    // assert IsParent(heap, 6, 14);

    // assert IsParent(heap, 7, 15);
    // assert IsParent(heap, 7, 16);

    // assert IsParent(heap, 8, 17);
    // assert IsParent(heap, 8, 18);

    // assert IsParent(heap, 9, 19);
    // assert IsParent(heap, 9, 20);

    // assert HeapElementValue(heap, 0) <= HeapElementValue(heap, 1);
    // assert HeapElementValue(heap, 0) <= HeapElementValue(heap, 2);

    // assert HeapElementValue(heap, 8) <= HeapElementValue(heap, 17);
    // assert HeapElementValue(heap, 8) <= HeapElementValue(heap, 18);
    

    // assert HeapElementValue(heap, 9) <= HeapElementValue(heap, 19);
    // assert HeapElementValue(heap, 9) <= HeapElementValue(heap, 20);

    // assert HeapElementValue(heap, 4) <= HeapElementValue(heap, 9);
    // assert HeapElementValue(heap, 4) <= HeapElementValue(heap, 10);

    int parent = index;
    
    /*@
        loop invariant 0 <= index < HeapElementsCount(heap);
        loop invariant 0 <= parent <= index;

        loop invariant \forall integer element;
            0 < element < index < HeapElementsCount(heap) ==>
                HeapElementValue(heap, Parent(element)) <= HeapElementValue(heap, element);

        loop invariant \forall integer element;
            0 < index < element < HeapElementsCount(heap) ==>
                HeapElementValue(heap, Parent(element)) <= HeapElementValue(heap, element);

        // ensures repaired_heap:
        //     \forall integer element;
        //         0 < element < HeapElementsCount(heap) ==>
        //             HeapElementValue(heap, Parent(element)) <= HeapElementValue(heap, element);

        loop assigns index, parent, HeapElements(heap)[0 .. HeapElementsCount(heap) - 1];
        loop variant index;
    */
    while (index > 0) {
        //@ assert HasLeftChild(heap, index) ==> HeapElementValue(heap, index) <= HeapElementValue(heap, LeftChild(index));
        //@ assert HasRightChild(heap, index) ==> HeapElementValue(heap, index) <= HeapElementValue(heap, RightChild(index));

        parent = HeapParent(heap, index);

        if (heap.elements[parent] <= heap.elements[index]) {
            //@ assert HeapElementValue(heap, parent) <= HeapElementValue(heap, index);
            //@ assert \forall integer i; 0 < i < index + 1 ==> HeapElementValue(heap, Parent(i)) <= HeapElementValue(heap, i);

            break;
        }

        /*@
        assert \forall integer element;
            0 < index < element < HeapElementsCount(heap) ==>
                HeapElementValue(heap, Parent(element)) <= HeapElementValue(heap, element);
        */

        //@ assert HeapElementValue(heap, parent) > HeapElementValue(heap, index);
        // swap (&heap.elements[parent], &heap.elements[index]);

        /*@
        assert \forall integer element;
            0 < index < element < HeapElementsCount(heap) ==>
                HeapElementValue(heap, Parent(element)) <= HeapElementValue(heap, element);
        */
        int tmp = heap.elements[index];
        /*@
        assert \forall integer element;
            0 < index < element < HeapElementsCount(heap) ==>
                HeapElementValue(heap, Parent(element)) <= HeapElementValue(heap, element);
        */
        heap.elements[parent] = heap.elements[index];
        index = parent;
        /*
        assert \forall integer element;
            0 < index < element < HeapElementsCount(heap) ==>
                HeapElementValue(heap, Parent(element)) <= HeapElementValue(heap, element);
        */
        heap.elements[parent] = tmp;
        /*@
        assert \forall integer element;
            0 < index < element < HeapElementsCount(heap) ==>
                HeapElementValue(heap, Parent(element)) <= HeapElementValue(heap, element);
        */

        //@ assert HeapElementValue(heap, parent) <= HeapElementValue(heap, index);

        /*@
        assert \forall integer element;
            0 < index < element < HeapElementsCount(heap) ==>
                HeapElementValue(heap, Parent(element)) <= HeapElementValue(heap, element);
        */

        //@ assert HasLeftChild(heap, index) ==> HeapElementValue(heap, index) <= HeapElementValue(heap, LeftChild(index));
        //@ assert HasRightChild(heap, index) ==> HeapElementValue(heap, index) <= HeapElementValue(heap, RightChild(index));

        index = parent;
    }
}