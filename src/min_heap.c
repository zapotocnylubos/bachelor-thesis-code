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
    predicate HasLeftChild(Heap *heap, integer index) =
        LeftChild(index) < HeapElementsCount(heap);
    
    predicate HasRightChild(Heap *heap, integer index) =
        RightChild(index) < HeapElementsCount(heap);

    predicate HasBothChildren(Heap *heap, integer index) =
        HasLeftChild(heap, index) && HasRightChild(heap, index);
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
    requires \valid(heap) && 0 < HeapElementsCount(heap);
    requires 0 < child < HeapElementsCount(heap);

    assigns \nothing;

    ensures \result == Parent(child);
    ensures 0 <= \result < HeapElementsCount(heap);
*/
int HeapParent(Heap *heap, int child) {
    if (child <= 0 || child >= heap->elementsCount) {
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
    requires \valid(heap)
        && 0 < HeapElementsCount(heap)
        && \valid(HeapElements(heap) + (0 .. HeapElementsCount(heap) - 1));

    requires 0 <= index < HeapElementsCount(heap);
    
    requires \forall integer ancestor, descendant;
            0 <= ancestor < descendant < index
            && IsDescendant(ancestor, descendant, heap) ==>
                HeapElementValue(heap, ancestor) <= HeapElementValue(heap, descendant);
    
    requires \forall integer ancestor, descendant;
            index < ancestor < descendant < HeapElementsCount(heap)
            && IsDescendant(ancestor, descendant, heap) ==>
                HeapElementValue(heap, ancestor) <= HeapElementValue(heap, descendant);


    assigns HeapElements(heap)[0 .. HeapElementsCount(heap) - 1];

    ensures \forall integer ancestor, descendant;
            0 <= ancestor < descendant < HeapElementsCount(heap)
            && IsDescendant(ancestor, descendant, heap) ==>
                HeapElementValue(heap, ancestor) <= HeapElementValue(heap, descendant);
*/
void HeapBubbleUp(Heap *heap, int index) {
    //@ assert \valid(HeapElements(heap) + (0 .. HeapElementsCount(heap)-1));
    if (!heap->elementsCount) {
        exit(1);
    }
    //@ assert \valid(HeapElements(heap) + (0 .. HeapElementsCount(heap)-1));

    // if (index == 0) {
    //     return;
    // }

    /*@
        //loop invariant 0 <= index <= HeapElementsCount(heap);

        // loop invariant \forall integer ancestor, descendant;
        //     0 <= ancestor < descendant < index
        //     && IsDescendant(ancestor, descendant, heap) ==>
        //         HeapElementValue(heap, ancestor) <= HeapElementValue(heap, descendant);

        // loop invariant \forall integer ancestor, descendant;
        //     index < ancestor < descendant < HeapElementsCount(heap)
        //     && IsDescendant(ancestor, descendant, heap) ==>
        //         HeapElementValue(heap, ancestor) <= HeapElementValue(heap, descendant);
        
        // loop invariant index > 0 ==> 0 <= Parent(index) < HeapElementsCount(heap);

        loop assigns index, HeapElements(heap)[0 .. HeapElementsCount(heap) - 1];
        // loop   variant index;
    */
    while (index > 0) {
        //@ assert \valid(HeapElements(heap) + (0 .. HeapElementsCount(heap)-1));
        //@ assert 0 <= index < HeapElementsCount(heap);
        int parent = HeapParent(heap, index);
        //@ assert 0 <= index < HeapElementsCount(heap);
        //@ assert 0 <= parent <= index < HeapElementsCount(heap);
        //@ assert 0 <= parent < HeapElementsCount(heap);
        // assert \valid(HeapElements(heap) + (0 .. HeapElementsCount(heap)-1));

        if (heap->elements[parent] <= heap->elements[index]){
            break;
        }

        int tmp = heap->elements[parent];
        heap->elements[parent] = heap->elements[index];
        heap->elements[index] = tmp;

    // HeapBubbleUp(heap, parent);
        index = parent;
    }
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
  requires \valid_read(a + (beg .. end-1));
  requires beg < end;
  assigns  \nothing;
*/
size_t min_idx_in(int* a, size_t beg, size_t end){
    size_t min_i = beg;
    /*@
        loop invariant beg <= min_i < i <= end;
        loop assigns min_i, i;
        loop variant end-i;
    */
    for(size_t i = beg+1; i < end; ++i){
        if(a[i] < a[min_i]) min_i = i; 
    }
    
    return min_i; 
}

/*@
  requires \valid_read(a + (beg .. end-1));
  requires beg < end;
  assigns  \nothing;
*/
size_t min_idx_in2(int* a, size_t beg, size_t end){
    size_t min_i = end-1;
    /*@
        loop invariant (beg - 1) <= i < min_i <= end - 1;
        loop assigns min_i, i;
        loop variant (i-1) - beg;
    */
    for(size_t i = end-1-1; i >= beg; --i){
        if(a[i] < a[min_i]) min_i = i; 
    }
    
    return min_i; 
}

/*@
  requires \valid(p) && \valid(q);
  assigns  *p, *q;
  ensures  *p == \old(*q) && *q == \old(*p);
*/
void swap(int* p, int* q){
int tmp = *p; *p = *q; *q = tmp; }


/*@
 requires \valid(v+(0..n-1));
 requires n > 0;
 assigns v[0..n-1];
 ensures \forall integer q; 0<=q<=n-1 ==> v[q]==(unsigned char)0;
*/
static void make_zero( unsigned char *v, size_t n ) {

  unsigned char *p = (unsigned char*)v;

  /*@
    loop invariant 0 <= n <= \at(n, Pre);
    //loop invariant p == v+(\at(n, Pre)-n);
    //loop invariant \forall integer j;  0 <= j < (\at(n, Pre)-n) ==> v[j] == (unsigned char)0;
    //loop assigns n, p, v[0..\at(n, Pre)-n-1];
    loop variant n;
  */

  while( n-- ){
    *p++ = 0;
  }
}


/*@
  requires 0 < child;
  assigns \nothing;
  ensures 0 <= \result < child;
*/
size_t random_between(size_t child) {
    return (child - 1) / 2;
}

/*@
    requires 0 <= bound < size;
*/
void random_loop(size_t bound, size_t size){
    // size_t i = bound;
    /*@
        loop invariant 0 <= bound < size;
        loop assigns bound;
        loop variant bound;
    */
    while(bound > 0) {
        bound = random_between(bound);
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
void testHeapArrayTraversal(size_t bound, size_t size, int *arr){
    // size_t i = bound;
    int a = 0;
    /*@
        loop invariant 0 <= bound < size;
        loop assigns bound, arr[0..size-1];
        loop variant bound;
    */
    while(bound > 0) {
        bound = test_heap_array_traversal_next(bound);
        arr[bound] = 0;
    }
}