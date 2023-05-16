#include <limits.h>

struct Key {
    int a, b;
};

struct Value {
    int c, d;
};

struct Item {
    struct Key *k;
    struct Value *v;
};

struct Queue {
    struct Item *array;
    int capacity;
    int curr_elem;
    int empty_elem;
};
/*@
    predicate is_valid_queue (struct Queue *self) = \valid(self) && self->capacity > 1 && 
        \valid(self->array + (0..self->capacity - 1)) && 0 <= self->curr_elem < self->capacity && 
        0 <= self->empty_elem < self->capacity &&
        (\forall integer i, j; 0 <= i < j < self->capacity ==> (self->array[i].k != self->array[j].k) &&
        (self->array[i].v != self->array[j].v)) &&
        \forall integer i; 0 <= i < self->capacity ==> \valid(self->array[i].k) && \valid(self->array[i].v);

    predicate is_empty_queue (struct Queue *self) = self->curr_elem == self->empty_elem;

/// Не проверен, возможны изменения
    logic integer queue_size (struct Queue *self) = self->empty_elem >= self->curr_elem ? 
        self->empty_elem - self->curr_elem : self->capacity + self->empty_elem - self->curr_elem;

    ///logic integer get_item (struct Queue *self, integer item_number) = self->array[(self->curr_elem + item_number) % self->capacity];
    logic struct Item* get_item (struct Queue *self, integer item_number) = self->curr_elem + item_number < self->capacity ?
         &self->array[self->curr_elem + item_number] : &self->array[self->curr_elem + item_number - self->capacity];

    predicate compare_keys{L1, L2} (struct Key *i1, struct Key *i2) = (\at(i1->a, L1) == \at(i2->a, L2)) && 
        (\at(i1->b, L1) == \at(i2->b, L2));

    predicate compare_values{L1, L2} (struct Value *i1, struct Value *i2) = (\at(i1->c, L1) == \at(i2->c, L2)) && 
        (\at(i1->d, L1) == \at(i2->d, L2));
    
    predicate compare_items{L1, L2} (struct Item *i1, struct Item *i2) = compare_keys{L1, L2}(\at(i1->k, L1), \at(i2->k, L2)) && 
        compare_values{L1, L2}(\at(i1->v, L1), \at(i2->v, L2));

    predicate same_items{L1, L2} (struct Queue *self, integer begin, integer size) = 
        \forall integer k;
            begin <= k < begin + size ==> compare_items{L1, L2}(get_item{L1}(self, k), get_item{L2}(self, k));

    ///predicate is_full_queue (struct Queue *self) = (self->empty_elem + 1) % self->capacity == self->curr_elem;
    predicate is_full_queue (struct Queue *self) = self->empty_elem + 1 < self->capacity ? 
        self->empty_elem + 1 == self->curr_elem :
        self->empty_elem + 1 - self->capacity == self->curr_elem;
*/


/*@
    requires \valid(self);
    requires max_size > 0;

    assigns *self;

    allocates self->array;
    allocates self->array[..].k;
    allocates self->array[..].v;

//   ensures \result == 0 ==> \offset_min(self->array) == 0;
    ensures \result == 0 ==> \freeable(self->array);
    ensures \result == 0 ==> \forall integer i; 0 <= i < self->capacity ==> \freeable(self->array[i].k) && \freeable(self->array[i].k); 
//   ensures \result == 0 ==> \offset_min{Pre}(self->array) > \offset_max{Pre}(self->array);
    ensures \result == 0 ==> \allocable{Pre}(self->array);
    ensures \result == 0 ==> \forall integer i; 0 <= i < self->capacity ==> \allocable{Pre}(self->array[i].k) && 
        \allocable{Pre}(self->array[i].v);
    ensures \resutl == 0 ==> (\forall integer i, j; 0 <= i < j < self->capacity ==> (\base_addr(self->array[i].k) != \base_addr(self->array[j].k)) &&
        (\base_addr(self->array[i].v) != \base_addr(self->array[j].v)));
    ensures \result == 0 ==> is_valid_queue(self);
    ensures \result == 0 ==> is_empty_queue(self);
    ensures \result == 0 ==> (max_size <= INT_MAX - 1) && self->capacity == max_size + 1;
*/

int q_init(struct Queue *self, int max_size);

/*@
    requires \valid(self);
    requires \freeable(self->array);
    requires \forall integer i; 0 <= i < self->capacity ==> \freeable(self->array[i].k) && \freeable(self->array[i].k);
    requires \forall integer i, j; 0 <= i < j < self->capacity ==> (\base_addr(self->array[i].k) != \base_addr(self->array[j].k)) &&
        (\base_addr(self->array[i].v) != \base_addr(self->array[j].v));
    requires is_valid_queue(self);

    assigns *self;

    frees self->array;
    frees self->array[..].k;
    frees self->array[..].v;

    ensures \allocable(\at(self->array, Old));
    ensures \forall integer i; 0 <= i < self->capacity ==> \allocable(\at(self->array[i].k, Old)) && 
        \allocable(\at(self->array[i].v, Old));
*/

void q_clear(struct Queue *self);

/*@
    requires \valid(self);
    requires is_valid_queue(self);
    requires \valid(elem);

    assigns self->curr_elem;
    assigns self->empty_elem;
    assigns *self->array[0..self->capacity - 1].k;
    assigns *self->array[0..self->capacity - 1].v;

    allocates \nothing;

    ensures \result == 0 ==> !is_full_queue{Old}(self);
    ensures is_valid_queue(self);
    ensures same_items{Old, Here}(self, 0, queue_size{Old}(self));
    ensures \result != 0 ==> queue_size{Old}(self) == queue_size(self);
    ensures \result == 0 ==> compare_items{Here, Here}(get_item(self, queue_size{Old}(self)) ,elem);
    ensures \result == 0 ==> queue_size{Old}(self) + 1 == queue_size(self);
*/

int q_add(struct Queue *self, struct Item *elem);

/*@
    requires \valid(self);
    requires is_valid_queue(self);
    requires elem == \null || \valid(elem);

    assigns self->curr_elem;
    assigns self->empty_elem;
    assigns *self->array[0..self->capacity - 1].k;
    assigns *self->array[0..self->capacity - 1].v;
    assign *elem;

    allocates \nothing;

    ensures \result == 0 ==> !is_empty_queue{Old}(self);
    ensures is_valid_queue(self);
    ensures same_items{Old, Here}(self, 0, queue_size{Here}(self));
    ensures \result != 0 ==> queue_size{Old}(self) == queue_size(self);
    ensures \result != 0 && \valid(elem) ==> compare_items{Old, Here}(elem, elem);
    ensures \result == 0 && \valid(elem) ==> compare_items{Here, Here}(get_item{Old}(self, queue_size(self)), elem);
    ensures \result == 0 ==> queue_size{Old}(self) - 1 == queue_size(self);
*/

int q_remove(struct Queue *self, struct Item *elem);

/*@
    requires \valid(self);
    requires is_valid_queue(self);

    assigns \nothing;

    allocates \nothing;

    ensures \result <==> is_empty_queue(self);
*/

int q_is_empty(struct Queue *self);