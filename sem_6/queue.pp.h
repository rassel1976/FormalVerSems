// #include <limits.h>

struct Queue {
    int *array;
    int capacity;
    int curr_elem;
    int empty_elem;
};
/*@
    predicate is_valid_queue (struct Queue *self) = \valid(self) && self->capacity > 1 && 
        \valid(self->array + (0..self->capacity - 1)) && 0 <= self->curr_elem < self->capacity && 
        0 <= self->empty_elem < self->capacity;

    predicate is_empty_queue (struct Queue *self) = self->curr_elem == self->empty_elem;

/// Не проверен, возможны изменения
    logic integer queue_size (struct Queue *self) = self->empty_elem >= self->curr_elem ? 
        self->empty_elem - self->curr_elem : self->capacity + self->empty_elem - self->curr_elem;

    ///logic integer get_item (struct Queue *self, integer item_number) = self->array[(self->curr_elem + item_number) % self->capacity];
    logic integer get_item (struct Queue *self, integer item_number) = self->curr_elem + item_number < self->capacity ?
         self->array[self->curr_elem + item_number] : self->array[self->curr_elem + item_number - self->capacity];

    predicate same_items{L1, L2} (struct Queue *self, integer begin, integer size) = 
        \forall integer k;
            begin <= k < begin + size ==> \at(get_item(self, k), L1) == \at(get_item(self, k), L2);

    ///predicate is_full_queue (struct Queue *self) = (self->empty_elem + 1) % self->capacity == self->curr_elem;
    predicate is_full_queue (struct Queue *self) = self->empty_elem + 1 < self->capacity ? 
        self->empty_elem + 1 == self->curr_elem :
        self->empty_elem + 1 - self->capacity == self->curr_elem;*/
// */


/*@
    requires \valid(self);
    requires max_size > 0;

    assigns *self;

    allocates self->array;

//   ensures \result == 0 ==> \offset_min(self->array) == 0;
    ensures \result == 0 ==> \freeable(self->array);
//   ensures \result == 0 ==> \offset_min{Pre}(self->array) > \offset_max{Pre}(self->array);
    ensures \result == 0 ==> \allocable{Pre}(self->array);
    ensures \result == 0 ==> is_valid_queue(self);
    ensures \result == 0 ==> is_empty_queue(self);
    ensures \result == 0 ==> (max_size <= 0x7fffffff - 1) && self->capacity == max_size + 1;*/
// */

int q_init(struct Queue *self, int max_size);

/*@
    requires \valid(self);
    requires \freeable(self->array);
    requires is_valid_queue(self);

    assigns *self;

    frees self->array;

    ensures \allocable(\at(self->array, Old));*/
// */

void q_clear(struct Queue *self);

/*@
    requires \valid(self);
    requires is_valid_queue(self);

    assigns *self;
    assigns self->array[0..self->capacity - 1];

    ensures \result == 0 ==> !is_full_queue{Old}(self);
    ensures \result == 0 ==> is_valid_queue(self);
    ensures \result == 0 ==> same_items{Old, Here}(self, 0, queue_size{Old}(self));
    ensures \result == 0 ==> get_item(self, queue_size{Old}(self)) == elem;
    ensures \result == 0 ==> queue_size{Old}(self) + 1 == queue_size(self);*/
// */

int q_add(struct Queue *self, int elem);

/*@
    requires \valid(self);
    requires is_valid_queue(self);
    
*/
// */

int q_remove(struct Queue *self, int *elem);

int q_is_empty(struct Queue *self);
