#include "map.h"

int initializeMap(Map *map, int size) {
    if (size < 0 || map == NULL) {
        return 1;
    }

    map->items = malloc(size * sizeof(Item));
    map->capacity = size;
    map->count = 0;

    if (map->items == NULL) {
        return 1;
    }

    /*@
        loop invariant 0 <= i <= map->capacity;
        loop invariant \valid(map->items + (0..map->capacity - 1));
        loop invariant \forall integer j; 0 <= j < i ==> map->items[j].existent == 0;
        loop variant map->capacity - i;
    */
    for (int i = 0; i < map->capacity; i++) {
        map->items[i].existent = 0;
    }

    /*@ ghost
        int i = 0;
        /@
            loop invariant 0 <= i <= map->capacity;
            loop invariant count(map, 0, i) == 0;
            loop variant map->capacity - i;
        @/
        while (i < map->capacity) {
            i++;
            //@ assert count(map, 0, i - 1) == 0;
            //@ assert map->items[i - 1].existent == 0 ==> count(map, i - 1, i) == 0; 
            /@ assert count(map, 0, i) == count(map, 0, i - 1) + count(map, i - 1, i) ==
                0 + count(map, i - 1, i) == 0 + 0 == 0;
            @/
        }
        //@ assert map->count == 0 == count(map, 0, map->capacity);
    
    */

    return 0;
}

void finalizeMap(Map *map) {
    if (map == NULL) {
        return ;
    }

    if (map->items == NULL) {
        return ;
    }

    free(map->items);
    map->items = NULL;
}

int addElement(Map *map, Key *key, Value *value) {
    if (map == NULL || map->items == NULL) {
        return -1;
    }


    /*@
        loop invariant 0 <= i <= map->capacity;
        loop invariant \valid(map->items + (0..map->capacity - 1));
        loop invariant \forall integer j; 0 <= j < i ==> 
            !((map->items[j].key.a == key->a && map->items[j].key.b == key->b) && map->items[j].existent == 1);
        loop invariant \forall integer j; 0 <= j < i ==> (compare_items{Pre, Here}(get_item_t{Pre}(map, i), get_item_t{Here}(map, i)) && (\at(map->items[j].existent, Pre) == \at(map->items[j].existent, Here) == 1));
        loop invariant count{Here}(map, 0, map->capacity) == count{Pre}(map, 0, map->capacity); 
        loop variant map->capacity - i;
    */

    for (int i = 0; i < map->capacity; i++) {
        if (map->items[i].key.a == key->a && map->items[i].key.b == key->b && map->items[i].existent == 1) {
            map->items[i].value.c = value->c;
            map->items[i].value.d = value->d;
            /*@ ghost
                int k = i + 1;
                /@
                    loop invariant i + 1 <= k <= map->capacity;
                    loop invariant \forall integer j; i + 1 <= j < k ==> compare_items{Pre, Here}(get_item_t{Pre}(map, j), get_item_t{Here}(map, j)) && (\at(map->items[j].existent, Pre) == \at(map->items[j].existent, Here) == 1);
                    loop variant map->capacity - k;
                @/
                while (k < map->capacity) {
                    k++;
                }
                //@ assert no_mchg{Pre, Here}(map, key);
            */
            return 1;
        }
    }

    if (map->count == map->capacity) {
        return 0;
    } else {
        /*@
            loop invariant 0 <= i <= map->capacity;
            loop invariant \valid(map->items + (0..map->capacity - 1));
            loop variant map->capacity - i;
        */
        for (int i = 0; i < map->capacity; i++) {
            //@ assert map->count < map->capacity;
            if (map->items[i].existent == 0) {
                map->items[i].key.a = key->a;
                map->items[i].key.b = key->b;
                map->items[i].value.c = value->c;
                map->items[i].value.d = value->d;
                map->items[i].existent = 1;
                map->count++;
                return 1;
            }
        }
    }
}

int removeElement(Map *map, Key *key, Value *value) {
    if (map == NULL || map->items == NULL) {
        return -1;
    }

    for (int i = 0; i < map->count; i++) {
        if (map->items[i].key.a == key->a && map->items[i].key.b == key->b) {
            if (value != NULL) {
                value->c = map->items[i].value.c;
                value->d = map->items[i].value.d;
            }

            map->items[i].key.a = map->items[map->count - 1].key.a;
            map->items[i].key.b = map->items[map->count - 1].key.b;
            map->items[i].value.c = map->items[map->count - 1].value.c;
            map->items[i].value.d = map->items[map->count - 1].value.d;
            map->items[map->count - 1].existent = 0;
            map->count--;
            return 1;
        }
    }

    return 0;
}

int getElement(Map *map, Key *key, Value *value) {
    if (map == NULL || map->items == NULL || key == NULL) {
        return -1;
    }

    Pre1:
    //@ assert map->capacity >= 0;

    /*@
        loop invariant 0 <= i <= map->capacity;
        loop invariant \valid(map->items + (0..map->capacity - 1));
        loop invariant compare_values{Pre1, Here}(value, value);
        loop invariant \forall integer j; (0 <= j < i) ==> 
            !((map->items[j].key.a == key->a && map->items[j].key.b == key->b) &&
            map->items[j].existent == 1); 
        loop variant map->capacity - i;
    */

    for (int i = 0; i < map->capacity; i++) {
        if (map->items[i].key.a == key->a && map->items[i].key.b == key->b && map->items[i].existent == 1) {

            if (value != NULL) {
                value->c = map->items[i].value.c;
                value->d = map->items[i].value.d;

                return 1;
            } else {
                return -1;
            }
        }
    }

    return 0;

}