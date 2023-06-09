#ifndef __MAP_H__
#define __MAP_H__

#include "maptypes.h"
#include <stdlib.h>
#include <limits.h>

/*
    Вариант А

    Формальная спецификация

    Для типов данных:

        a) Формальная спецификация структуры Map:

        a1) Структура может хранить лишь единственное отображение для конкретного ключа (нет одинаковых ключей).
        a2) map->items структуры Map представляет собой массив длины map->capacity.
        a3) map->count == количеству элементов items с полем existent == 1.
        a4) При работе со структурой учитываются те и только те записи массива items,
            которые имеют поле item->existent установленным в истину (item->existent == 1).
        a5) 0 <= map->count <= map->capacity – количество "занятых" отображений меньше размера массива этих отображений
        a6) Отображения в map->items могут храниться с пропусками; При этом за двумя последовательно идущими элементами,
            у которых item->existent установлено в ложь, остальные элементы тоже имеют item->existent установленным в ложь
        a7) Элементы map->items хранятся с начала массива.

        b) Формальная спецификация структуры Item:

        // (b0 Item – структура, содержащая поле existent и пару значений: структуры Key и Value)
        b1) Поле existent может принимать значения 0 или 1 (false или true соответственно).
        b2) При item->existent == 0 содержимое остальных полей не учитывается при работе с структурой Map

        c) Формальная спецификация структуры Key:

        c1) Есть два поля размера int: key->a и key->b

        d) Формальная спецификация структуры Value:

        d1) Есть два поля размера int: value->c и value->d

    Для функций(initializeMap, addElement, getElement):

    A, initializeMap:
        A1) initializeMap иницализирует валидную структуру по указателю.
        A2) на вход функции подаётся валидный указатель на перемунную-структуру и размер.
        A3) size >= 0.
        A4) если результат работы равен нулю, то map->items аллоцируется на размер size * sizeof(Item).
        A5) если результат работы равен нулю, то map->capacity = size.
        A6) если результат работы равен нулю, то map->count = 0.
        A7) если результат работы равен нулю, то map->items[0..map->capacity - 1].existent = 0.
        A8) функция может аллоцировать map->items.
        
    B, addElement: // сильно поменял
        B1) addElement имеет право изменять map->items и map->count;
        B2) функция принимает валидные указатели на Map, Key, Value.
        B3) map должен удовлетворять формальной спецификации структуры Map.
        B4) функция ничего не аллоцирует и ничего не освобождает.
        B5) функция не меняет значения по указателям key и value.
        B6) функция возвращает единицу, если в результирующем map-е существует отображение (key, value) - 
            либо в map-е было отображение (key, не поданное value) и count не изменяется, 
            либо в map-e было достаточно места для добавления нового отображения (key, value) и 
            count увеличивается на 1.
        //B7) функция не меняет существующие отображения
        B7) if count{Pre} == capacity ==> result == 0 и ключа не было :) // TODO: переписать

        B8) все предыдущие отображения (items равны) существуют в результирующем map-е (кроме случая key был в map)
        B9) если \result == 1 в массиве точно есть key/value как данные
        //B9) подаваемый map должен быть валидным.
        B10) результирующий map должен удовлетворять формальной спецификации структуры Map.
        B11) map->capacity не изменяется.
        B12) если функция возвращает ноль, то в результирующем отображении не существует добавляемого отображения.

     C, getElement:

        C1) Функция getElement возвращает по указателю value сохранённое в ассоциативном массиве map значение для заданного ключа key
        C2) и возвращает истину (единицу), если заданный ассоциативный массив имеет отображения для заданного ключа.
        C3) В случае, если значение по заданному ключу не содержится в отображении, возвращается ложь (ноль) и ничего другого не происходит.
        C4) Функция не меняет ассоциативный массив
        // все существовавшие отображения остаются в массиве
        C5) и переданный ключ.
        // key не перетирается и не меняется
        C6) map->capacity не меняется
        C7) map->count не меняется
        С8) map остается валидным
        C9) Переданные в функцию значения – валидные (map валидный, key валидный, value – указатель на валидную память), остаются валидными
        // ничего другого функция не делает
        С10) Функции передается на вход валидный map,
        C11) Ничего не выделяет
        С12) ничего не освобождает


*/

/*@ axiomatic MapCount {
    logic integer count{L}(Map *map, integer m, integer n);

    axiom count_zero: \forall Map *map, integer m, n; m >= n ==>
        count(map, m, n) == 0;

    predicate count_one_p{L}(Map *map, integer m, integer n) =
      (n == m + 1) ==>
        count(map, m, n) == (map->items[m].existent ? 1 : 0);

    axiom count_one{L}: \forall Map *map, integer m; count_one_p(map, m, m + 1);

    predicate count_split_p{L}(Map *map, integer m, integer n, integer k) =
        count(map, m, k) == count(map, m, n) + count(map, n, k);

    axiom count_split{L}: \forall Map *map, integer m, n, k; m <= n <= k ==>
        count_split_p(map, m, n, k);

    logic integer count_exist(Map *map) = count(map, 0, map->capacity); // посчитать все existent в Map

}*/

/*@ axiomatic CountLem {
    lemma l_count_split:
        \forall Map *map, integer i;
            (is_valid_map(map) && (0 < i < map->capacity)) ==>
                (count(map, 0, i) == 
                    count(map, 0, i - 1) + count(map, i - 1, i));

    lemma l_count_split2:
        \forall Map *map, integer i, j;
            (is_valid_map(map) && (0 < i < j) && (j < map->capacity)) ==>
                (count(map, 0, j) == 
                    count(map, 0, i) + count(map, i, j));
    
    lemma l_count_one_p:
        \forall Map *map, integer i;
            is_valid_map(map) ==>
            (
                (count_one_p(map, i, i + 1)) && 
                    (count(map, i, (i + 1)) ==
                        (
                            map->items[i].existent ? 1 : 0
                        )
                    )
            ); 
}*/

/*@

    predicate is_valid_map_mem (Map *map) =
        \valid(map) &&
        \offset_max(map->items) == map->capacity - 1 &&
        //!\valid(map->items + map->capacity) && // проверка а2
        \valid(map->items + (0..map->capacity - 1)); // check map ptr is valid + map->items mem is valid

    predicate is_valid_map_sizes (Map *map) =
        0 <= map->count <= map->capacity; // проверка a5

    predicate begin_ok (Map *map) =
        map->count > 0 ==> map->items[0].existent == 1; // проверка a7

    predicate is_valid_item (Map *map, integer idx) =
        (0 <= idx < map->capacity) ==>
        (0 <= map->items[idx].existent <= 1); // проверка b2, c1, d1

    predicate count_ok (Map *map) =
        count_exist(map) == map->count; // проверка a3

    predicate gap_ok(Map *map) =
        \forall integer i, j;
        ((i + 1 < j < map->capacity) &&
        (0 <= i < map->capacity - 1)) &&
        ((map->items[i].existent == 0) &&
        (map->items[i + 1].existent == 0)) ==>
            map->items[j].existent == 0;  // проверка a6
            // (следующий элемент после двух пропусков: existent == 0)

    predicate is_valid_items (Map *map) =
        \forall integer i; 0 <= i < map->capacity ==> // проверка a4
        is_valid_item(map, i);

    predicate compare_keys{L1, L2} (Key *k1, Key *k2) =
        (\at(k1->a, L1) == \at(k2->a, L2)) &&
        (\at(k1->b, L1) == \at(k2->b, L2));  // сравнение ключей (+ по временным меткам)

    predicate compare_values{L1, L2} (Value *v1, Value *v2) =
        (\at(v1->c, L1) == \at(v2->c, L2)) &&
        (\at(v1->d, L1) == \at(v2->d, L2)); // сравнение значений (+ по временным меткам)

    predicate compare_keys_now{L} (Key *k1, Key *k2) = compare_keys{L, L} (k1, k2);  // сравнение ключей

    predicate compare_values_now{L} (Value *v1, Value *v2) = compare_values{L, L} (v1, v2);  // сравнение значений

    predicate valid_existence (Item *it) =
        0 <= it->existent <= 1; // existence is bool, проверка b1

    predicate item_exists_t {L} (Item *it) =
        \at(it->existent, L)  == 1; // как предыдущее, только в момент времени

    logic Key* get_key_t {L} (Item *it) =
        \at(&it->key, L); // как предыдущее, только в момент времени

    logic Value* get_value_t {L} (Item *it) =
        \at(&it->value, L); // как предыдущее, только в момент времени

    logic Item* get_item_t {L} (Map *map, integer idx) =
        \at(&map->items[idx], L); // как предыдущее, только в момент времени

    predicate all_valid_existence (Map *map) =
        \forall integer i;
        0 <= i <= map->capacity ==>
            valid_existence(get_item_t(map, i)); // проверка b1

    predicate unique_keys (Map *map) =
        \forall integer i, j;
        (0 <= i < map->capacity) &&
        (map->capacity > j > i) &&
        (item_exists_t(get_item_t(map, i))) &&
        (item_exists_t(get_item_t(map, j))) ==>
            !(compare_keys_now(get_key_t(get_item_t(map, i)), get_key_t(get_item_t(map, j)))); // проверка a1

    predicate compare_items{L1, L2} (Item *i1, Item *i2) =
        compare_keys{L1, L2}(\at(&i1->key, L1), \at(&i2->key, L2)) &&
        compare_values{L1, L2}(\at(&i1->value, L1), \at(&i2->value, L2)); // сравнение значений item

    predicate count_lowers{L1, L2} (Map *map) =
        \at(map->count, L1) == \at(map->count, L2) + 1; // в L2 произошло понижение счетчика count на 1 по сравнению с L1

    predicate same_count{L1, L2} (Map *map) =
        \at(map->count, L1) == \at(map->count, L2); // count остался таким же

    predicate same_capacity{L1, L2} (Map *map) =
        \at(map->capacity, L1) == \at(map->capacity, L2); // capacity остался таким же

    predicate same_items{L1, L2} (Map *map) =
        \forall integer i;
        0 <= i < (\at(map->capacity, L2)) &&
        item_exists_t{L1}(get_item_t{L1}(map, i)) &&
        item_exists_t{L2}(get_item_t{L2}(map, i)) ==>
        compare_items{L1, L2}
            (\at(&map->items[i], L1), \at(&map->items[i], L2)); // отображения остались такими же и вообще никак не поменялись

    predicate no_mchg{L1, L2} (Map *map, Key *key) = // проверяет, что в отображении остались все значения, которые были, кроме указанного
        \forall integer i;
        (0 <= i < (\at(map->capacity, L1))) &&
        item_exists_t{L1}(get_item_t{L1}(map, i)) &&
        !compare_keys{L1, L1}(key, get_key_t{L1}(get_item_t{L1}(map, i))) ==>
            (
            \exists integer j;
            (0 <= j < (\at(map->capacity, L2))) &&
            item_exists_t{L2}(get_item_t{L2}(map, j)) &&
                compare_items{L1, L2}(get_item_t{L1}(map, i), get_item_t{L2}(map, j))
            );

    predicate no_new{L1, L2} (Map *map) = // проверяет, что каждое значение из результирующего map было в исходном
        \forall integer i;
        (0 <= i < (\at(map->capacity, L2))) &&
        item_exists_t{L2}(get_item_t{L2}(map, i)) ==>
        (
            \exists integer j;
            (0 <= j <= (\at(map->capacity, L1))) &&
            item_exists_t{L1}(get_item_t{L1}(map, j)) &&
            compare_items{L1, L2} (get_item_t{L2}(map, i), get_item_t{L1}(map, j))
        );

predicate is_valid_map (Map *map) =
        (\offset_max(map->items) == map->capacity - 1) &&
        (\valid(map->items + (0..map->capacity - 1))) && 
        (0 <= map->count <= map->capacity) && 
        (map->count > 0 ==> map->items[0].existent == 1) &&
        ( 
            \forall integer i; 
                (0 <= i < map->capacity) ==> 
                    (map->items[i].existent == 0 || map->items[i].existent == 1)
        ) && 
        (count(map, 0, map->capacity) == map->count) &&
        (
            \forall integer i, j;
                (0 <= i < map->capacity) && (i < j < map->capacity) &&
                (map->items[i].existent == 1 && map->items[j].existent == 1) ==>
                    !(map->items[i].key.a == map->items[j].key.a && map->items[i].key.b == map->items[j].key.b) 
        ) &&
        (
            \forall integer i, j;
                (
                    (0 < i < j) && (j < map->capacity) &&
                    (map->items[i - 1].existent == 0) &&
                    (map->items[i].existent == 0)
                ) ==> map->items[j].existent == 0
        );

*/

/*@
    requires \valid(map); //A2
    requires size >= 0; // A3

    ensures \result == 0 ==> \offset_max(map->items) == size - 1; //A4
    ensures \result == 0 ==> \freeable(map->items); //A4
    ensures \result == 0 ==> map->capacity == size; //A5
    ensures \result == 0 ==> map->count == 0; //A6
    ensures \result == 0 ==> is_valid_map(map); //A1
    ensures \result == 0 ==> \forall integer i; 0 <= i < map->capacity ==> map->items[i].existent == 0; //A7
    ensures \result == 0 ==> \allocable{Pre}(map->items);//A4

*/

int initializeMap(Map *map, int size);

void finalizeMap(Map *map);

/*@

    requires \valid(map) && \valid(key) && \valid(value); //B2
    requires is_valid_map(map); //B3

    assigns map->items[0..map->capacity - 1]; //B1
    assigns map->count; // B6, B1

    frees \nothing; //B4, B5

    ensures 0 <= \result <= 1;
    ensures is_valid_map(map); //B10
    ensures same_capacity{Old, Post}(map); //B11
    ensures compare_keys{Pre, Post} (key, key);//B5
    ensures compare_values{Pre, Post} (value, value); // B5

    ensures \result == 1 ==> \exists integer i; (0 <= i < map->capacity) && (compare_keys{Post, Post}(
        get_key_t{Post}(get_item_t{Post}(map, i)), key
        )) && (compare_values{Post, Post}(
            get_value_t{Post}(get_item_t{Post}(map, i)), value
        )) && map->items[i].existent == 1;//B6, B9

    ensures \result == 1 ==> (\exists integer i; (0 <= i < map->capacity) && (compare_keys{Post, Post}(
        get_key_t{Post}(get_item_t{Post}(map, i)), key
        )) && map->items[i].existent == 1) ? (\at(map->count, Post) == \at(map->count, Pre)) : 
            (\at(map->count, Post) == \at(map->count, Pre) + 1); // B6


    ensures \result == 1 ==> no_mchg{Pre, Post} (map, key); //B8
    ensures \result == 0 ==> \at(map->count, Pre) == \at(map->capacity, Pre); //B7
    ensures \result == 0 ==> (\forall integer i; //B12
        (0 <= i < map->capacity) ==>
            !((map->items[i].key.a == key->a && map->items[i].key.b == key->b) && map->items[i].existent == 1)); 


*/

int addElement(Map *map, Key *key, Value *value);

int removeElement(Map *map, Key *key, Value *value);

/*@
    requires is_valid_map(map); //C10
    requires \valid(map);
    requires \valid(key); //C9
    requires \valid(value); //C9

    assigns *value; //C1

    frees \nothing; //С14

    ensures is_valid_map(map); //С8
    ensures same_capacity{Old, Post}(map); //С6
    ensures same_count{Old, Post}(map); //С7
    ensures same_items{Old, Post}(map); //С4
    ensures compare_keys{Old, Post}(key, key); //С5
    ensures \valid(key); //С9
    ensures \valid(value); //С9

    ensures 0 <= \result <= 1;

    ensures \result == 1 ==> // С2
      \exists integer i;
      (0 <= i < map->capacity) &&
        compare_keys{Here, Here}(key, get_key_t{Here}(get_item_t{Here}(map, i))) && // C2
        compare_values{Here, Here}(value, get_value_t{Here}(get_item_t{Here}(map, i))) &&
        map->items[i].existent == 1; //С1

    ensures \result == 0 ==> // С3
      compare_values{Old, Post}(value, value) && 
      (\forall integer i;
        (0 <= i < map->capacity) ==>
            !((map->items[i].key.a == key->a && map->items[i].key.b == key->b) && map->items[i].existent == 1)); 

  */

int getElement(Map *map, Key *key, Value *value);

#endif // __MAP_H__