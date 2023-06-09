/***************************************
Этот модуль описывает типы данных для представления
ориентированных графов, их вершин и дуг.

Граф представлен в типе `Graph`.

Поле `vertices` описывает вершины графа. Это массив из `vsize` значений
типа `Vertex`. Тип `Vertex` описывает размещение некоторой вершины графа
в массиве `vertices`. Поле `existent` в элементе массива `vertices` с
некоторым индексом `i` равно истине (т.е. не равно 0) тогда, когда в этом
элементе размещена вершина графа. В противном случае элемент массива
`vertices` с индексом `i` считается свободным.

Поле `edges` описывает дуги графа. Это массив из `esize` значений типа `Edge`.
Тип `Edge` описывает размещение некоторой дуги графа в массиве `edges`.
Поле `existent` в элементе массива `edges` имеет тот же смысл, что и то же
поле в элементе массива `vertices`. Поля `from` и `to` должны быть индексами в
массиве `vertices` и означают вершины, из которой исходит дуга и в которую
входит дуга.

Поле `ecnt` означает то количество первых элементов массива `edges`,
после которого все остальные элементы будут свободными.

Ниже приведено определение описанных типов и предикат `valid`, формально
описывающий инвариант типа `Graph`.

В конце модуля размещена функция `add_edge`, которая добавляет дугу в граф.
Ее аргумент `g` означает граф, в который надо
добавить дугу, аргументы `f` и `t` означают индексы в массиве `g->vertices`,
означающие начало и конец добавляемой дуги. Функция применима только
к графам, в которых есть свободное место для добавления дуги.
Перед функцией размещена ее формальная спецификация на языке `ACSL`.
****************************************/


typedef struct {
    int payload;
    int existent;
} Vertex;

typedef struct {
	int from;
	int to;
	int existent;
} Edge;

typedef struct {
	Vertex *vertices;
	int vsize;
	Edge *edges;
	int ecnt;
	int esize;
} Graph;

/*@
  predicate is_vertex(Graph *g, integer v) =
  	0 <= v < g->vsize;

  predicate edge_valid(Graph *g, integer k) =
 	g->edges[k].existent ==>
	is_vertex(g, g->edges[k].from) &&
	is_vertex(g, g->edges[k].to) &&
	g->vertices[g->edges[k].from].existent &&
	g->vertices[g->edges[k].to].existent;

  predicate edges_valid(Graph *g, integer n) =
 	\forall integer k; 0 <= k < n ==> edge_valid(g, k);

  predicate graph_valid(Graph *g) =
 	g->vsize > 0 &&
    g->esize > 0 &&
    g->esize >= g->ecnt >= 0 &&
	\valid(g->vertices + (0 .. g->vsize - 1)) &&
	\valid(g->edges + (0 .. g->esize - 1)) &&
	edges_valid(g, g->ecnt) &&
	(\forall integer k; g->ecnt <= k < g->esize ==> !g->edges[k].existent);
*/

/*@ predicate full(Graph *g) = range_existent(g, 0, g->esize);
    predicate range_existent(Graph *g, integer m, integer n) = \forall integer k; m <= k < n ==> g->edges[k].existent;
*/

/*@ axiomatic EdgesCount {
    logic integer count{L}(Graph *g, integer f, integer t, integer m, integer n);

    axiom count_zero: \forall Graph *g, integer f, t, m, n; m >= n ==>
        count(g, f, t, m, n) == 0;

	predicate count_one_p{L}(Graph *g, integer f, integer t, integer m) =
        count(g, f, t, m, m + 1) == (g->edges[m].existent && g->edges[m].from == f && g->edges[m].to == t ? 1 : 0);

    axiom count_one{L}: \forall Graph *g, integer f, t, m; count_one_p(g, f, t, m);

    predicate count_split_p{L}(Graph *g, integer f, integer t, integer m, integer n, integer k) =
        count(g, f, t, m, k) == count(g, f, t, m, n) + count(g, f, t, n, k);

    axiom count_split{L}: \forall Graph *g, integer f, t, m, n, k; m <= n <= k ==>
        count_split_p(g, f, t, m, n, k);
}*/

/*@ logic integer all_count(Graph *g, integer f, integer t) = count(g, f, t, 0, g->esize); */

/*@ lemma zeros{L}:
    \forall Graph *g;\forall integer f, t, m;  graph_valid(g) && g->esize > m>= g->ecnt ==> !g->edges[m].existent;
*/
/*@ lemma count_prop{L}:
    \forall Graph *g; \forall integer f, t, m, n; m <= n ==> count(g, f, t, m, (n+1)) == count(g, f,t, m,n) + count(g,f,t,n, n+1);  
*/
/*@ lemma count_prop2{L}:
    \forall Graph *g; \forall integer f, t, m, n, z,k; z== k+1 && m <=k && z<=n ==> count(g, f, t, m, n) == count(g, f, t, m, k) +  count(g, f, t, k, z) + count(g, f, t, z, n);
*/

/*@ ghost 
    /@ lemma
        requires \valid(g);
        requires graph_valid(g);
        ensures count(g, f, t, g->ecnt, g->esize) ==0;
    @/
    void count_after(Graph *g,int f,int t, int m){
        /@ loop invariant 0 <= i <= g->esize;
           loop invariant count(g, f, t, g->ecnt, i) == 0;
           loop variant g->esize - i;
        @/
        for (int i = g->ecnt; i < g->esize; i++){

        }
        return;
    }
*/
/*@
    requires \valid(g) && graph_valid(g);
    requires is_vertex(g, f);
    requires is_vertex(g, t);
    requires g->vertices[f].existent;
    requires g->vertices[t].existent;
    ensures \result == all_count(g, f, t);
*/
int
count(Graph *g, int f, int t)
{
    int c = 0;
    /*@ loop invariant 0 <= i <= g->ecnt;
        loop invariant c == count(g, f, t, 0, i);
        loop invariant 0 <= c <= i;
        loop variant g->ecnt - i;
    */
    for (int i = 0; i < g->ecnt; ++i) {
        if (g->edges[i].existent && g->edges[i].from == f && g->edges[i].to == t) {
            ++ c;
        }
    }
 //@ assert all_count(g, f ,t) == count(g,f,t,0, g->ecnt) + count(g,f,t,g->ecnt, g->esize);
 //@ assert count(g,f,t,g->ecnt, g->esize) == 0;
    return c;
}

/*@
  requires \valid(g) && graph_valid(g);
  requires is_vertex(g, f);
  requires is_vertex(g, t);
  requires g->vertices[f].existent;
  requires g->vertices[t].existent;
  requires !full(g);
  ensures graph_valid(g);
  ensures all_count(g, f, t) == all_count{Pre}(g, f, t) + 1;
  ensures \forall integer f2, t2; (f2 != f || t2 != t) ==> all_count(g, f2, t2) == all_count{Pre}(g, f2, t2);
*/
void
add_edge(Graph *g, int f, int t)
{
    Before:
    if (g->ecnt < g->esize) {
            //@ assert \forall integer f2, t2; count{Pre}(g,f2,t2, 0, g->esize) == count{Pre}(g,f2,t2, 0, g->ecnt) + count{Pre}(g,f2,t2, g->ecnt,g->ecnt + 1) + count{Pre}(g,f2,t2, g->ecnt + 1,g->esize);
            //@assert \forall integer f2 ,t2; count{Pre}(g,f2,t2, g->ecnt, g->ecnt+1) == 0;
        g->edges[g->ecnt].from = f;
        g->edges[g->ecnt].to = t;
        g->edges[g->ecnt].existent = 1;
	    ++ g->ecnt;
        /*@ ghost
        const int r = g->ecnt -1;
        /@ loop invariant 0 <= i <= r;
           loop invariant \forall integer k; 0 <=k  < g->esize && k!= r ==> g->edges[k] == \at(g->edges[k],Pre);
           loop invariant  \forall integer f2, t2; i+1 <= r ==> count(g,f2,t2, 0, i+1) == count(g, f2,t2, 0,i) + count(g, f2,t2, i,i +1);
           loop invariant   i < r ==> g->edges[i] == \at(g->edges[\at(i, Here)], Pre);
           loop invariant  \forall integer f2, t2; i+1 <= r ==> count(g,f2,t2, i, i+1) == count{Pre}(g, f2,t2, i,i +1);
           loop invariant  \forall integer f2, t2; i+1 <= r ==> count{Pre}(g,f2,t2, 0, i+1) == count{Pre}(g, f2,t2, 0,i) + count{Pre}(g, f2,t2, i,i +1);
           loop invariant  \forall integer f2, t2; count(g,f2,t2, 0, i) == count{Pre}(g, f2,t2, 0,i);  // preserve2 в 3_1.mlw
           loop invariant graph_valid(g);
           loop assigns \nothing;
           loop variant r - i;
        @/
        for (int i = 0; i < r; i++){
    
        }
        /@ loop invariant r+1 <= i <= g->esize;
           loop invariant graph_valid(g);
           loop invariant \forall integer k; r < k  < g->esize  ==> g->edges[k] == \at(g->edges[k],Pre);
           loop invariant  \forall integer f2, t2; r+1< i+1 <= g->esize ==> count(g,f2,t2, r+1, i + 1) == count(g, f2,t2,r+1, i) + count(g, f2,t2, i, i + 1);
           loop invariant  i > r ==> g->edges[i] == \at(g->edges[\at(i, Here)], Pre);
           loop invariant  \forall integer f2, t2; i+1 <= g->esize  ==> count(g,f2,t2, i, i+1) == count{Pre}(g, f2,t2, i,i +1);
           loop invariant  \forall integer f2, t2; i+1 <= g->esize ==> count{Pre}(g,f2,t2,r+1, i+1) == count{Pre}(g, f2,t2,r+1, i) + count{Pre}(g,f2,t2,i, i+1);
           loop invariant (\forall integer f2, t2; count(g,f2,t2, r+1, i) == count{Pre}(g, f2,t2,r +1, i)); // preserve2 в 3_1.mlw
           loop assigns \nothing;
           loop variant g->esize -i;

        @/
        for (int i = r+1; i < g->esize; i++){

        }
        */
        //@ assert \forall integer f2,t2; count(g,f2,t2, 0, g->ecnt -1) == count{Pre}(g, f2,t2, 0,g->ecnt);
        //@ assert \forall integer f2,t2; count(g,f2,t2, r+1, g->esize) == count{Pre}(g, f2, t2,r+1,g->esize);
        /*@ assert \forall integer f2,t2; count(g,f2,t2, 0, g->esize) == count(g,f2,t2, 0,r) + count(g,f2,t2,r,r +1) + count(g,f2,t2, r+1 ,g->esize)==
         count{Pre}(g,f2,t2, 0, r) + count(g,f2,t2,r,r +1) + count(g,f2,t2, r+1 ,g->esize) ==
         count{Pre}(g,f2,t2, 0, r) + count(g,f2,t2,r,r +1) + count{Pre}(g,f2,t2, r+1 ,g->esize) ==
         count{Pre}(g,f2,t2, 0, r) + count{Pre}(g,f2,t2,r,r +1) + count{Pre}(g,f2,t2, r+1 ,g->esize) + count(g,f2,t2,r,r +1)  ==count{Pre}(g,f2,t2,0, r+1) +count{Pre}(g,f2,t2,r+1, g->esize) +  count(g,f2,t2,r,r +1)  ==  count{Pre}(g,f2,t2,0,g->esize) + count(g,f2,t2,r,r +1);
        */
        //@ assert \forall integer f2,t2; count(g,f2,t2, 0, g->esize) == count{Pre}(g,f2,t2, 0, g->ecnt) + count(g,f2,t2, g->ecnt -1,g->ecnt) + count{Pre}(g,f2,t2, g->ecnt+1 ,g->esize);
        //@assert \forall integer f2, t2; (f2 != f || t2 != t) ==> count(g,f2,t2, 0, g->esize) == count{Pre}(g,f2,t2, 0, g->ecnt) + count{Pre}(g,f2,t2, g->ecnt+1 ,g->esize);
        //@assert \forall integer f2, t2; (f2 != f || t2 != t) ==> count{Pre}(g,f2,t2, 0, g->esize) == count{Pre}(g,f2,t2, 0, g->ecnt) + count{Pre}(g,f2,t2, g->ecnt+1 ,g->esize) ;
        //@assert count(g,f,t, g->ecnt -1, g->ecnt) == 1;
        //@assert \forall integer f2, t2; (f2 != f || t2 != t) ==> count(g,f2,t2, g->ecnt -1, g->ecnt) == 0;
        return;
    }
    /*@ loop invariant 0 <= i <= g->ecnt;
        loop invariant graph_valid(g);
        loop invariant \forall integer  f2, t2, m, n;  count(g,f2,t2, m,n) == count{Pre}(g,f2,t2,m,n);
        loop invariant (!full(g));
        loop invariant \exists integer k; 0<=k<g->ecnt && !g->edges[k].existent;
        loop invariant \forall integer k; 0<=k < i ==> g->edges[k].existent;
        loop invariant \forall integer k; 0 <=k < g->esize ==> g->edges[k] == \at(g->edges[k], Pre);
        loop variant g->ecnt -i;
    */
    for (int i = 0; i < g->ecnt; ++i) {
       if (!g->edges[i].existent) {
            g->edges[i].from = f;
            g->edges[i].to = t;
	        g->edges[i].existent = 1;
            /*@ ghost const int r = i;
            /@ loop invariant 0 <= k <= r;
                loop invariant \forall integer p; 0 <= p  < g->esize && p != i ==> g->edges[p] == \at(g->edges[p],Pre);
                loop invariant  \forall integer f2, t2; k+1 <= r ==> count(g,f2,t2, 0, k+1) == count(g, f2,t2, 0,k) + count(g, f2,t2, k,k +1);
                loop invariant  \forall integer p; 0<= p < g->esize && p!= r ==> g->edges[p] == \at(g->edges[\at(p, Here)], Pre);
                loop invariant  k < r ==> g->edges[k] == \at(g->edges[\at(k, Here)], Pre);
                loop invariant  \forall integer f2, t2; k+1 <= r ==> count(g,f2,t2, k, k+1) == count{Pre}(g, f2,t2, k,k +1);
                loop invariant  \forall integer f2, t2; k+1 <= r ==> count{Pre}(g,f2,t2, 0, k+1) == count{Pre}(g, f2,t2, 0,k) + count{Pre}(g, f2,t2, k,k +1);
                loop invariant  \forall integer f2, t2; count(g,f2,t2, 0, k) == count{Pre}(g, f2,t2, 0,k);  // preserve2 в 3_1.mlw
                loop invariant graph_valid(g);
                loop variant r - k;
            @/
            for (int k = 0; k < r; k++){
        
            }
            /@ loop invariant r+1 <= k <= g->esize;
           loop invariant graph_valid(g);
           loop invariant \forall integer p; r < p  < g->esize  ==> g->edges[p] == \at(g->edges[p],Pre);
           loop invariant  \forall integer f2, t2; r+1<= k+1 <= g->esize ==> count(g,f2,t2, r+1, k + 1) == count(g, f2,t2,r+1, k) + count(g, f2,t2, k, k + 1);
           loop invariant  k < g->esize ==> g->edges[k] == \at(g->edges[\at(k, Here)], Pre);
           loop invariant  \forall integer f2, t2; k+1 <= g->esize  ==> count(g,f2,t2, k, k+1) == count{Pre}(g, f2,t2, k,k +1);
           loop invariant  \forall integer f2, t2; r+1< k <= g->esize ==> count(g,f2,t2, r+1, k) == count(g, f2,t2,r+1, k -1) + count(g, f2,t2, k-1, k)== 
           count(g, f2,t2,r+1, k -1) + count{Pre}(g, f2,t2, k -1,k) ==count{Pre}(g, f2,t2,r+1, k -1) + count{Pre}(g, f2,t2, k -1,k) == count{Pre}(g,f2,t2,r+1, k);
        
           loop variant g->esize -k;

        @/
            for (int k = r + 1; k < g->esize; k++){

            }
            */
//@ assert \forall integer f2,t2; count(g,f2,t2, 0, i) == count{Pre}(g, f2,t2, 0,i);
//@ assert \forall integer f2,t2; count(g,f2,t2, i+1, g->esize) == count{Pre}(g, f2, t2, i+1,g->esize);
//@ assert \forall integer f2,t2; count(g,f2,t2, 0, g->esize) == count(g,f2,t2, 0, i) + count(g,f2,t2, i,i + 1) + count(g,f2,t2, i+1 ,g->esize);
//@ assert \forall integer f2,t2; count(g,f2,t2, 0, g->esize) == count{Pre}(g,f2,t2, 0, i) + count(g,f2,t2,i, i+1) + count{Pre}(g,f2,t2, i+1 ,g->esize);
//@assert \forall integer f2, t2; (f2 != f || t2 != t) ==> count(g,f2,t2, 0, g->esize) == count{Pre}(g,f2,t2, 0, i) + count{Pre}(g,f2,t2, i+1 ,g->esize);
//@assert (\at(g->edges[\at(i, Here)].existent, Pre)) == 0;
//@assert count{Pre}(g,f,t, i , i+1) == 0;
//@assert count(g,f,t, i , i+1) == 1;
//@assert \forall integer f2, t2; (f2 != f || t2 != t) ==> count{Pre}(g,f2,t2, 0, g->esize) == count{Pre}(g,f2,t2, 0, i) + count{Pre}(g,f2,t2, i, i+1)+ count{Pre}(g,f2,t2, i+1 ,g->esize);
//@assert \forall integer f2, t2; (f2 != f || t2 != t) ==> count{Pre}(g,f2,t2, 0, g->esize) == count{Pre}(g,f2,t2, 0, i) + count{Pre}(g,f2,t2, i+1 ,g->esize);
//@assert \forall integer f2, t2; (f2 != f || t2 != t) ==> count(g,f2,t2, i, i+1) == 0;
	        return;
        }
    }
}

