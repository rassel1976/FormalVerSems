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

/*@

    lemma count_one2: 
    \forall Graph *g, integer f, t, m; 
        count_one_p(g, f, t, m) && 
        (count(g, f, t, m, (m + 1)) == (g->edges[m].existent != 0 && 
            g->edges[m].from == f && 
            g->edges[m].to == t ? 1 : 0));
    
    // lemma empty_ecnt3: 
    // \forall Graph *g, integer f, t, m; 
    //     graph_valid(g) && \valid(g) ==> 
    //         (g->ecnt <= m - 1 < g->esize) ==> ((count(g, f, t, m, m + 1)) == 0);

    lemma all_count2: 
    \forall Graph *g, integer k, f, t;
        (0 <= g->ecnt <= g->esize) 
        ==> 
        (all_count(g, f, t) == count(g, f, t, 0, g->esize)) &&
        (all_count(g, f, t) == count(g, f, t, 0, g->ecnt) + count(g, f, t, g->ecnt, g->esize)) &&
        (count(g, f, t, 0, g->esize) == count(g, f, t, 0, g->ecnt) + count(g, f, t, g->ecnt, g->esize));

    lemma all_count3:
    \forall Graph *g, integer k, f, t, m;
         (0 <= m - 1 <= g->ecnt) ==> 
             (count(g, f, t, 0, m)) == (count(g, f, t, 0, m - 1)) + (count(g, f, t, m - 1, m));

    // lemma all_count4:
    // \forall Graph *g, integer k, f, t, m;
    //      (0 <= m - 1 < g->esize) ==> 
    //          (count(g, f, t, 0, m)) == (count(g, f, t, 0, m - 1)) + (count(g, f, t, m - 1, m));

    // lemma count_zero_lemma:
    //     \forall Graph *g, integer f, t, m, n; 
    //         (m >= n) ==> (count(g, f, t, m, n) == 0);

    // lemma count_one_lemma:
    //     \forall Graph *g, integer f, t, m; 
    //         count_one_p(g, f, t, m) && 
    //         (count(g, f, t, m, (m + 1)) == (g->edges[m].existent != 0 && g->edges[m].from == f && g->edges[m].to == t ? 1 : 0));

    lemma count_split_lemma: 
        \forall Graph *g, integer f, t, m, n, k; 
            (m <= n <= k) 
            ==> 
            count_split_p(g, f, t, m, n, k) && 
            (count(g, f, t, m, k) == count(g, f, t, m, n) + count(g, f, t, n, k));

    // lemma all_count_lemma: 
    //     \forall Graph *g, integer k, f, t;
    //         (0 <= g->ecnt <= g->esize) 
    //         ==> 
    //         (all_count(g, f, t) == count(g, f, t, 0, g->esize)) &&
    //         (all_count(g, f, t) == count(g, f, t, 0, g->ecnt) + count(g, f, t, g->ecnt, g->esize)) &&
    //         (count(g, f, t, 0, g->esize) == count(g, f, t, 0, g->ecnt) + count(g, f, t, g->ecnt, g->esize));


*/

/*@
    ghost
    /@
        lemma
        requires \valid(g);
        requires graph_valid(g);
        requires g->ecnt <= k <= g->esize;
        decreases k - g->ecnt;
        ensures count(g, f, t, g->ecnt, k) == 0;
    @/
    void empty_ecnt(Graph *g, int f, int t, int k) {
        if (k > g->ecnt) {
            //@ assert count(g, f, t, (k - 1), k) == 0;
            //@ assert count(g, f, t, g->ecnt, k) == count(g, f, t, g->ecnt, (k - 1)) + count(g, f, t, (k - 1), k); 
            empty_ecnt(g, f, t, (k - 1));
        }
    }
        
*/

/*@ lemma count_prop{L}:
    \forall Graph *g; \forall integer f, t, m, n; m <= n ==> count(g, f, t, m, (n+1)) == count(g, f,t, m,n) + count(g,f,t,n, n+1);  
*/
/*@ lemma count_prop2{L}:
    \forall Graph *g; \forall integer f, t, m, n, z,k; z== k+1 && m <=k && z<=n ==> count(g, f, t, m, n) == count(g, f, t, m, k) +  count(g, f, t, k, z) + count(g, f, t, z, n);
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
    /*@
        loop invariant 0 <= c <= i;
        loop invariant ( i <= g->ecnt);
        loop invariant c == count(g, f, t, 0, i);
        loop variant (g->ecnt - i);
    */
    for (int i = 0; i < g->ecnt; ++i) {
        
        if (g->edges[i].existent && g->edges[i].from == f && g->edges[i].to == t) {
            ++ c;
        }
        /*@
            assert g->edges[i].existent && g->edges[i].from == f && g->edges[i].to == t ? 
                count(g, f, t, i, i + 1) == 1 : 
                count(g, f, t, i, i + 1) == 0; 
        */
    }

    /*@ assert c == count(g, f, t, 0, g->ecnt); */
    /*@ assert count(g, f, t, g->ecnt, g->esize) == 0; */
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
    Pre1:
    if (g->ecnt < g->esize) {
        //@ assert \forall integer f2, t2; count{Pre}(g,f2,t2, 0, g->esize) == count{Pre}(g,f2,t2, 0, g->ecnt) + count{Pre}(g,f2,t2, g->ecnt,g->ecnt + 1) + count{Pre}(g,f2,t2, g->ecnt + 1,g->esize);
        //@assert \forall integer f2 ,t2; count{Pre}(g,f2,t2, g->ecnt, g->ecnt+1) == 0;
        g->edges[g->ecnt].from = f;
        g->edges[g->ecnt].to = t;
        g->edges[g->ecnt].existent = 1;
	    ++ g->ecnt;
         /*@
            assert \forall integer f2, t2;
                        (f2 != f || t2 != t) ==> count{Here}(g, f2, t2, g->ecnt - 1, g->ecnt) == count{Pre}(g, f2, t2, g->ecnt - 1, g->ecnt);
        */

        /*@ ghost
            int k1 = 0;
            /@
                loop invariant \valid(g) && \valid(g->edges + (0 .. g->esize - 1));
                loop invariant k1 <= g->esize;
                loop invariant graph_valid(g);
                loop invariant k1 >= 0;
                loop variant (g->esize - k1);
            @/

            while (k1 < g->esize) {
                k1++;
            }
            int k4 = 0;
            /@
                loop invariant \valid(g) && \valid(g->edges + (0 .. g->esize - 1));
                loop invariant k4 >= 0;
                loop invariant k4 <= g->esize;
                loop invariant \forall int j; 0 <= j <= k4 && j < g->esize ==> 
                    j != (g->ecnt - 1) ==> 
                    \at(g->edges[j].from, Pre1) == \at(g->edges[j].from, Here) &&
                    \at(g->edges[j].to, Pre1) == \at(g->edges[j].to, Here) &&
                    \at(g->edges[j].existent, Pre1) == \at(g->edges[j].existent, Here);
                loop invariant \forall integer k; 
                     (0 <= k <= k4) && (k < g->esize)
                     ==>
                     \forall integer f2, t2;
                         (f2 != f || t2 != t) ==> count{Here}(g, f2, t2, k, k + 1) == count{Pre}(g, f2, t2, k, k + 1);
                loop variant (g->esize - k4);
            @/

            while (k4 < g->esize) {
                k4++;
            }

            int k8 = 0;
            /@
                loop invariant \valid(g) && \valid(g->edges + (0 .. g->esize - 1));
                loop invariant k8 >= 0;
                loop invariant k8 <= g->ecnt - 1;
                loop invariant 
                    \forall integer f2, t2;
                        (f2 != f || t2 != t) ==> count{Here}(g, f2, t2, 0, k8) == count{Pre}(g, f2, t2, 0, k8);
                loop variant (g->ecnt - 1 - k8);
            @/

            while (k8 < g->ecnt - 1) {
                k8++;
            }


            int k2 = 0;
            /@
                loop invariant \valid(g) && \valid(g->edges + (0 .. g->esize - 1));
                loop invariant k2 >= 0;
                loop invariant k2 <= g->esize;
                loop invariant \forall integer k; 
                    (0 <= k <= k2) && (k < g->esize)
                    ==>
                    \forall integer f2, t2;
                        (f2 != f || t2 != t) ==> count{Here}(g, f2, t2, 0, k) == count{Pre}(g, f2, t2, 0, k);
                loop variant (g->esize - k2);
            @/

            while (k2 < g->esize) {
                k2++;
                /@
                    assert \forall integer q; 
                    (0 <= q <= k2) && (q < g->esize) ==>
                    \forall integer f2, t2; (f2 != f || t2 != t) ==>
                    count{Pre1}(g, f2, t2, 0, q)
                            == count{Pre1}(g, f2, t2, 0, q - 1) + count{Pre1}(g, f2, t2, q - 1, q)
                            == count{Pre1}(g, f2, t2, 0, q - 1) +  count{Here}(g, f2, t2, q - 1, q)
                            == count{Here}(g, f2, t2, 0, q - 1) + count{Here}(g, f2, t2, q - 1, q)
                            == count{Here}(g, f2, t2, 0, q);
                @/
            }
            int k3 = 0;
            /@
                loop invariant \valid(g) && \valid(g->edges + (0 .. g->esize - 1));
                loop invariant k3 >= 0;
                loop invariant k3 <= g->esize;
                loop invariant count{Here}(g, f, t, 0, k3) == count{Pre1}(g, f, t, 0, k3) + (k3 < g->ecnt ? 0 : 1);
                loop variant (g->esize - k3);
            @/

            while (k3 < g->esize) {
                k3++;
            }
        */

        return;
    }

    Pre2:
    for (int i = 0; i < g->ecnt; ++i) {
        Pre3:
       if (!g->edges[i].existent) {
            g->edges[i].from = f;
            g->edges[i].to = t;
	        g->edges[i].existent = 1;
	        return;
        }
    }
}

