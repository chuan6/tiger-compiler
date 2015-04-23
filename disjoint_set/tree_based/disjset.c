#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef struct element {
    struct element* parent;
    int rank;
    void* item;
} element;

element*
link_elements(element* x, element* y) {
    if (x == y)
        return x;

    int xrank = x->rank, yrank = y->rank;
    if (xrank < yrank) {
        x->parent = y;
        return y;
    } //xrank >= yrank

    y->parent = x;
    if (xrank == yrank)
        x->rank += 1;
    return x;
}

element*
make_set(void* x) {
    element* ep = (element*) malloc(sizeof(element));
    ep->parent = ep;
    ep->rank = 0;
    ep->item = x;
    return ep;
}

void free_element(element* x) { free(x); }

element*
find_set(element* x) {
    assert(x != NULL);
    assert(x->parent != NULL);
    if (x->parent == x) {
        return x;
    }
    return x->parent = find_set(x->parent);
}

element*
union_sets(element* x, element* y) {
    //if x and y belong to the same set, simply return the set
    return link_elements(find_set(x), find_set(y));
}

int main() {
    char* str_a = "hello";
    char* str_b = "world";
    char* str_c = "chuan";
    char* str_d = "leo";
    char* str_e = "compiler";
    char* str_f = "tiger";

    element* a = make_set(str_a);
    element* b = make_set(str_b);
    element* c = make_set(str_c);
    element* d = make_set(str_d);
    element* e = make_set(str_e);
    element* f = make_set(str_f);

    assert(a->parent == a
           && b->parent == b
           && c->parent == c
           && d->parent == d
           && e->parent == e
           && f->parent == f);

    element* x = union_sets(a, b);
    element* y = union_sets(c, d);
    element* z = union_sets(e, f);
    assert(x->rank == 1 && y->rank == 1 && z->rank == 1
           && x == a && y == c && z == e);

    element* u = union_sets(b, d);
    assert(u->rank == 2 && u == a);
    element* v = union_sets(b, f);
    assert(v->rank == 2 && u == a);

    assert(find_set(a) == a
           && find_set(b) == a
           && find_set(c) == a
           && find_set(d) == a
           && find_set(e) == a
           && find_set(f) == a);
    
    free_element(a);
    free_element(b);
    free_element(c);
    free_element(d);
    free_element(e);
    free_element(f);

    printf("test_0 passed.\n");
    return 0;
}
