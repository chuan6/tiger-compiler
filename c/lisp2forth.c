/*
  Translate Lisp form expression to Forth form expression.

  Input example: "(/ (+ 1 2 3 4) 2)"
  Output example: "2 4 3 2 1 + + + /"
*/
#include <assert.h>
#include <ctype.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef struct {
        int isbranch;
        void *ptr;
} element;

typedef struct list {
        element elem;
        struct list *ptr;
} list;

void print_element(element e);
void print_list(list x);

void
print_element(element e) {
        //printf("-");
        if (e.isbranch) {
                print_list(*((list *)e.ptr));
        } else {
                printf("%s", (char *)e.ptr);
        }
}

void
print_list(list x) {
        list p;
        int c = 0;
        printf("(");
        for (p = x; p.ptr != NULL; p = *p.ptr, c++) {
                printf("%d: ", c);
                print_element(p.elem);
                printf(" ");
        }
        printf("%d: ", c);
        print_element(p.elem);
        printf(")");
}

int
len(list *x) {
        int c = 0;
        for (; x != NULL; x = x->ptr)
                c++;
        return c;
}

list *
conj(list *x, element e) {
        list *y = (list *)malloc(sizeof(list));
        if (y != NULL) {
                y->elem = e;
                y->ptr = x;
        }
        return y;
}

list *
reverse(list *x) {
        list *y = x->ptr;
        if (y == NULL)
                return x;

        x->ptr = NULL;

        list *z = y->ptr;
        if (z == NULL) {
                y->ptr = x;
                return y;
        }
        // length of x is >= 3.

        for (; z->ptr != NULL; z = z->ptr) {
                y->ptr = x;
                x = y;
                y = z;
        }
        y->ptr = x;
        z->ptr = y;
        return z;
}

void
delete(list *x) {
        if (x == NULL)
                return;
        if (x->elem.isbranch) {
                delete(x->elem.ptr);
        }
        free(x); // don't delete content pointed by x->ptr
}

enum flag {UNKOWN, OPEN, CLOSE, SPACE};
element collect_an_elem(char *s, char**end, enum flag *curr);
list *str_to_list(char *s, char **end, enum flag curr);

// s: a string whose first item, either a list "(...)" or a scalar, is to
//    be collected as an element of its enclosing list.
// end: output parameter; stores the pointer to the current position at s.
element
collect_an_elem(char *s, char **end, enum flag *curr) {
        for (; isspace(*s); s++)
                ;
        int spaceflag = 0;

        char *t = s;
        element e;
 LOOP:
        switch (*s) {
        case '(':
                *curr = OPEN;
                e.isbranch = 1;
                e.ptr = NULL;
                break;
        case ')':
                *curr = CLOSE;
                e.isbranch = 0;
                *s = '\0';
                e.ptr = t; // even if strlen(t)==0
                break;
        case '\0':
                // TODO error: ill-formatted list expression
                return e; // return right here!
        default:
                if (spaceflag |= isspace(*s)) { //first space
                        *curr = SPACE;
                        e.isbranch = 0;
                        *s = '\0';
                        e.ptr = t;
                        break;
                } else {
                        s++;
                        goto LOOP;
                }
        }

        *end = ++s;
        return e;
}

list *
str_to_list(char *s, char **end, enum flag curr) {
        if (curr != OPEN) {
                for (; *s != '('; s++)
                        ; // TODO error: *s == '\0'
                curr = OPEN;
                s++;
        }
        
        list *r = NULL;
        element e;
 LOOP:
        e = collect_an_elem(s, &s, &curr); // s and curr get updated
        switch (curr) {
        case OPEN:
                e.ptr = str_to_list(s, &s, curr);
                r = conj(r, e);
                goto LOOP;
        case CLOSE:
                if (e.isbranch || *((char *)e.ptr) != '\0' || r == NULL)
                        r = conj(r, e);
                *end = s;
                return reverse(r);
        case SPACE:
                r = conj(r, e);
                goto LOOP;
        default:
                // TODO handle other cases: UNKNOWN if necessary
                break;
        }

        return NULL;
}

list *
flatten(list *x, list **end) {
        list *suc = x->ptr;
        list *endp = x;
        if (x->elem.isbranch) {
                x = flatten((list *)x->elem.ptr, &endp);
                endp->ptr = suc;
        }
        if (suc == NULL) {
                return x;
        }
        suc = suc->ptr;

        list *pre = endp;
        list *p = pre->ptr;
        for (; suc != NULL; pre=endp, p=suc, suc=suc->ptr) {
                if (p->elem.isbranch) {
                        pre->ptr = flatten((list *)p->elem.ptr, &endp);
                        endp->ptr = suc;
                } else {
                        endp = endp->ptr;
                }
        }

        if (p->elem.isbranch) {
                pre->ptr = flatten((list *)p->elem.ptr, &endp);
        } else {
                endp = endp->ptr;
        }

        if (end != NULL)
                *end = endp;
        return x;
}

list *
to_forth(list *x) {
        int n = len(x) - 3;
        if (n > 0) {
                list *xend, *y;
                element e;
                int i = 0;
                do {
                        xend = x->ptr->ptr;
                        y = xend->ptr; // y != NULL
                
                        xend->ptr = NULL; //split
                        e.isbranch = 1;
                        e.ptr = x;
                        x = conj(conj(y, e), x->elem);
                } while (++i < n);
                assert(len(x) == 3);
        }
        assert(len(x) <= 3);
        
        list *t;
        for (t = x; t != NULL; t = t->ptr) {
                if (t->elem.isbranch) {
                        t->elem.ptr = to_forth((list *)t->elem.ptr);
                }
        }
        return reverse(x);
}

int main(int argc, char *argv[]) {
        //printf("%s\n", ++(argv[1]));
        char *endp;
        list *x = str_to_list(argv[1], &endp, UNKOWN);
        printf("length of list: %d\n", len(x));
        print_list(*x); printf("\n");

        x = to_forth(x);
        printf("length of list: %d\n", len(x));
        print_list(*x); printf("\n");

        x = flatten(x, NULL);
        printf("length of list: %d\n", len(x));
        print_list(*x); printf("\n");
        
        delete(x);
        return 0;
}
