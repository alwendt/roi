/* C compiler: symbol table management */

#include <stdio.h>

#define HASHSIZE 119            /* hash table size */

static struct string {          /* string table */
        char *str;              /* string */
        struct string *next;    /* next entry */
} *stab[HASHSIZE];


/* alloc - allocate n bytes of storage or die */
char *alloc(n)
int n;
{
        char *s, *malloc();

        if ((s = malloc(n)) == NULL) {
                fprintf(stderr, "compiler error: storage overflow\n");
                exit(1);
                }
        return (s);
}



/* slookup - lookup str, install if flag is non-zero, return pointer */
char *slookup(str, flag)
char *str;
int flag;
{
        register int h, len;
        char *s, *strcpy();
        register struct string *p;

        h = 0;
        for (s = str, len = 0; *s; len++)
                h += *s++;
        for (p = stab[h%HASHSIZE]; p; p = p->next)
                if (strcmp(str, p->str) == 0)
                        return (p->str);
        if (flag) {
                p = (struct string *) alloc(sizeof(struct string));
                p->str = strcpy(alloc(len + 1), str);
                p->next = stab[h%HASHSIZE];
                stab[h%HASHSIZE] = p;
                return (p->str);
                }
        return (NULL);
}
