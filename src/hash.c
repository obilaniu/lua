/*
** hash.c
** hash manager for lua
** Luiz Henrique de Figueiredo - 17 Aug 90
*/

char *rcs_hash="$Id: hash.c,v 1.2 1994/03/28 15:14:02 celes Exp celes $";

#include <string.h>
#include <stdlib.h>

#include "mm.h"

#include "opcode.h"
#include "hash.h"
#include "inout.h"
#include "table.h"
#include "lua.h"

#define streq(s1,s2)	(strcmp(s1,s2)==0)
#define strneq(s1,s2)	(strcmp(s1,s2)!=0)

#define new(s)		((s *)malloc(sizeof(s)))
#define newvector(n,s)	((s *)calloc(n,sizeof(s)))

#define nhash(t)	((t)->nhash)
#define nodelist(t)	((t)->list)
#define list(t,i)	((t)->list[i])
#define markarray(t)    ((t)->mark)
#define ref_tag(n)	(tag(&(n)->ref))
#define ref_nvalue(n)	(nvalue(&(n)->ref))
#define ref_svalue(n)	(svalue(&(n)->ref))

#ifndef ARRAYBLOCK
#define ARRAYBLOCK 50
#endif

typedef struct ArrayList
{
 Hash *array;
 struct ArrayList *next;
} ArrayList;

static ArrayList *listhead = NULL;

static int head (Hash *t, Object *ref)		/* hash function */
{
 if (tag(ref) == T_NUMBER) return (((int)nvalue(ref))%nhash(t));
 else if (tag(ref) == T_STRING)
 {
  int h;
  char *name = svalue(ref);
  for (h=0; *name!=0; name++)		/* interpret name as binary number */
  {
   h <<= 8;
   h  += (unsigned char) *name;		/* avoid sign extension */
   h  %= nhash(t);			/* make it a valid index */
  }
  return h;
 }
 else
 {
  lua_reportbug ("unexpected type to index table");
  return -1;
 }
}

static Node *present(Hash *t, Object *ref, int h)
{
 Node *n=NULL, *p;
 if (tag(ref) == T_NUMBER)
 {
  for (p=NULL,n=list(t,h); n!=NULL; p=n, n=n->next)
   if (ref_tag(n) == T_NUMBER && nvalue(ref) == ref_nvalue(n)) break;
 }  
 else if (tag(ref) == T_STRING)
 {
  for (p=NULL,n=list(t,h); n!=NULL; p=n, n=n->next)
   if (ref_tag(n) == T_STRING && streq(svalue(ref),ref_svalue(n))) break;
 }  
 if (n==NULL)				/* name not present */
  return NULL;
#if 0
 if (p!=NULL)				/* name present but not first */
 {
  p->next=n->next;			/* move-to-front self-organization */
  n->next=list(t,h);
  list(t,h)=n;
 }
#endif
 return n;
}

static void freelist (Node *n)
{
 while (n)
 {
  Node *next = n->next;
  free (n);
  n = next;
 }
}

/*
** Create a new hash. Return the hash pointer or NULL on error.
*/
static Hash *hashcreate (unsigned int nhash)
{
 Hash *t = new (Hash);
 if (t == NULL)
 {
  lua_error ("not enough memory");
  return NULL;
 }
 nhash(t) = nhash;
 markarray(t) = 0;
 nodelist(t) = newvector (nhash, Node*);
 if (nodelist(t) == NULL)
 {
  lua_error ("not enough memory");
  return NULL;
 }
 return t;
}

/*
** Delete a hash
*/
static void hashdelete (Hash *h)
{
 int i;
 for (i=0; i<nhash(h); i++)
  freelist (list(h,i));
 free (nodelist(h));
 free(h);
}


/*
** Mark a hash and check its elements 
*/
void lua_hashmark (Hash *h)
{
 if (markarray(h) == 0)
 {
  int i;
  markarray(h) = 1;
  for (i=0; i<nhash(h); i++)
  {
   Node *n;
   for (n = list(h,i); n != NULL; n = n->next)
   {
    lua_markobject(&n->ref);
    lua_markobject(&n->val);
   }
  }
 } 
}
 
/*
** Garbage collection to arrays
** Delete all unmarked arrays.
*/
void lua_hashcollector (void)
{
 ArrayList *curr = listhead, *prev = NULL;
 while (curr != NULL)
 {
  ArrayList *next = curr->next;
  if (markarray(curr->array) != 1)
  {
   if (prev == NULL) listhead = next;
   else              prev->next = next;
   hashdelete(curr->array);
   free(curr);
  }
  else
  {
   markarray(curr->array) = 0;
   prev = curr;
  }
  curr = next;
 }
}


/*
** Create a new array
** This function insert the new array at array list. It also
** execute garbage collection if the number of array created
** exceed a pre-defined range.
*/
Hash *lua_createarray (int nhash)
{
 ArrayList *new = new(ArrayList);
 if (new == NULL)
 {
  lua_error ("not enough memory");
  return NULL;
 }
 new->array = hashcreate(nhash);
 if (new->array == NULL)
 {
  lua_error ("not enough memory");
  return NULL;
 }

 if (lua_nentity == lua_block)
  lua_pack(); 

 lua_nentity++;
 new->next = listhead;
 listhead = new;
 return new->array;
}


/*
** If the hash node is present, return its pointer, otherwise create a new
** node for the given reference and also return its pointer.
** On error, return NULL.
*/
Object *lua_hashdefine (Hash *t, Object *ref)
{
 int   h;
 Node *n;
 h = head (t, ref);
 if (h < 0) return NULL; 
 
 n = present(t, ref, h);
 if (n == NULL)
 {
  n = new(Node);
  if (n == NULL)
  {
   lua_error ("not enough memory");
   return NULL;
  }
  n->ref = *ref;
  tag(&n->val) = T_NIL;
  n->next = list(t,h);			/* link node to head of list */
  list(t,h) = n;
 }
 return (&n->val);
}


/*
** Internal function to manipulate arrays. 
** Given an array object and a reference value, return the next element
** in the hash.
** This function pushs the element value and its reference to the stack.
*/
static void firstnode (Hash *a, int h)
{
 if (h < nhash(a))
 {  
  int i;
  for (i=h; i<nhash(a); i++)
  {
   if (list(a,i) != NULL)
   {
    if (tag(&list(a,i)->val) != T_NIL)
    {
     lua_pushobject (&list(a,i)->ref);
     lua_pushobject (&list(a,i)->val);
     return;
    }
    else
    {
     Node *next = list(a,i)->next;
     while (next != NULL && tag(&next->val) == T_NIL) next = next->next;
     if (next != NULL)
     {
      lua_pushobject (&next->ref);
      lua_pushobject (&next->val);
      return;
     }
    }
   }
  }
 }
 lua_pushnil();
 lua_pushnil();
}
void lua_next (void)
{
 Hash   *a;
 Object *o = lua_getparam (1);
 Object *r = lua_getparam (2);
 if (o == NULL || r == NULL)
 { lua_error ("too few arguments to function `next'"); return; }
 if (lua_getparam (3) != NULL)
 { lua_error ("too many arguments to function `next'"); return; }
 if (tag(o) != T_ARRAY)
 { lua_error ("first argument of function `next' is not a table"); return; }
 a = avalue(o);
 if (tag(r) == T_NIL)
 {
  firstnode (a, 0);
  return;
 }
 else
 {
  int h = head (a, r);
  if (h >= 0)
  {
   Node *n = list(a,h);
   while (n)
   {
    if (memcmp(&n->ref,r,sizeof(Object)) == 0)
    {
     if (n->next == NULL)
     {
      firstnode (a, h+1);
      return;
     }
     else if (tag(&n->next->val) != T_NIL)
     {
      lua_pushobject (&n->next->ref);
      lua_pushobject (&n->next->val);
      return;
     }
     else
     {
      Node *next = n->next->next;
      while (next != NULL && tag(&next->val) == T_NIL) next = next->next;
      if (next == NULL)
      {
       firstnode (a, h+1);
       return;
      }
      else
      {
       lua_pushobject (&next->ref);
       lua_pushobject (&next->val);
      }
      return;
     }
    }
    n = n->next;
   }
   if (n == NULL)
    lua_error ("error in function 'next': reference not found");
  }
 }
}
