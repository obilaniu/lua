/*
** $Id: inout.h,v 1.19 1997/06/18 20:35:49 roberto Exp roberto $
*/


#ifndef inout_h
#define inout_h

#include "types.h"
#include <stdio.h>


extern Word lua_linenumber;
extern Word lua_debugline;
extern char *lua_parsedfile;

void luaI_setparsedfile (char *name);

void luaI_predefine (void);

int lua_dobuffer (char *buff, int size);
int lua_doFILE (FILE *f, int bin);


#endif
