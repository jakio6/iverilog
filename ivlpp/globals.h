#ifndef __globals_H
#define __globals_H
/*
 * Copyright (c) 1999 Stephen Williams (steve@icarus.com)
 *
 *    This source code is free software; you can redistribute it
 *    and/or modify it in source code form under the terms of the GNU
 *    General Public License as published by the Free Software
 *    Foundation; either version 2 of the License, or (at your option)
 *    any later version.
 *
 *    This program is distributed in the hope that it will be useful,
 *    but WITHOUT ANY WARRANTY; without even the implied warranty of
 *    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *    GNU General Public License for more details.
 *
 *    You should have received a copy of the GNU General Public License
 *    along with this program; if not, write to the Free Software
 *    Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA
 */
#if !defined(WINNT)
#ident "$Id: globals.h,v 1.2 1999/09/05 22:33:18 steve Exp $"
#endif

# include  <stdio.h>

extern void reset_lexor(FILE*out, char*paths[]);
extern void define_macro(const char*name, const char*value);

/* These variables contain the include directories to be searched when
   an include directive in encountered. */
extern char**include_dir;
extern unsigned include_cnt;

/* This flag is true if #line directives are to be generated. */
extern int line_direct_flag;

/* This is the entry to the parser. */
extern int yyparse();

/*
 * $Log: globals.h,v $
 * Revision 1.2  1999/09/05 22:33:18  steve
 *  Take multiple source files on the command line.
 *
 * Revision 1.1  1999/07/03 20:03:47  steve
 *  Add include path and line directives.
 *
 */
#endif
