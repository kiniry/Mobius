/* A Bison parser, made by GNU Bison 2.3.  */

/* Skeleton interface for Bison's Yacc-like parsers in C

   Copyright (C) 1984, 1989, 1990, 2000, 2001, 2002, 2003, 2004, 2005, 2006
   Free Software Foundation, Inc.

   This program is free software; you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation; either version 2, or (at your option)
   any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program; if not, write to the Free Software
   Foundation, Inc., 51 Franklin Street, Fifth Floor,
   Boston, MA 02110-1301, USA.  */

/* As a special exception, you may create a larger work that contains
   part or all of the Bison parser skeleton and distribute that work
   under terms of your choice, so long as that work isn't itself a
   parser generator using the skeleton or a modified version thereof
   as a parser skeleton.  Alternatively, if you modify or redistribute
   the parser skeleton itself, you may (at your option) remove this
   special exception, which will cause the skeleton and the resulting
   Bison output files to be licensed under the GNU General Public
   License without this special exception.

   This special exception was added by the Free Software Foundation in
   version 2.2 of Bison.  */

/* Tokens.  */
#ifndef YYTOKENTYPE
# define YYTOKENTYPE
   /* Put the tokens into the symbol table, so that GDB and other debuggers
      know about them.  */
   enum yytokentype {
     NUMERAL_TOK = 258,
     SYM_TOK = 259,
     STRING_TOK = 260,
     AR_SYMB = 261,
     USER_VAL_TOK = 262,
     TRUE_TOK = 263,
     FALSE_TOK = 264,
     ITE_TOK = 265,
     NOT_TOK = 266,
     IMPLIES_TOK = 267,
     IF_THEN_ELSE_TOK = 268,
     AND_TOK = 269,
     OR_TOK = 270,
     XOR_TOK = 271,
     IFF_TOK = 272,
     EXISTS_TOK = 273,
     FORALL_TOK = 274,
     LET_TOK = 275,
     FLET_TOK = 276,
     NOTES_TOK = 277,
     CVC_COMMAND_TOK = 278,
     LOGIC_TOK = 279,
     COLON_TOK = 280,
     LBRACKET_TOK = 281,
     RBRACKET_TOK = 282,
     LCURBRACK_TOK = 283,
     RCURBRACK_TOK = 284,
     LPAREN_TOK = 285,
     RPAREN_TOK = 286,
     SAT_TOK = 287,
     UNSAT_TOK = 288,
     UNKNOWN_TOK = 289,
     ASSUMPTION_TOK = 290,
     FORMULA_TOK = 291,
     STATUS_TOK = 292,
     BENCHMARK_TOK = 293,
     EXTRASORTS_TOK = 294,
     EXTRAFUNS_TOK = 295,
     EXTRAPREDS_TOK = 296,
     DOLLAR_TOK = 297,
     QUESTION_TOK = 298,
     DISTINCT_TOK = 299,
     EOF_TOK = 300,
     PAT_TOK = 301
   };
#endif
/* Tokens.  */
#define NUMERAL_TOK 258
#define SYM_TOK 259
#define STRING_TOK 260
#define AR_SYMB 261
#define USER_VAL_TOK 262
#define TRUE_TOK 263
#define FALSE_TOK 264
#define ITE_TOK 265
#define NOT_TOK 266
#define IMPLIES_TOK 267
#define IF_THEN_ELSE_TOK 268
#define AND_TOK 269
#define OR_TOK 270
#define XOR_TOK 271
#define IFF_TOK 272
#define EXISTS_TOK 273
#define FORALL_TOK 274
#define LET_TOK 275
#define FLET_TOK 276
#define NOTES_TOK 277
#define CVC_COMMAND_TOK 278
#define LOGIC_TOK 279
#define COLON_TOK 280
#define LBRACKET_TOK 281
#define RBRACKET_TOK 282
#define LCURBRACK_TOK 283
#define RCURBRACK_TOK 284
#define LPAREN_TOK 285
#define RPAREN_TOK 286
#define SAT_TOK 287
#define UNSAT_TOK 288
#define UNKNOWN_TOK 289
#define ASSUMPTION_TOK 290
#define FORMULA_TOK 291
#define STATUS_TOK 292
#define BENCHMARK_TOK 293
#define EXTRASORTS_TOK 294
#define EXTRAFUNS_TOK 295
#define EXTRAPREDS_TOK 296
#define DOLLAR_TOK 297
#define QUESTION_TOK 298
#define DISTINCT_TOK 299
#define EOF_TOK 300
#define PAT_TOK 301




#if ! defined YYSTYPE && ! defined YYSTYPE_IS_DECLARED
typedef union YYSTYPE
#line 66 "smtlib.y"
{
  std::string *str;
  std::vector<std::string> *strvec;
  CVC3::Expr *node;
  std::vector<CVC3::Expr> *vec;
  std::pair<std::vector<CVC3::Expr>, std::vector<std::string> > *pat_ann;
}
/* Line 1489 of yacc.c.  */
#line 149 "parsesmtlib.hpp"
	YYSTYPE;
# define yystype YYSTYPE /* obsolescent; will be withdrawn */
# define YYSTYPE_IS_DECLARED 1
# define YYSTYPE_IS_TRIVIAL 1
#endif

extern YYSTYPE smtliblval;

