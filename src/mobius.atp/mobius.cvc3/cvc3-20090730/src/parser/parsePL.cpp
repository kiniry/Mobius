/* A Bison parser, made by GNU Bison 2.3.  */

/* Skeleton implementation for Bison's Yacc-like parsers in C

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

/* C LALR(1) parser skeleton written by Richard Stallman, by
   simplifying the original so-called "semantic" parser.  */

/* All symbols defined below should begin with yy or YY, to avoid
   infringing on user name space.  This should be done even for local
   variables, as they might otherwise be expanded by user macros.
   There are some unavoidable exceptions within include files to
   define necessary library symbols; they are noted "INFRINGES ON
   USER NAME SPACE" below.  */

/* Identify Bison output.  */
#define YYBISON 1

/* Bison version.  */
#define YYBISON_VERSION "2.3"

/* Skeleton name.  */
#define YYSKELETON_NAME "yacc.c"

/* Pure parsers.  */
#define YYPURE 0

/* Using locations.  */
#define YYLSP_NEEDED 0

/* Substitute the variable and function names.  */
#define yyparse PLparse
#define yylex   PLlex
#define yyerror PLerror
#define yylval  PLlval
#define yychar  PLchar
#define yydebug PLdebug
#define yynerrs PLnerrs


/* Tokens.  */
#ifndef YYTOKENTYPE
# define YYTOKENTYPE
   /* Put the tokens into the symbol table, so that GDB and other debuggers
      know about them.  */
   enum yytokentype {
     DISTINCT_TOK = 258,
     AND_TOK = 259,
     ARRAY_TOK = 260,
     BOOLEAN_TOK = 261,
     DATATYPE_TOK = 262,
     ELSE_TOK = 263,
     ELSIF_TOK = 264,
     END_TOK = 265,
     ENDIF_TOK = 266,
     EXISTS_TOK = 267,
     FALSELIT_TOK = 268,
     FORALL_TOK = 269,
     IN_TOK = 270,
     IF_TOK = 271,
     LAMBDA_TOK = 272,
     SIMULATE_TOK = 273,
     LET_TOK = 274,
     NOT_TOK = 275,
     IS_INTEGER_TOK = 276,
     OF_TOK = 277,
     OR_TOK = 278,
     REAL_TOK = 279,
     INT_TOK = 280,
     SUBTYPE_TOK = 281,
     BITVECTOR_TOK = 282,
     THEN_TOK = 283,
     TRUELIT_TOK = 284,
     TYPE_TOK = 285,
     WITH_TOK = 286,
     XOR_TOK = 287,
     TCC_TOK = 288,
     PATTERN_TOK = 289,
     DONE_TOK = 290,
     DOTDOT_TOK = 291,
     ASSIGN_TOK = 292,
     NEQ_TOK = 293,
     IMPLIES_TOK = 294,
     IFF_TOK = 295,
     PLUS_TOK = 296,
     MINUS_TOK = 297,
     MULT_TOK = 298,
     POW_TOK = 299,
     DIV_TOK = 300,
     MOD_TOK = 301,
     INTDIV_TOK = 302,
     LT_TOK = 303,
     LE_TOK = 304,
     GT_TOK = 305,
     GE_TOK = 306,
     FLOOR_TOK = 307,
     LEFTSHIFT_TOK = 308,
     RIGHTSHIFT_TOK = 309,
     BVPLUS_TOK = 310,
     BVSUB_TOK = 311,
     BVUDIV_TOK = 312,
     BVSDIV_TOK = 313,
     BVUREM_TOK = 314,
     BVSREM_TOK = 315,
     BVSMOD_TOK = 316,
     BVSHL_TOK = 317,
     BVASHR_TOK = 318,
     BVLSHR_TOK = 319,
     BVUMINUS_TOK = 320,
     BVMULT_TOK = 321,
     SQHASH_TOK = 322,
     HASHSQ_TOK = 323,
     PARENHASH_TOK = 324,
     HASHPAREN_TOK = 325,
     ARROW_TOK = 326,
     BVNEG_TOK = 327,
     BVAND_TOK = 328,
     MID_TOK = 329,
     BVXOR_TOK = 330,
     BVNAND_TOK = 331,
     BVNOR_TOK = 332,
     BVCOMP_TOK = 333,
     BVXNOR_TOK = 334,
     CONCAT_TOK = 335,
     BVTOINT_TOK = 336,
     INTTOBV_TOK = 337,
     BOOLEXTRACT_TOK = 338,
     BVLT_TOK = 339,
     BVGT_TOK = 340,
     BVLE_TOK = 341,
     BVGE_TOK = 342,
     SX_TOK = 343,
     BVZEROEXTEND_TOK = 344,
     BVREPEAT_TOK = 345,
     BVROTL_TOK = 346,
     BVROTR_TOK = 347,
     BVSLT_TOK = 348,
     BVSGT_TOK = 349,
     BVSLE_TOK = 350,
     BVSGE_TOK = 351,
     ARITH_VAR_ORDER_TOK = 352,
     ASSERT_TOK = 353,
     QUERY_TOK = 354,
     CHECKSAT_TOK = 355,
     CONTINUE_TOK = 356,
     RESTART_TOK = 357,
     HELP_TOK = 358,
     DBG_TOK = 359,
     TRACE_TOK = 360,
     UNTRACE_TOK = 361,
     OPTION_TOK = 362,
     TRANSFORM_TOK = 363,
     PRINT_TOK = 364,
     PRINT_TYPE_TOK = 365,
     CALL_TOK = 366,
     ECHO_TOK = 367,
     INCLUDE_TOK = 368,
     DUMP_PROOF_TOK = 369,
     DUMP_ASSUMPTIONS_TOK = 370,
     DUMP_SIG_TOK = 371,
     DUMP_TCC_TOK = 372,
     DUMP_TCC_ASSUMPTIONS_TOK = 373,
     DUMP_TCC_PROOF_TOK = 374,
     DUMP_CLOSURE_TOK = 375,
     DUMP_CLOSURE_PROOF_TOK = 376,
     WHERE_TOK = 377,
     ASSERTIONS_TOK = 378,
     ASSUMPTIONS_TOK = 379,
     COUNTEREXAMPLE_TOK = 380,
     COUNTERMODEL_TOK = 381,
     PUSH_TOK = 382,
     POP_TOK = 383,
     POPTO_TOK = 384,
     PUSH_SCOPE_TOK = 385,
     POP_SCOPE_TOK = 386,
     POPTO_SCOPE_TOK = 387,
     RESET_TOK = 388,
     CONTEXT_TOK = 389,
     FORGET_TOK = 390,
     GET_TYPE_TOK = 391,
     CHECK_TYPE_TOK = 392,
     GET_CHILD_TOK = 393,
     GET_OP_TOK = 394,
     SUBSTITUTE_TOK = 395,
     UMINUS_TOK = 396,
     ID_TOK = 397,
     STRINGLIT_TOK = 398,
     NUMERAL_TOK = 399,
     HEX_TOK = 400,
     BINARY_TOK = 401
   };
#endif
/* Tokens.  */
#define DISTINCT_TOK 258
#define AND_TOK 259
#define ARRAY_TOK 260
#define BOOLEAN_TOK 261
#define DATATYPE_TOK 262
#define ELSE_TOK 263
#define ELSIF_TOK 264
#define END_TOK 265
#define ENDIF_TOK 266
#define EXISTS_TOK 267
#define FALSELIT_TOK 268
#define FORALL_TOK 269
#define IN_TOK 270
#define IF_TOK 271
#define LAMBDA_TOK 272
#define SIMULATE_TOK 273
#define LET_TOK 274
#define NOT_TOK 275
#define IS_INTEGER_TOK 276
#define OF_TOK 277
#define OR_TOK 278
#define REAL_TOK 279
#define INT_TOK 280
#define SUBTYPE_TOK 281
#define BITVECTOR_TOK 282
#define THEN_TOK 283
#define TRUELIT_TOK 284
#define TYPE_TOK 285
#define WITH_TOK 286
#define XOR_TOK 287
#define TCC_TOK 288
#define PATTERN_TOK 289
#define DONE_TOK 290
#define DOTDOT_TOK 291
#define ASSIGN_TOK 292
#define NEQ_TOK 293
#define IMPLIES_TOK 294
#define IFF_TOK 295
#define PLUS_TOK 296
#define MINUS_TOK 297
#define MULT_TOK 298
#define POW_TOK 299
#define DIV_TOK 300
#define MOD_TOK 301
#define INTDIV_TOK 302
#define LT_TOK 303
#define LE_TOK 304
#define GT_TOK 305
#define GE_TOK 306
#define FLOOR_TOK 307
#define LEFTSHIFT_TOK 308
#define RIGHTSHIFT_TOK 309
#define BVPLUS_TOK 310
#define BVSUB_TOK 311
#define BVUDIV_TOK 312
#define BVSDIV_TOK 313
#define BVUREM_TOK 314
#define BVSREM_TOK 315
#define BVSMOD_TOK 316
#define BVSHL_TOK 317
#define BVASHR_TOK 318
#define BVLSHR_TOK 319
#define BVUMINUS_TOK 320
#define BVMULT_TOK 321
#define SQHASH_TOK 322
#define HASHSQ_TOK 323
#define PARENHASH_TOK 324
#define HASHPAREN_TOK 325
#define ARROW_TOK 326
#define BVNEG_TOK 327
#define BVAND_TOK 328
#define MID_TOK 329
#define BVXOR_TOK 330
#define BVNAND_TOK 331
#define BVNOR_TOK 332
#define BVCOMP_TOK 333
#define BVXNOR_TOK 334
#define CONCAT_TOK 335
#define BVTOINT_TOK 336
#define INTTOBV_TOK 337
#define BOOLEXTRACT_TOK 338
#define BVLT_TOK 339
#define BVGT_TOK 340
#define BVLE_TOK 341
#define BVGE_TOK 342
#define SX_TOK 343
#define BVZEROEXTEND_TOK 344
#define BVREPEAT_TOK 345
#define BVROTL_TOK 346
#define BVROTR_TOK 347
#define BVSLT_TOK 348
#define BVSGT_TOK 349
#define BVSLE_TOK 350
#define BVSGE_TOK 351
#define ARITH_VAR_ORDER_TOK 352
#define ASSERT_TOK 353
#define QUERY_TOK 354
#define CHECKSAT_TOK 355
#define CONTINUE_TOK 356
#define RESTART_TOK 357
#define HELP_TOK 358
#define DBG_TOK 359
#define TRACE_TOK 360
#define UNTRACE_TOK 361
#define OPTION_TOK 362
#define TRANSFORM_TOK 363
#define PRINT_TOK 364
#define PRINT_TYPE_TOK 365
#define CALL_TOK 366
#define ECHO_TOK 367
#define INCLUDE_TOK 368
#define DUMP_PROOF_TOK 369
#define DUMP_ASSUMPTIONS_TOK 370
#define DUMP_SIG_TOK 371
#define DUMP_TCC_TOK 372
#define DUMP_TCC_ASSUMPTIONS_TOK 373
#define DUMP_TCC_PROOF_TOK 374
#define DUMP_CLOSURE_TOK 375
#define DUMP_CLOSURE_PROOF_TOK 376
#define WHERE_TOK 377
#define ASSERTIONS_TOK 378
#define ASSUMPTIONS_TOK 379
#define COUNTEREXAMPLE_TOK 380
#define COUNTERMODEL_TOK 381
#define PUSH_TOK 382
#define POP_TOK 383
#define POPTO_TOK 384
#define PUSH_SCOPE_TOK 385
#define POP_SCOPE_TOK 386
#define POPTO_SCOPE_TOK 387
#define RESET_TOK 388
#define CONTEXT_TOK 389
#define FORGET_TOK 390
#define GET_TYPE_TOK 391
#define CHECK_TYPE_TOK 392
#define GET_CHILD_TOK 393
#define GET_OP_TOK 394
#define SUBSTITUTE_TOK 395
#define UMINUS_TOK 396
#define ID_TOK 397
#define STRINGLIT_TOK 398
#define NUMERAL_TOK 399
#define HEX_TOK 400
#define BINARY_TOK 401




/* Copy the first part of user declarations.  */
#line 1 "PL.y"

/*****************************************************************************/
/*!
 * \file PL.y
 * 
 * Author: Sergey Berezin
 * 
 * Created: Feb 06 03:00:43 GMT 2003
 *
 * <hr>
 *
 * License to use, copy, modify, sell and/or distribute this software
 * and its documentation for any purpose is hereby granted without
 * royalty, subject to the terms and conditions defined in the \ref
 * LICENSE file provided with this distribution.
 * 
 * <hr>
 * 
 */
/*****************************************************************************/
/* PL.y
   Aaron Stump, 4/14/01

   This file contains the bison code for the parser that reads in CVC
   commands in the presentation language (hence "PL").
*/

#include "vc.h"
#include "parser_exception.h"
#include "parser_temp.h"
#include "rational.h"

// Exported shared data
namespace CVC3 {
  extern ParserTemp* parserTemp;
}
// Define shortcuts for various things
#define TMP CVC3::parserTemp
#define EXPR CVC3::parserTemp->expr
#define VC (CVC3::parserTemp->vc)
#define RAT(args) CVC3::newRational args

// Suppress the bogus warning suppression in bison (it generates
// compile error)
#undef __GNUC_MINOR__

/* stuff that lives in PL.lex */
extern int PLlex(void);

int PLerror(const char *s)
{
  std::ostringstream ss;
  ss << CVC3::parserTemp->fileName << ":" << CVC3::parserTemp->lineNum
     << ": " << s;
  return CVC3::parserTemp->error(ss.str());
}


namespace CVC3 {

// File-static auxiliary funcion to wrap accessors upto the index i
// (not inclusive) around "e".  Used to rebuild the UPDATE expressions.
static Expr wrapAccessors(const Expr& e,
			  const std::vector<Expr>& accessors,
			  const int i) {
  DebugAssert((int)accessors.size() >= i, "wrapAccessors: too few accessors");
  Expr res(e);
  for(int j=0; j<i; j++) {
    const Expr& acc = accessors[j];
    switch(acc.getKind()) {
    case ID: // Datatype: apply the accessor directly to 'res'
      res = VC->listExpr(acc, res);
      break;
    case RAW_LIST:
      DebugAssert(acc.arity() == 2 && acc[0].getKind() == ID,
		  "PL.y: wrong number of arguments in the accessor of WITH: "
		  +acc.toString());
      res = VC->listExpr(acc[0], res, acc[1]);
      break;
    default:
      DebugAssert(false, "PL.y: Bad accessor in WITH: "+acc.toString());
    }
  }
  return res;
}

// Convert a complex WITH statement into a bunch of nested simple UPDATEs

// Updator "e1 WITH accessors := e2" is represented as
// (e1 (accessor1 accessor2 ... ) e2), where the accessors are:
// (READ idx)
// ID (datatype constructor's argument)
// (RECORD_SELECT ID)
// and (TUPLE_SELECT num).
 
// We rebuild this into nested RECORD_UPDATE, WRITE,
// TUPLE_UPDATE, and DATATYPE_UPDATE expressions.  For example:
//
// e WITH [idx] car.f := newVal  is transformed into
// e WITH [idx] := (e[idx] WITH car := (car(e[idx]) WITH .f := newVal))
// which is represented as
// (WRITE e idx
//        (DATATYPE_UPDATE (READ e idx) car
//                         (RECORD_UPDATE (car (READ e idx)) f newVal))).
// Here "car" and "f" are identifiers (ID "car") and (ID "f").

static Expr PLprocessUpdate(const CVC3::Expr& e,
			    const CVC3::Expr& update) {
  TRACE("parser verbose", "PLprocessUpdate(", e, ") {");
  DebugAssert(update.arity() == 2,"PL.y: Bad WITH statement: "
	      +update.toString());
  // Rebuild accessors: resolve ID in (READ (ID "name")) and leave
  // the rest alone
  TRACE("parser verbose", "PLprocessUpdate: update[0] = ", update[0], "");
  std::vector<Expr> acc;
  for(Expr::iterator i=update[0].begin(), iend=update[0].end(); i!=iend; ++i) {
    TRACE("parser verbose", "*i = ", *i, "");
    acc.push_back(*i);
  }
  TRACE("parser verbose", "acc.size() = ", acc.size(), "");
  TRACE("parser verbose", "accessors = ", VC->listExpr(acc), "");
  // 'res' serves as the accumulator of updators; initially it is
  // newVal (which is update[1]).  We run through accessors in reverse
  // order, wrapping this accumulator with the corresponding
  // updators.
  Expr res(update[1]);
  // Rebuilding the original expression "e"
  // The main loop
  for(int i=acc.size()-1; i>=0; i--) {
    Expr ac(acc[i]);  // The current accessor
    TRACE("parser verbose", "ac["+int2string(i)+"] = ", ac, "");
    // "e" with all preceding accessors
    Expr tmp(wrapAccessors(e, acc, i));
    TRACE("parser verbose", "tmp = ", tmp, "");
    switch(ac.getKind()) {
    case ID: // Datatype update
      res = VC->listExpr("_DATATYPE_UPDATE", tmp, ac, res);
      break;
    case RAW_LIST: {
      const std::string& kind = ac[0][0].getString();
      if(kind == "_READ") // Array update
	res = VC->listExpr("_WRITE", tmp, ac[1], res);
      else if(kind == "_RECORD_SELECT") // Record update
	res = VC->listExpr("_RECORD_UPDATE", tmp, ac[1], res);
      else if(kind == "_TUPLE_SELECT") // Tuple element
	res = VC->listExpr("_TUPLE_UPDATE", tmp, ac[1], res);
      else
	DebugAssert(false, "PL.y: Bad accessor in WITH: "+ac.toString());
      break;
    }
    default:
      DebugAssert(false, "PL.y: Bad accessor in WITH: "+ac.toString());
    }
  }
  TRACE("parser verbose", "PLprocessUpdate => ", res, " }");
  return res;
}


// Process a vector of simultaneous updates (from a single WITH)
static Expr PLprocessUpdates(const CVC3::Expr& e,
			     const std::vector<CVC3::Expr>& updates,
			     size_t idx=0) {
  // Processed all the updates
  if(idx >= updates.size()) return e;
  return PLprocessUpdates(PLprocessUpdate(e, updates[idx]), updates, idx+1);
}



} // end of namespace CVC3

#define YYLTYPE_IS_TRIVIAL 1
#define YYMAXDEPTH 10485760
/* Prefer YYERROR_VERBOSE over %error-verbose to avoid errors in older bison */
#define YYERROR_VERBOSE 1


/* Enabling traces.  */
#ifndef YYDEBUG
# define YYDEBUG 1
#endif

/* Enabling verbose error messages.  */
#ifdef YYERROR_VERBOSE
# undef YYERROR_VERBOSE
# define YYERROR_VERBOSE 1
#else
# define YYERROR_VERBOSE 0
#endif

/* Enabling the token table.  */
#ifndef YYTOKEN_TABLE
# define YYTOKEN_TABLE 0
#endif

#if ! defined YYSTYPE && ! defined YYSTYPE_IS_DECLARED
typedef union YYSTYPE
#line 179 "PL.y"
{
  std::string *str;
  CVC3::Expr *node;
  std::vector<CVC3::Expr> *vec;
  int kind;
}
/* Line 187 of yacc.c.  */
#line 581 "parsePL.cpp"
	YYSTYPE;
# define yystype YYSTYPE /* obsolescent; will be withdrawn */
# define YYSTYPE_IS_DECLARED 1
# define YYSTYPE_IS_TRIVIAL 1
#endif



/* Copy the second part of user declarations.  */


/* Line 216 of yacc.c.  */
#line 594 "parsePL.cpp"

#ifdef short
# undef short
#endif

#ifdef YYTYPE_UINT8
typedef YYTYPE_UINT8 yytype_uint8;
#else
typedef unsigned char yytype_uint8;
#endif

#ifdef YYTYPE_INT8
typedef YYTYPE_INT8 yytype_int8;
#elif (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
typedef signed char yytype_int8;
#else
typedef short int yytype_int8;
#endif

#ifdef YYTYPE_UINT16
typedef YYTYPE_UINT16 yytype_uint16;
#else
typedef unsigned short int yytype_uint16;
#endif

#ifdef YYTYPE_INT16
typedef YYTYPE_INT16 yytype_int16;
#else
typedef short int yytype_int16;
#endif

#ifndef YYSIZE_T
# ifdef __SIZE_TYPE__
#  define YYSIZE_T __SIZE_TYPE__
# elif defined size_t
#  define YYSIZE_T size_t
# elif ! defined YYSIZE_T && (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
#  include <stddef.h> /* INFRINGES ON USER NAME SPACE */
#  define YYSIZE_T size_t
# else
#  define YYSIZE_T unsigned int
# endif
#endif

#define YYSIZE_MAXIMUM ((YYSIZE_T) -1)

#ifndef YY_
# if YYENABLE_NLS
#  if ENABLE_NLS
#   include <libintl.h> /* INFRINGES ON USER NAME SPACE */
#   define YY_(msgid) dgettext ("bison-runtime", msgid)
#  endif
# endif
# ifndef YY_
#  define YY_(msgid) msgid
# endif
#endif

/* Suppress unused-variable warnings by "using" E.  */
#if ! defined lint || defined __GNUC__
# define YYUSE(e) ((void) (e))
#else
# define YYUSE(e) /* empty */
#endif

/* Identity function, used to suppress warnings about constant conditions.  */
#ifndef lint
# define YYID(n) (n)
#else
#if (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
static int
YYID (int i)
#else
static int
YYID (i)
    int i;
#endif
{
  return i;
}
#endif

#if ! defined yyoverflow || YYERROR_VERBOSE

/* The parser invokes alloca or malloc; define the necessary symbols.  */

# ifdef YYSTACK_USE_ALLOCA
#  if YYSTACK_USE_ALLOCA
#   ifdef __GNUC__
#    define YYSTACK_ALLOC __builtin_alloca
#   elif defined __BUILTIN_VA_ARG_INCR
#    include <alloca.h> /* INFRINGES ON USER NAME SPACE */
#   elif defined _AIX
#    define YYSTACK_ALLOC __alloca
#   elif defined _MSC_VER
#    include <malloc.h> /* INFRINGES ON USER NAME SPACE */
#    define alloca _alloca
#   else
#    define YYSTACK_ALLOC alloca
#    if ! defined _ALLOCA_H && ! defined _STDLIB_H && (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
#     include <stdlib.h> /* INFRINGES ON USER NAME SPACE */
#     ifndef _STDLIB_H
#      define _STDLIB_H 1
#     endif
#    endif
#   endif
#  endif
# endif

# ifdef YYSTACK_ALLOC
   /* Pacify GCC's `empty if-body' warning.  */
#  define YYSTACK_FREE(Ptr) do { /* empty */; } while (YYID (0))
#  ifndef YYSTACK_ALLOC_MAXIMUM
    /* The OS might guarantee only one guard page at the bottom of the stack,
       and a page size can be as small as 4096 bytes.  So we cannot safely
       invoke alloca (N) if N exceeds 4096.  Use a slightly smaller number
       to allow for a few compiler-allocated temporary stack slots.  */
#   define YYSTACK_ALLOC_MAXIMUM 4032 /* reasonable circa 2006 */
#  endif
# else
#  define YYSTACK_ALLOC YYMALLOC
#  define YYSTACK_FREE YYFREE
#  ifndef YYSTACK_ALLOC_MAXIMUM
#   define YYSTACK_ALLOC_MAXIMUM YYSIZE_MAXIMUM
#  endif
#  if (defined __cplusplus && ! defined _STDLIB_H \
       && ! ((defined YYMALLOC || defined malloc) \
	     && (defined YYFREE || defined free)))
#   include <stdlib.h> /* INFRINGES ON USER NAME SPACE */
#   ifndef _STDLIB_H
#    define _STDLIB_H 1
#   endif
#  endif
#  ifndef YYMALLOC
#   define YYMALLOC malloc
#   if ! defined malloc && ! defined _STDLIB_H && (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
void *malloc (YYSIZE_T); /* INFRINGES ON USER NAME SPACE */
#   endif
#  endif
#  ifndef YYFREE
#   define YYFREE free
#   if ! defined free && ! defined _STDLIB_H && (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
void free (void *); /* INFRINGES ON USER NAME SPACE */
#   endif
#  endif
# endif
#endif /* ! defined yyoverflow || YYERROR_VERBOSE */


#if (! defined yyoverflow \
     && (! defined __cplusplus \
	 || (defined YYSTYPE_IS_TRIVIAL && YYSTYPE_IS_TRIVIAL)))

/* A type that is properly aligned for any stack member.  */
union yyalloc
{
  yytype_int16 yyss;
  YYSTYPE yyvs;
  };

/* The size of the maximum gap between one aligned stack and the next.  */
# define YYSTACK_GAP_MAXIMUM (sizeof (union yyalloc) - 1)

/* The size of an array large to enough to hold all stacks, each with
   N elements.  */
# define YYSTACK_BYTES(N) \
     ((N) * (sizeof (yytype_int16) + sizeof (YYSTYPE)) \
      + YYSTACK_GAP_MAXIMUM)

/* Copy COUNT objects from FROM to TO.  The source and destination do
   not overlap.  */
# ifndef YYCOPY
#  if defined __GNUC__ && 1 < __GNUC__
#   define YYCOPY(To, From, Count) \
      __builtin_memcpy (To, From, (Count) * sizeof (*(From)))
#  else
#   define YYCOPY(To, From, Count)		\
      do					\
	{					\
	  YYSIZE_T yyi;				\
	  for (yyi = 0; yyi < (Count); yyi++)	\
	    (To)[yyi] = (From)[yyi];		\
	}					\
      while (YYID (0))
#  endif
# endif

/* Relocate STACK from its old location to the new one.  The
   local variables YYSIZE and YYSTACKSIZE give the old and new number of
   elements in the stack, and YYPTR gives the new location of the
   stack.  Advance YYPTR to a properly aligned location for the next
   stack.  */
# define YYSTACK_RELOCATE(Stack)					\
    do									\
      {									\
	YYSIZE_T yynewbytes;						\
	YYCOPY (&yyptr->Stack, Stack, yysize);				\
	Stack = &yyptr->Stack;						\
	yynewbytes = yystacksize * sizeof (*Stack) + YYSTACK_GAP_MAXIMUM; \
	yyptr += yynewbytes / sizeof (*yyptr);				\
      }									\
    while (YYID (0))

#endif

/* YYFINAL -- State number of the termination state.  */
#define YYFINAL  202
/* YYLAST -- Last index in YYTABLE.  */
#define YYLAST   5727

/* YYNTOKENS -- Number of terminals.  */
#define YYNTOKENS  159
/* YYNNTS -- Number of nonterminals.  */
#define YYNNTS  92
/* YYNRULES -- Number of rules.  */
#define YYNRULES  290
/* YYNRULES -- Number of states.  */
#define YYNSTATES  686

/* YYTRANSLATE(YYLEX) -- Bison symbol number corresponding to YYLEX.  */
#define YYUNDEFTOK  2
#define YYMAXUTOK   401

#define YYTRANSLATE(YYX)						\
  ((unsigned int) (YYX) <= YYMAXUTOK ? yytranslate[YYX] : YYUNDEFTOK)

/* YYTRANSLATE[YYLEX] -- Bison symbol number corresponding to YYLEX.  */
static const yytype_uint8 yytranslate[] =
{
       0,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
     147,   154,     2,     2,   157,     2,   146,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,   155,   153,
       2,   142,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,   144,     2,   156,     2,    35,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,   145,     2,   158,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     1,     2,     3,     4,
       5,     6,     7,     8,     9,    10,    11,    12,    13,    14,
      15,    16,    17,    18,    19,    20,    21,    22,    23,    24,
      25,    26,    27,    28,    29,    30,    31,    32,    33,    34,
      36,    37,    38,    39,    40,    41,    42,    43,    44,    45,
      46,    47,    48,    49,    50,    51,    52,    53,    54,    55,
      56,    57,    58,    59,    60,    61,    62,    63,    64,    65,
      66,    67,    68,    69,    70,    71,    72,    73,    74,    75,
      76,    77,    78,    79,    80,    81,    82,    83,    84,    85,
      86,    87,    88,    89,    90,    91,    92,    93,    94,    95,
      96,    97,    98,    99,   100,   101,   102,   103,   104,   105,
     106,   107,   108,   109,   110,   111,   112,   113,   114,   115,
     116,   117,   118,   119,   120,   121,   122,   123,   124,   125,
     126,   127,   128,   129,   130,   131,   132,   133,   134,   135,
     136,   137,   138,   139,   140,   141,   143,   148,   149,   150,
     151,   152
};

#if YYDEBUG
/* YYPRHS[YYN] -- Index of the first RHS symbol of rule number YYN in
   YYRHS.  */
static const yytype_uint16 yyprhs[] =
{
       0,     0,     3,     6,     9,    12,    14,    16,    18,    20,
      22,    24,    26,    28,    30,    32,    34,    36,    38,    40,
      42,    44,    46,    48,    50,    52,    54,    56,    58,    60,
      62,    64,    69,    72,    75,    78,    80,    82,    85,    88,
      90,    93,    96,   100,   105,   109,   112,   114,   117,   120,
     123,   127,   130,   132,   135,   137,   139,   141,   143,   145,
     147,   149,   151,   153,   155,   157,   159,   161,   164,   166,
     169,   171,   174,   176,   179,   181,   184,   186,   189,   191,
     193,   196,   198,   201,   204,   209,   213,   216,   228,   230,
     232,   234,   236,   238,   240,   242,   244,   246,   248,   250,
     252,   254,   256,   258,   260,   264,   266,   268,   272,   274,
     278,   282,   284,   288,   290,   295,   297,   301,   305,   311,
     315,   321,   325,   327,   331,   335,   339,   343,   347,   352,
     356,   361,   368,   370,   372,   374,   379,   381,   383,   389,
     391,   393,   396,   398,   400,   403,   405,   409,   411,   413,
     415,   417,   419,   424,   429,   434,   438,   442,   446,   448,
     450,   452,   454,   456,   458,   460,   462,   464,   467,   470,
     473,   478,   482,   486,   490,   492,   494,   498,   502,   506,
     510,   518,   522,   526,   530,   534,   538,   543,   547,   551,
     555,   558,   565,   569,   573,   577,   581,   588,   595,   602,
     609,   616,   623,   630,   637,   644,   651,   658,   665,   672,
     679,   686,   693,   700,   707,   711,   720,   725,   732,   739,
     748,   755,   762,   769,   776,   783,   790,   797,   804,   809,
     818,   823,   827,   831,   835,   839,   845,   849,   855,   857,
     861,   867,   869,   872,   876,   878,   882,   884,   888,   890,
     893,   896,   901,   904,   908,   912,   919,   926,   934,   941,
     949,   956,   960,   962,   966,   970,   976,   978,   980,   984,
     988,   994,   999,  1001,  1003,  1007,  1011,  1017,  1022,  1026,
    1028,  1032,  1034,  1040,  1044,  1053,  1060,  1066,  1068,  1074,
    1078
};

/* YYRHS -- A `-1'-separated list of the rules' RHS.  */
static const yytype_int16 yyrhs[] =
{
     160,     0,    -1,   250,   153,    -1,   249,   153,    -1,   161,
     153,    -1,   153,    -1,    36,    -1,   163,    -1,   164,    -1,
     165,    -1,   166,    -1,   167,    -1,   168,    -1,   169,    -1,
     170,    -1,   171,    -1,   172,    -1,   173,    -1,   174,    -1,
     175,    -1,   176,    -1,   177,    -1,   178,    -1,   179,    -1,
     185,    -1,   183,    -1,   184,    -1,   181,    -1,   182,    -1,
     180,    -1,   162,    -1,    98,   147,   224,   154,    -1,    99,
     219,    -1,   100,   219,    -1,   101,   219,    -1,   101,    -1,
     102,    -1,   103,   219,    -1,   105,   187,    -1,   105,    -1,
     106,   187,    -1,   107,   187,    -1,   108,   187,   188,    -1,
     108,   187,    43,   188,    -1,   108,   187,   187,    -1,   104,
     187,    -1,   104,    -1,   109,   219,    -1,   110,   219,    -1,
     111,   191,    -1,   112,   186,   219,    -1,   113,   187,    -1,
     113,    -1,   114,   187,    -1,   115,    -1,   116,    -1,   117,
      -1,   118,    -1,   119,    -1,   120,    -1,   121,    -1,   122,
      -1,   123,    -1,   124,    -1,   125,    -1,   126,    -1,   127,
      -1,   128,   188,    -1,   128,    -1,   131,   188,    -1,   131,
      -1,   129,   188,    -1,   129,    -1,   132,   188,    -1,   132,
      -1,   130,   188,    -1,   130,    -1,   133,   188,    -1,   133,
      -1,   134,    -1,   135,   187,    -1,   135,    -1,   136,   186,
      -1,   137,   219,    -1,   138,   219,   155,   191,    -1,   139,
     219,   188,    -1,   140,   219,    -1,   141,   186,   155,   191,
     142,   219,   144,   186,    38,   219,   156,    -1,   148,    -1,
     149,    -1,   150,    -1,   152,    -1,   151,    -1,   186,    -1,
     192,    -1,   207,    -1,   201,    -1,   210,    -1,   214,    -1,
     205,    -1,   202,    -1,   245,    -1,   211,    -1,   209,    -1,
     147,   191,   154,    -1,   191,    -1,   208,    -1,     7,   195,
      10,    -1,   196,    -1,   195,   157,   196,    -1,   186,   142,
     197,    -1,   198,    -1,   197,    75,   198,    -1,   186,    -1,
     186,   147,   199,   154,    -1,   200,    -1,   199,   157,   200,
      -1,   186,   155,   191,    -1,   144,   191,    72,   191,   156,
      -1,   191,    72,   191,    -1,   147,   206,   154,    72,   191,
      -1,    68,   203,    69,    -1,   204,    -1,   203,   157,   204,
      -1,   186,   155,   191,    -1,   144,   206,   156,    -1,   191,
     157,   191,    -1,   206,   157,   191,    -1,     5,   191,    22,
     191,    -1,   145,   218,   158,    -1,    26,   147,   219,   154,
      -1,    26,   147,   219,   157,   219,   154,    -1,     6,    -1,
     212,    -1,   213,    -1,    27,   147,   188,   154,    -1,    24,
      -1,    25,    -1,   144,   215,    37,   216,   156,    -1,    35,
      -1,   188,    -1,    43,   188,    -1,    35,    -1,   188,    -1,
      43,   188,    -1,   186,    -1,   186,   157,   217,    -1,   217,
      -1,   186,    -1,   188,    -1,   189,    -1,   190,    -1,   219,
     147,   224,   154,    -1,    18,   147,   224,   154,    -1,   219,
     144,   219,   156,    -1,   219,   146,   186,    -1,   219,   146,
     188,    -1,   219,    31,   228,    -1,   231,    -1,   232,    -1,
     241,    -1,   233,    -1,   234,    -1,   237,    -1,   222,    -1,
      29,    -1,    13,    -1,    43,   219,    -1,    20,   219,    -1,
      21,   219,    -1,    33,   147,   219,   154,    -1,   219,   142,
     219,    -1,   219,    39,   219,    -1,   219,    32,   219,    -1,
     221,    -1,   220,    -1,   219,    40,   219,    -1,   219,    41,
     219,    -1,   219,    42,   219,    -1,   219,    43,   219,    -1,
     219,    44,   147,   219,   157,   219,   154,    -1,   219,    44,
     219,    -1,   219,    45,   219,    -1,   219,    46,   219,    -1,
     219,    51,   219,    -1,   219,    52,   219,    -1,    53,   147,
     219,   154,    -1,   219,    49,   219,    -1,   219,    50,   219,
      -1,   147,   219,   154,    -1,    73,   219,    -1,   219,   144,
     150,   155,   150,   156,    -1,   219,    74,   219,    -1,   219,
      75,   219,    -1,   219,    54,   150,    -1,   219,    55,   150,
      -1,    76,   147,   219,   157,   219,   154,    -1,    77,   147,
     219,   157,   219,   154,    -1,    78,   147,   219,   157,   219,
     154,    -1,    79,   147,   219,   157,   219,   154,    -1,    80,
     147,   219,   157,   219,   154,    -1,    89,   147,   219,   157,
     150,   154,    -1,    90,   147,   219,   157,   150,   154,    -1,
      91,   147,   219,   157,   150,   154,    -1,    92,   147,   219,
     157,   150,   154,    -1,    93,   147,   219,   157,   150,   154,
      -1,    85,   147,   219,   157,   219,   154,    -1,    86,   147,
     219,   157,   219,   154,    -1,    87,   147,   219,   157,   219,
     154,    -1,    88,   147,   219,   157,   219,   154,    -1,    94,
     147,   219,   157,   219,   154,    -1,    95,   147,   219,   157,
     219,   154,    -1,    96,   147,   219,   157,   219,   154,    -1,
      97,   147,   219,   157,   219,   154,    -1,   219,    81,   219,
      -1,    83,   147,   219,   157,   150,   157,   150,   154,    -1,
      82,   147,   219,   154,    -1,    84,   147,   219,   157,   150,
     154,    -1,    56,   147,   150,   157,   224,   154,    -1,    57,
     147,   150,   157,   219,   157,   219,   154,    -1,    58,   147,
     219,   157,   219,   154,    -1,    59,   147,   219,   157,   219,
     154,    -1,    60,   147,   219,   157,   219,   154,    -1,    61,
     147,   219,   157,   219,   154,    -1,    62,   147,   219,   157,
     219,   154,    -1,    63,   147,   219,   157,   219,   154,    -1,
      64,   147,   219,   157,   219,   154,    -1,    65,   147,   219,
     157,   219,   154,    -1,    66,   147,   219,   154,    -1,    67,
     147,   150,   157,   219,   157,   219,   154,    -1,     3,   147,
     224,   154,    -1,   220,     4,   219,    -1,   219,     4,   219,
      -1,   221,    23,   219,    -1,   219,    23,   219,    -1,    16,
     219,    28,   219,   223,    -1,     8,   219,    11,    -1,     9,
     219,    28,   219,   223,    -1,   219,    -1,   224,   157,   219,
      -1,    34,   147,   224,   154,   155,    -1,   225,    -1,   226,
     225,    -1,   229,    38,   219,    -1,   227,    -1,   228,   157,
     227,    -1,   230,    -1,   144,   219,   156,    -1,   186,    -1,
     146,   186,    -1,   146,   188,    -1,   230,   144,   219,   156,
      -1,   230,   186,    -1,   230,   146,   186,    -1,   230,   146,
     188,    -1,    17,   147,   247,   154,   155,   219,    -1,    14,
     147,   247,   154,   155,   219,    -1,    14,   147,   247,   154,
     155,   226,   219,    -1,    12,   147,   247,   154,   155,   219,
      -1,    12,   147,   247,   154,   155,   226,   219,    -1,     5,
     147,   246,   154,   155,   219,    -1,    70,   235,    71,    -1,
     236,    -1,   235,   157,   236,    -1,   186,    38,   219,    -1,
     147,   224,   157,   219,   154,    -1,   239,    -1,   240,    -1,
     239,   157,   240,    -1,   186,   142,   219,    -1,   186,   155,
     191,   142,   219,    -1,    19,   238,    15,   219,    -1,   243,
      -1,   244,    -1,   243,   157,   244,    -1,   186,   142,   219,
      -1,   186,   155,    30,   142,   219,    -1,    19,   242,    15,
     191,    -1,   218,   155,   191,    -1,   246,    -1,   247,   157,
     246,    -1,   247,    -1,   186,   155,   191,   142,   219,    -1,
     186,   155,   191,    -1,   186,   147,   248,   154,   155,   191,
     142,   219,    -1,   186,   147,   248,   154,   155,   191,    -1,
     186,   157,   218,   155,   191,    -1,   194,    -1,   186,   155,
      30,   142,   193,    -1,   186,   155,    30,    -1,   186,   157,
     218,   155,    30,    -1
};

/* YYRLINE[YYN] -- source line where rule number YYN was defined.  */
static const yytype_uint16 yyrline[] =
{
       0,   402,   402,   408,   414,   419,   424,   432,   433,   434,
     435,   436,   437,   438,   439,   440,   441,   442,   443,   444,
     445,   446,   447,   448,   449,   450,   451,   452,   453,   454,
     455,   458,   465,   472,   476,   480,   483,   486,   491,   495,
     499,   503,   508,   513,   520,   526,   530,   535,   541,   545,
     551,   558,   562,   567,   573,   576,   579,   582,   585,   588,
     591,   594,   599,   602,   605,   608,   611,   615,   619,   622,
     626,   630,   634,   637,   641,   645,   649,   652,   656,   659,
     663,   667,   671,   676,   681,   687,   693,   698,   713,   719,
     725,   732,   741,   752,   753,   756,   757,   758,   759,   760,
     761,   762,   763,   764,   765,   768,   769,   772,   781,   787,
     795,   803,   809,   817,   822,   830,   836,   844,   852,   858,
     867,   875,   882,   889,   897,   905,   912,   920,   936,   944,
     953,   958,   966,   970,   971,   974,   981,   987,   992,  1000,
    1004,  1005,  1012,  1016,  1017,  1025,  1031,  1039,  1049,  1050,
    1051,  1052,  1053,  1062,  1067,  1073,  1079,  1085,  1091,  1092,
    1093,  1095,  1097,  1098,  1099,  1101,  1105,  1110,  1121,  1126,
    1131,  1136,  1142,  1148,  1154,  1159,  1164,  1170,  1176,  1182,
    1188,  1196,  1202,  1208,  1226,  1232,  1238,  1243,  1249,  1255,
    1259,  1264,  1273,  1279,  1285,  1292,  1299,  1305,  1311,  1317,
    1323,  1329,  1335,  1341,  1347,  1353,  1359,  1365,  1371,  1377,
    1384,  1390,  1396,  1402,  1408,  1414,  1423,  1428,  1439,  1448,
    1456,  1463,  1470,  1477,  1484,  1491,  1498,  1505,  1512,  1517,
    1525,  1531,  1538,  1549,  1556,  1565,  1580,  1586,  1598,  1604,
    1613,  1618,  1624,  1632,  1640,  1646,  1653,  1660,  1666,  1672,
    1678,  1684,  1690,  1696,  1702,  1710,  1719,  1727,  1737,  1746,
    1757,  1766,  1774,  1780,  1788,  1796,  1806,  1812,  1817,  1825,
    1831,  1840,  1848,  1854,  1859,  1867,  1873,  1881,  1889,  1899,
    1905,  1913,  1920,  1928,  1935,  1949,  1961,  1971,  1972,  1978,
    1983
};
#endif

#if YYDEBUG || YYERROR_VERBOSE || YYTOKEN_TABLE
/* YYTNAME[SYMBOL-NUM] -- String name of the symbol SYMBOL-NUM.
   First, the terminals, then, starting at YYNTOKENS, nonterminals.  */
static const char *const yytname[] =
{
  "$end", "error", "$undefined", "\"DISTINCT\"", "\"AND\"", "\"ARRAY\"",
  "\"BOOLEAN\"", "\"DATATYPE\"", "\"ELSE\"", "\"ELSIF\"", "\"END\"",
  "\"ENDIF\"", "\"EXISTS\"", "\"FALSE\"", "\"FORALL\"", "\"IN\"", "\"IF\"",
  "\"LAMBDA\"", "\"SIMULATE\"", "\"LET\"", "\"NOT\"", "\"IS_INTEGER\"",
  "\"OF\"", "\"OR\"", "\"REAL\"", "\"INT\"", "\"SUBTYPE\"",
  "\"BITVECTOR\"", "\"THEN\"", "\"TRUE\"", "\"TYPE\"", "\"WITH\"",
  "\"XOR\"", "\"TCC\"", "\"PATTERN\"", "'_'", "DONE_TOK", "\"..\"",
  "\":=\"", "\"/=\"", "\"=>\"", "\"<=>\"", "\"+\"", "\"-\"", "\"*\"",
  "\"^\"", "\"/\"", "\"MOD\"", "\"DIV\"", "\"<\"", "\"<=\"", "\">\"",
  "\">=\"", "\"FLOOR\"", "\"<<\"", "\">>\"", "\"BVPLUS\"", "\"BVSUB\"",
  "\"BVUDIV\"", "\"BVSDIV\"", "\"BVUREM\"", "\"BVSREM\"", "\"BVSMOD\"",
  "\"BVSHL\"", "\"BVASHR\"", "\"BVLSHR\"", "\"BVUMINUS\"", "\"BVMULT\"",
  "\"[#\"", "\"#]\"", "\"(#\"", "\"#)\"", "\"->\"", "\"~\"", "\"&\"",
  "\"|\"", "\"BVXOR\"", "\"BVNAND\"", "\"BVNOR\"", "\"BVCOMP\"",
  "\"BVXNOR\"", "\"@\"", "\"BVTOINT\"", "\"INTTOBV\"", "\"BOOLEXTRACT\"",
  "\"BVLT\"", "\"BVGT\"", "\"BVLE\"", "\"BVGE\"", "\"SX\"",
  "\"BVZEROEXTEND\"", "\"BVREPEAT\"", "\"BVROTL\"", "\"BVROTR\"",
  "\"BVSLT\"", "\"BVSGT\"", "\"BVSLE\"", "\"BVSGE\"",
  "\"ARITH_VAR_ORDER\"", "\"ASSERT\"", "\"QUERY\"", "\"CHECKSAT\"",
  "\"CONTINUE\"", "\"RESTART\"", "\"HELP\"", "\"DBG\"", "\"TRACE\"",
  "\"UNTRACE\"", "\"OPTION\"", "\"TRANSFORM\"", "\"PRINT\"",
  "\"PRINT_TYPE\"", "\"CALL\"", "\"ECHO\"", "\"INCLUDE\"",
  "\"DUMP_PROOF\"", "\"DUMP_ASSUMPTIONS\"", "\"DUMP_SIG\"", "\"DUMP_TCC\"",
  "\"DUMP_TCC_ASSUMPTIONS\"", "\"DUMP_TCC_PROOF\"", "\"DUMP_CLOSURE\"",
  "\"DUMP_CLOSURE_PROOF\"", "\"WHERE\"", "\"ASSERTIONS\"",
  "\"ASSUMPTIONS\"", "\"COUNTEREXAMPLE\"", "\"COUNTERMODEL\"", "\"PUSH\"",
  "\"POP\"", "\"POPTO\"", "\"PUSH_SCOPE\"", "\"POP_SCOPE\"",
  "\"POPTO_SCOPE\"", "\"RESET\"", "\"CONTEXT\"", "\"FORGET\"",
  "\"GET_TYPE\"", "\"CHECK_TYPE\"", "\"GET_CHILD\"", "\"GET_OP\"",
  "\"SUBSTITUTE\"", "'='", "UMINUS_TOK", "'['", "'{'", "'.'", "'('",
  "ID_TOK", "STRINGLIT_TOK", "NUMERAL_TOK", "HEX_TOK", "BINARY_TOK", "';'",
  "')'", "':'", "']'", "','", "'}'", "$accept", "cmd", "other_cmd",
  "Arith_Var_Order", "Assert", "Query", "Dbg", "Trace", "Option", "Help",
  "Transform", "Print", "Call", "Echo", "Include", "DumpCommand", "Where",
  "Push", "Pop", "PopTo", "Context", "Forget", "Get_Type", "Check_Type",
  "Get_Child", "Get_Op", "Substitute", "Identifier", "StringLiteral",
  "Numeral", "Binary", "Hex", "Type", "TypeNotIdentifier", "TypeDef",
  "DataType", "SingleDataTypes", "SingleDataType", "Constructors",
  "Constructor", "VarDecls", "VarDecl", "FunctionType", "RecordType",
  "FieldDecls", "FieldDecl", "TupleType", "TypeList", "ArrayType",
  "ScalarType", "SubType", "BasicType", "BitvectorType", "Real", "Int",
  "SubrangeType", "LeftBound", "RightBound", "reverseIDs", "IDs", "Expr",
  "AndExpr", "OrExpr", "Conditional", "ElseRest", "Exprs", "Pattern",
  "Patterns", "Update", "Updates", "UpdatePositionNode", "UpdatePosition",
  "Lambda", "QuantExpr", "ArrayLiteral", "RecordLiteral", "RecordEntries",
  "RecordEntry", "TupleLiteral", "LetDeclsNode", "LetDecls", "LetDecl",
  "LetExpr", "TypeLetDeclsNode", "TypeLetDecls", "TypeLetDecl",
  "TypeLetExpr", "BoundVarDecl", "BoundVarDecls", "BoundVarDeclNode",
  "ConstDecl", "TypeDecl", 0
};
#endif

# ifdef YYPRINT
/* YYTOKNUM[YYLEX-NUM] -- Internal token number corresponding to
   token YYLEX-NUM.  */
static const yytype_uint16 yytoknum[] =
{
       0,   256,   257,   258,   259,   260,   261,   262,   263,   264,
     265,   266,   267,   268,   269,   270,   271,   272,   273,   274,
     275,   276,   277,   278,   279,   280,   281,   282,   283,   284,
     285,   286,   287,   288,   289,    95,   290,   291,   292,   293,
     294,   295,   296,   297,   298,   299,   300,   301,   302,   303,
     304,   305,   306,   307,   308,   309,   310,   311,   312,   313,
     314,   315,   316,   317,   318,   319,   320,   321,   322,   323,
     324,   325,   326,   327,   328,   329,   330,   331,   332,   333,
     334,   335,   336,   337,   338,   339,   340,   341,   342,   343,
     344,   345,   346,   347,   348,   349,   350,   351,   352,   353,
     354,   355,   356,   357,   358,   359,   360,   361,   362,   363,
     364,   365,   366,   367,   368,   369,   370,   371,   372,   373,
     374,   375,   376,   377,   378,   379,   380,   381,   382,   383,
     384,   385,   386,   387,   388,   389,   390,   391,   392,   393,
     394,   395,    61,   396,    91,   123,    46,    40,   397,   398,
     399,   400,   401,    59,    41,    58,    93,    44,   125
};
# endif

/* YYR1[YYN] -- Symbol number of symbol that rule YYN derives.  */
static const yytype_uint8 yyr1[] =
{
       0,   159,   160,   160,   160,   160,   160,   161,   161,   161,
     161,   161,   161,   161,   161,   161,   161,   161,   161,   161,
     161,   161,   161,   161,   161,   161,   161,   161,   161,   161,
     161,   162,   163,   164,   164,   164,   164,   164,   165,   165,
     166,   166,   167,   167,   167,   168,   168,   169,   170,   170,
     171,   172,   172,   173,   174,   174,   174,   174,   174,   174,
     174,   174,   175,   175,   175,   175,   175,   176,   176,   176,
     176,   177,   177,   177,   177,   178,   178,   178,   178,   178,
     179,   179,   180,   181,   182,   183,   184,   185,   186,   187,
     188,   189,   190,   191,   191,   192,   192,   192,   192,   192,
     192,   192,   192,   192,   192,   193,   193,   194,   195,   195,
     196,   197,   197,   198,   198,   199,   199,   200,   201,   201,
     201,   202,   203,   203,   204,   205,   206,   206,   207,   208,
     209,   209,   210,   210,   210,   211,   212,   213,   214,   215,
     215,   215,   216,   216,   216,   217,   217,   218,   219,   219,
     219,   219,   219,   219,   219,   219,   219,   219,   219,   219,
     219,   219,   219,   219,   219,   219,   219,   219,   219,   219,
     219,   219,   219,   219,   219,   219,   219,   219,   219,   219,
     219,   219,   219,   219,   219,   219,   219,   219,   219,   219,
     219,   219,   219,   219,   219,   219,   219,   219,   219,   219,
     219,   219,   219,   219,   219,   219,   219,   219,   219,   219,
     219,   219,   219,   219,   219,   219,   219,   219,   219,   219,
     219,   219,   219,   219,   219,   219,   219,   219,   219,   219,
     219,   220,   220,   221,   221,   222,   223,   223,   224,   224,
     225,   226,   226,   227,   228,   228,   229,   230,   230,   230,
     230,   230,   230,   230,   230,   231,   232,   232,   232,   232,
     233,   234,   235,   235,   236,   237,   238,   239,   239,   240,
     240,   241,   242,   243,   243,   244,   244,   245,   246,   247,
     247,   248,   249,   249,   249,   249,   249,   250,   250,   250,
     250
};

/* YYR2[YYN] -- Number of symbols composing right hand side of rule YYN.  */
static const yytype_uint8 yyr2[] =
{
       0,     2,     2,     2,     2,     1,     1,     1,     1,     1,
       1,     1,     1,     1,     1,     1,     1,     1,     1,     1,
       1,     1,     1,     1,     1,     1,     1,     1,     1,     1,
       1,     4,     2,     2,     2,     1,     1,     2,     2,     1,
       2,     2,     3,     4,     3,     2,     1,     2,     2,     2,
       3,     2,     1,     2,     1,     1,     1,     1,     1,     1,
       1,     1,     1,     1,     1,     1,     1,     2,     1,     2,
       1,     2,     1,     2,     1,     2,     1,     2,     1,     1,
       2,     1,     2,     2,     4,     3,     2,    11,     1,     1,
       1,     1,     1,     1,     1,     1,     1,     1,     1,     1,
       1,     1,     1,     1,     3,     1,     1,     3,     1,     3,
       3,     1,     3,     1,     4,     1,     3,     3,     5,     3,
       5,     3,     1,     3,     3,     3,     3,     3,     4,     3,
       4,     6,     1,     1,     1,     4,     1,     1,     5,     1,
       1,     2,     1,     1,     2,     1,     3,     1,     1,     1,
       1,     1,     4,     4,     4,     3,     3,     3,     1,     1,
       1,     1,     1,     1,     1,     1,     1,     2,     2,     2,
       4,     3,     3,     3,     1,     1,     3,     3,     3,     3,
       7,     3,     3,     3,     3,     3,     4,     3,     3,     3,
       2,     6,     3,     3,     3,     3,     6,     6,     6,     6,
       6,     6,     6,     6,     6,     6,     6,     6,     6,     6,
       6,     6,     6,     6,     3,     8,     4,     6,     6,     8,
       6,     6,     6,     6,     6,     6,     6,     6,     4,     8,
       4,     3,     3,     3,     3,     5,     3,     5,     1,     3,
       5,     1,     2,     3,     1,     3,     1,     3,     1,     2,
       2,     4,     2,     3,     3,     6,     6,     7,     6,     7,
       6,     3,     1,     3,     3,     5,     1,     1,     3,     3,
       5,     4,     1,     1,     3,     3,     5,     4,     3,     1,
       3,     1,     5,     3,     8,     6,     5,     1,     5,     3,
       5
};

/* YYDEFACT[STATE-NAME] -- Default rule to reduce with in state
   STATE-NUM when YYTABLE doesn't specify something else to do.  Zero
   means the default is an error.  */
static const yytype_uint16 yydefact[] =
{
       0,     0,     6,     0,     0,     0,    35,    36,     0,    46,
      39,     0,     0,     0,     0,     0,     0,     0,    52,     0,
      54,    55,    56,    57,    58,    59,    60,    61,    62,    63,
      64,    65,    66,    68,    72,    76,    70,    74,    78,    79,
      81,     0,     0,     0,     0,     0,     0,    88,     5,     0,
       0,    30,     7,     8,     9,    10,    11,    12,    13,    14,
      15,    16,    17,    18,    19,    20,    21,    22,    23,    29,
      27,    28,    25,    26,    24,     0,   287,     0,     0,     0,
       0,   108,     0,     0,     0,     0,   166,     0,     0,     0,
       0,     0,     0,     0,   165,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,    90,    92,    91,   148,   149,   150,
     151,    32,   175,   174,   164,   158,   159,   161,   162,   163,
     160,    33,    34,    37,    89,    45,    38,    40,    41,     0,
      47,    48,     0,   132,     0,   136,   137,     0,     0,     0,
       0,     0,    93,    49,    94,    96,   100,    99,    95,   103,
      97,   102,   133,   134,    98,   101,     0,    51,    53,    67,
      71,    75,    69,    73,    77,    80,    82,    83,     0,     0,
      86,     0,     1,     4,     0,     0,     0,     3,     2,     0,
     107,     0,   238,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,   266,   267,   168,   169,     0,   167,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,   262,   190,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,   238,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,    44,    42,     0,
       0,     0,   272,   273,     0,     0,     0,     0,   122,   139,
       0,   140,     0,     0,     0,     0,     0,     0,    50,     0,
      85,     0,   145,   147,     0,   279,   281,     0,   289,   283,
       0,   113,   110,   111,   109,    31,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,   261,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,   189,     0,   232,   234,
       0,     0,   248,   244,   157,     0,   246,   173,   172,   176,
     177,   178,   179,     0,   181,   182,   183,   187,   188,   184,
     185,   194,   195,   192,   193,   214,   171,    90,     0,   155,
     156,     0,   231,   233,    43,     0,     0,     0,     0,     0,
       0,     0,     0,   121,     0,   141,     0,     0,   125,     0,
       0,   104,     0,   119,    84,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,   239,   230,     0,     0,     0,
       0,     0,   153,   269,     0,   271,   268,   170,   186,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,   228,
       0,   264,   263,     0,     0,     0,     0,     0,   216,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,   239,     0,   249,   250,     0,     0,
       0,     0,   252,     0,     0,   154,   152,   128,   275,     0,
     277,   274,   130,     0,   135,   124,   123,   119,   126,   127,
     142,     0,   143,     0,     0,     0,   146,   278,   280,     0,
       0,   105,   288,   106,   282,   290,   286,     0,     0,   115,
     112,     0,     0,     0,     0,     0,   235,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
     265,   247,   245,   243,     0,   253,   254,     0,     0,     0,
       0,   118,   144,   138,   120,     0,   285,     0,     0,   114,
       0,   260,     0,   258,   241,     0,   256,     0,     0,     0,
     255,   270,   218,     0,   220,   221,   222,   223,   224,   225,
     226,   227,     0,   196,   197,   198,   199,   200,     0,   217,
     206,   207,   208,   209,   201,   202,   203,   204,   205,   210,
     211,   212,   213,   251,     0,   191,   276,   131,     0,     0,
     129,   117,   116,     0,   259,   242,   257,   236,     0,     0,
       0,     0,   180,   148,   284,     0,     0,   219,   229,   215,
       0,     0,   237,     0,   240,    87
};

/* YYDEFGOTO[NTERM-NUM].  */
static const yytype_int16 yydefgoto[] =
{
      -1,    49,    50,    51,    52,    53,    54,    55,    56,    57,
      58,    59,    60,    61,    62,    63,    64,    65,    66,    67,
      68,    69,    70,    71,    72,    73,    74,   137,   155,   138,
     139,   140,   173,   174,   542,    76,    80,    81,   332,   333,
     548,   549,   175,   176,   307,   308,   177,   313,   178,   543,
     179,   180,   181,   182,   183,   184,   314,   533,   323,   324,
     212,   142,   143,   144,   556,   268,   614,   615,   393,   394,
     395,   396,   145,   146,   147,   148,   243,   244,   149,   222,
     223,   224,   150,   301,   302,   303,   185,   325,   326,   327,
      77,    78
};

/* YYPACT[STATE-NUM] -- Index in YYTABLE of the portion describing
   STATE-NUM.  */
#define YYPACT_NINF -472
static const yytype_int16 yypact[] =
{
    4948,  -122,  -472,  -120,  4747,  4747,  4747,  -472,  4747,   -97,
     -97,   -97,   -97,   -97,  4747,  4747,   620,  -122,   -97,   -97,
    -472,  -472,  -472,  -472,  -472,  -472,  -472,  -472,  -472,  -472,
    -472,  -472,  -472,   -92,   -92,   -92,   -92,   -92,   -92,  -472,
     -97,  -122,  4747,  4747,  4747,  4747,  -122,  -472,  -472,    63,
     -91,  -472,  -472,  -472,  -472,  -472,  -472,  -472,  -472,  -472,
    -472,  -472,  -472,  -472,  -472,  -472,  -472,  -472,  -472,  -472,
    -472,  -472,  -472,  -472,  -472,   -17,  -472,   -66,   -32,   -70,
      -2,  -472,  4747,     6,    11,    18,  -472,    23,  4747,    52,
      53,  -122,  4747,  4747,  -472,    54,  4747,    57,    58,    60,
      65,    69,    71,    74,    77,    79,    80,    90,    91,    94,
    -122,  4747,   116,   117,   120,   134,   135,   141,   149,   150,
     151,   152,   154,   156,   157,   158,   159,   163,   165,   166,
     167,   168,   169,  4747,  -472,  -472,  -472,  -472,  -472,  -472,
    -472,  5365,  -472,  -472,  -472,  -472,  -472,  -472,  -472,  -472,
    -472,  5365,  5365,  5365,  -472,  -472,  -472,  -472,  -472,   -37,
    5365,  5365,   620,  -472,  -122,  -472,  -472,   170,   171,  -122,
      42,   620,  -472,    78,  -472,  -472,  -472,  -472,  -472,  -472,
    -472,  -472,  -472,  -472,  -472,  -472,  4747,  -472,  -472,  -472,
    -472,  -472,  -472,  -472,  -472,  -472,  -472,  5365,  2736,  5086,
    5365,   -10,  -472,  -472,  -122,   425,  -122,  -472,  -472,  -122,
    -472,  -122,  5365,  -111,  4747,  -122,  -122,  -122,  5203,  -122,
    4747,  -126,   195,   164,  -472,  5474,    28,  4747,    62,  4747,
     173,   174,  4747,  4747,  4747,  4747,  4747,  4747,  4747,  4747,
    4747,   175,   282,   -49,  -472,    16,  4747,  4747,  4747,  4747,
    4747,  4747,  4747,  4747,  4747,  4747,  4747,  4747,  4747,  4747,
    4747,  4747,  4747,  4747,  4747,  4747,  4747,  2792,   179,  4747,
    4747,    20,  4747,  4747,  4747,  4747,  4747,  4747,  4847,  4747,
    4747,  4747,  4747,  4747,  4747,   177,   188,  4747,  4747,  4747,
    4747,  4947,     9,  4747,  4747,  4747,   -92,  -472,  -472,     3,
     -22,   328,   190,  -472,  4747,   -92,   193,   -46,  -472,  -472,
     -92,  -472,   -48,  -138,   308,   -35,  -100,   620,  5365,   620,
    -472,   620,   192,  -472,   198,  -472,   199,   196,   215,   -44,
     204,   213,   287,  -472,  -472,  -472,  4747,   -81,   209,   -76,
     -23,  4747,   -15,    24,  4747,   620,  4747,  -122,  2854,  2909,
     207,   208,   861,   939,   992,  1048,  1101,  1157,  1210,  1266,
    2971,   214,  4747,  -472,  -122,  1319,  1375,  1428,  1484,  1537,
    3026,  1593,  1646,  1702,  1755,  1811,  1864,  1920,  1973,  2029,
    2082,  2138,  2191,  2247,  2300,  2356,  -472,  4747,  5474,   365,
    4747,     9,  -472,  -472,   216,   332,    25,   365,  5527,    51,
      51,     5,     5,  4747,    73,   280,    73,  5580,  5580,  5580,
    5580,  -472,  -472,    16,   148,   254,  5527,   211,  2518,  -472,
    -472,    26,  5474,   365,  -472,   620,  4747,   342,   620,  -122,
     677,   220,   620,  -472,  -122,  -472,   620,   620,  -472,   620,
     -26,  -472,   303,  -472,    78,   -28,  -122,   620,  -122,   221,
     518,  4747,   591,  -122,  -122,  5365,  -472,   222,   223,   224,
    5139,   225,  -472,  5365,   -27,  5365,  -472,  -472,  -472,  4747,
    4747,  4747,  4747,  4747,  4747,  4747,  4747,  4747,  4747,  -472,
    4747,  5365,  -472,  4747,  4747,  4747,  4747,  4747,  -472,   231,
     232,  4747,  4747,  4747,  4747,   234,   235,   237,   239,   241,
    4747,  4747,  4747,  4747,  3088,  2574,  -472,  -472,    20,  4747,
    4747,     9,  -472,   806,   243,  -472,  -472,    78,  5365,   252,
      78,  -472,  -472,  4747,  -472,    78,  -472,   246,    78,    78,
    -472,   -92,  -472,   247,   620,  4747,  -472,    78,  -472,   620,
    -122,    78,  -472,  -472,  5365,  -472,    78,   240,    30,  -472,
    -472,  4747,  4647,  4647,  4747,  4747,  -472,  4747,  4747,    31,
    2409,  3143,  3205,  3260,  3322,  3377,  3439,  3494,  3556,  2465,
    3611,  3673,  3728,  3790,  3845,   248,   258,  3907,  3962,  4024,
    4079,   259,   264,   267,   269,   271,  4141,  4196,  4258,  4313,
    -472,  -472,  -472,  5365,  2627,  -472,  -472,  4747,   250,  4747,
    4375,  -472,  -472,  -472,  -472,  5421,   -19,   274,   620,  -472,
    -122,  5365,   288,  5365,  -472,  4647,  5365,  4647,  5256,  5312,
    5365,  5365,  -472,  4747,  -472,  -472,  -472,  -472,  -472,  -472,
    -472,  -472,  4747,  -472,  -472,  -472,  -472,  -472,   279,  -472,
    -472,  -472,  -472,  -472,  -472,  -472,  -472,  -472,  -472,  -472,
    -472,  -472,  -472,  -472,  4430,  -472,  5365,  -472,  4947,  4747,
    -472,    78,  -472,  4747,  5365,  -472,  5365,  -472,  4747,  4492,
    4547,   284,  -472,   396,  5365,    37,  5139,  -472,  -472,  -472,
    4747,   281,  -472,  2683,  -472,  -472
};

/* YYPGOTO[NTERM-NUM].  */
static const yytype_int16 yypgoto[] =
{
    -472,  -472,  -472,  -472,  -472,  -472,  -472,  -472,  -472,  -472,
    -472,  -472,  -472,  -472,  -472,  -472,  -472,  -472,  -472,  -472,
    -472,  -472,  -472,  -472,  -472,  -472,  -472,   351,     2,    -3,
    -472,  -472,  -106,  -472,  -472,  -472,  -472,   230,  -472,   -11,
    -472,  -165,  -472,  -472,  -472,    14,  -472,   283,  -472,  -472,
    -472,  -472,  -472,  -472,  -472,  -472,  -472,  -472,     7,  -201,
      -4,  -472,  -472,  -472,  -220,   -79,  -471,   -96,   -50,  -472,
    -472,  -472,  -472,  -472,  -472,  -472,  -472,    95,  -472,  -472,
    -472,   113,  -472,  -472,  -472,    33,  -472,  -208,   -40,  -472,
    -472,  -472
};

/* YYTABLE[YYPACT[STATE-NUM]].  What to do in state STATE-NUM.  If
   positive, shift that token.  If negative, reduce the rule which
   number is the opposite.  If zero, do what YYDEFACT says.
   If YYTABLE_NINF, syntax error.  */
#define YYTABLE_NINF -1
static const yytype_int16 yytable[] =
{
     141,   151,   152,   213,   153,   330,   296,   338,   210,   530,
     160,   161,   156,   157,   158,   159,   344,   531,   438,   439,
     187,   188,   363,   433,   436,   425,    47,    82,   317,   345,
     189,   190,   191,   192,   193,   194,   271,   317,   197,   198,
     199,   200,   195,   335,   317,   317,   336,   162,   163,   278,
     279,   280,   154,   317,   442,   269,   299,   439,   134,   285,
     286,   164,   203,   202,   312,   315,   165,   166,   167,   168,
     285,   286,   209,   456,   270,   317,   336,   309,   458,   287,
     288,   448,   271,   272,   218,   310,   289,   207,   225,   226,
     273,   274,   228,   276,   277,   278,   279,   280,   451,   329,
     281,   282,   283,   284,   271,   285,   286,   245,   364,   437,
     169,   434,   154,   134,   535,   558,   285,   286,   279,   441,
     426,   208,   437,   659,   134,   287,   288,   285,   286,   267,
     204,   459,   289,   427,   448,   337,   287,   288,   205,   461,
     206,   343,   448,   289,   665,   321,   665,   287,   288,   291,
     317,   292,   293,   214,   289,   211,   298,    47,   215,   134,
     291,   297,   292,   293,   390,   216,   391,   311,    47,   510,
     217,   511,   291,    47,   292,   293,   339,   340,   462,   342,
     516,   336,   318,   336,   609,   622,   170,   610,   336,   171,
      47,   681,   134,   290,   336,   291,   320,   292,   293,   219,
     220,   227,   285,   286,   229,   230,   291,   231,   292,   293,
     346,   443,   232,   444,   421,   445,   233,   291,   234,   292,
     293,   235,   287,   348,   236,   349,   237,   238,   352,   353,
     354,   355,   356,   357,   358,   359,   360,   239,   240,   464,
     538,   241,   365,   366,   367,   368,   369,   370,   371,   372,
     373,   374,   375,   376,   377,   378,   379,   380,   381,   382,
     383,   384,   385,   246,   247,   388,   389,   248,   397,   398,
     399,   400,   401,   402,   404,   405,   406,   407,   408,   409,
     410,   249,   250,   413,   414,   415,   416,   418,   251,   420,
     422,   423,   291,   424,   292,   293,   252,   253,   254,   255,
     430,   256,   431,   257,   258,   259,   260,   435,   285,   286,
     261,   271,   262,   263,   264,   265,   266,   304,   305,   517,
     362,   347,   520,   350,   351,   361,   525,   411,   287,   288,
     527,   528,   455,   529,   285,   286,   387,   460,   412,   607,
     463,   537,   465,   428,   541,   440,   546,   429,   432,   446,
     449,    75,    79,   447,   287,   288,   448,   450,   481,   452,
     453,   289,   454,   457,   469,   470,   514,   172,   186,   269,
     509,   480,   519,   508,   524,   534,   539,   551,   552,   553,
     557,   575,   576,   504,   581,   582,   505,   583,   507,   584,
     559,   585,   196,   598,   599,   608,   271,   201,   291,   513,
     292,   293,   601,   603,   273,   638,   655,   276,   277,   278,
     279,   280,   639,   644,   281,   282,   283,   284,   645,   285,
     286,   646,   518,   647,   291,   648,   292,   293,   604,   671,
     162,   163,   660,   606,   680,   663,   684,   532,   679,   287,
     288,   334,   221,   550,   164,   662,   289,   544,   526,   165,
     166,   167,   168,   536,   316,   328,   682,   617,   592,   482,
     466,   242,   521,     0,     0,     0,   560,   561,   562,   563,
     564,   565,   566,   567,   568,     0,   569,     0,     0,   570,
     571,   572,   573,   574,     0,     0,     0,   577,   578,   579,
     580,     0,     0,   169,     0,     0,   586,   587,   588,   589,
       0,     0,   661,     0,     0,   593,   594,   290,   596,   291,
       0,   292,   293,   172,     0,   300,     0,     0,     0,   600,
     306,   172,   172,   162,   163,     0,     0,     0,   602,     0,
       0,   605,     0,     0,     0,     0,     0,   164,     0,     0,
       0,     0,   165,   166,   167,   168,     0,   611,   613,   616,
     618,   619,     0,   620,   621,   322,   172,   322,     0,     0,
     331,     0,    79,     0,     0,     0,   322,   322,   322,   170,
     322,     0,   171,    47,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,   675,     0,   169,     0,     0,     0,
       0,     0,     0,   654,     0,   656,   162,   163,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
     164,   664,     0,   666,     0,   165,   166,   167,   168,   669,
       0,   545,   392,     0,     0,   162,   163,     0,   670,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,   164,
       0,     0,     0,   419,   165,   166,   167,   168,     0,     0,
       0,     0,     0,     0,   418,   674,     0,     0,     0,   169,
       0,     0,   170,   540,   676,   171,    47,     0,   172,     0,
     172,     0,   172,     0,     0,     0,   683,     0,     0,     0,
       0,   269,     0,     0,     0,     0,     0,     0,   169,     0,
       0,     0,     0,     0,     0,     0,   172,     0,   221,     0,
     270,     0,     0,     0,     0,     0,     0,     0,   271,   272,
       0,     0,     0,     0,     0,   242,   273,   274,   275,   276,
     277,   278,   279,   280,     0,     0,   281,   282,   283,   284,
       0,   285,   286,     0,     0,   170,     0,     0,   171,    47,
       0,     0,   506,     0,     0,     0,     0,   512,     0,     0,
       0,   287,   288,     0,     0,     0,     0,     0,   289,     0,
       0,     0,     0,     0,   170,     0,     0,   171,    47,     0,
       0,     0,     0,     0,     0,     0,   172,     0,     0,   172,
     300,     0,     0,   172,     0,   306,     0,   172,   172,     0,
     172,     0,     0,     0,     0,     0,     0,   322,   172,   322,
       0,   172,     0,   172,   547,   331,     0,     0,     0,     0,
     269,     0,     0,     0,     0,     0,     0,     0,     0,   290,
       0,   291,     0,   292,   293,     0,     0,     0,     0,   270,
       0,   522,     0,     0,   523,     0,     0,   271,   272,     0,
       0,     0,     0,     0,     0,   273,   274,   275,   276,   277,
     278,   279,   280,     0,     0,   281,   282,   283,   284,   392,
     285,   286,   595,     0,     0,   269,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
     287,   288,     0,     0,   270,   172,     0,   289,     0,     0,
     172,   322,   271,   272,     0,     0,     0,     0,     0,     0,
     273,   274,   275,   276,   277,   278,   279,   280,     0,     0,
     281,   282,   283,   284,     0,   285,   286,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,   287,   288,     0,     0,     0,
       0,     0,   289,   269,     0,     0,     0,     0,   290,     0,
     291,     0,   292,   293,     0,     0,     0,     0,     0,   172,
     386,   547,   270,   597,     0,     0,     0,     0,     0,     0,
     271,   272,     0,     0,     0,     0,     0,     0,   273,   274,
     275,   276,   277,   278,   279,   280,     0,     0,   281,   282,
     283,   284,     0,   285,   286,     0,   269,     0,     0,     0,
       0,     0,     0,   290,     0,   291,     0,   292,   293,   673,
       0,     0,     0,   287,   288,   270,     0,     0,   471,     0,
     289,     0,     0,   271,   272,     0,     0,     0,     0,     0,
       0,   273,   274,   275,   276,   277,   278,   279,   280,     0,
       0,   281,   282,   283,   284,     0,   285,   286,     0,     0,
       0,     0,   269,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,   287,   288,     0,     0,
       0,   270,     0,   289,     0,     0,     0,     0,     0,   271,
     272,   290,     0,   291,     0,   292,   293,   273,   274,   275,
     276,   277,   278,   279,   280,     0,   472,   281,   282,   283,
     284,     0,   285,   286,     0,   269,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,   287,   288,   270,     0,     0,     0,     0,   289,
       0,     0,   271,   272,   290,     0,   291,     0,   292,   293,
     273,   274,   275,   276,   277,   278,   279,   280,     0,   473,
     281,   282,   283,   284,     0,   285,   286,     0,     0,     0,
       0,   269,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,   287,   288,     0,     0,     0,
     270,     0,   289,     0,     0,     0,     0,     0,   271,   272,
     290,     0,   291,     0,   292,   293,   273,   274,   275,   276,
     277,   278,   279,   280,     0,   474,   281,   282,   283,   284,
       0,   285,   286,     0,   269,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,   287,   288,   270,     0,     0,     0,     0,   289,     0,
       0,   271,   272,   290,     0,   291,     0,   292,   293,   273,
     274,   275,   276,   277,   278,   279,   280,     0,   475,   281,
     282,   283,   284,     0,   285,   286,     0,     0,     0,     0,
     269,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,   287,   288,     0,     0,     0,   270,
       0,   289,     0,     0,     0,     0,     0,   271,   272,   290,
       0,   291,     0,   292,   293,   273,   274,   275,   276,   277,
     278,   279,   280,     0,   476,   281,   282,   283,   284,     0,
     285,   286,     0,   269,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
     287,   288,   270,     0,     0,     0,     0,   289,     0,     0,
     271,   272,   290,     0,   291,     0,   292,   293,   273,   274,
     275,   276,   277,   278,   279,   280,     0,   477,   281,   282,
     283,   284,     0,   285,   286,     0,     0,     0,     0,   269,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,   287,   288,     0,     0,     0,   270,     0,
     289,     0,     0,     0,     0,     0,   271,   272,   290,     0,
     291,     0,   292,   293,   273,   274,   275,   276,   277,   278,
     279,   280,     0,   478,   281,   282,   283,   284,     0,   285,
     286,     0,   269,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,   287,
     288,   270,     0,     0,     0,     0,   289,     0,     0,   271,
     272,   290,     0,   291,     0,   292,   293,   273,   274,   275,
     276,   277,   278,   279,   280,     0,   483,   281,   282,   283,
     284,     0,   285,   286,     0,     0,     0,     0,   269,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,   287,   288,     0,     0,     0,   270,     0,   289,
       0,     0,     0,     0,     0,   271,   272,   290,     0,   291,
       0,   292,   293,   273,   274,   275,   276,   277,   278,   279,
     280,     0,   484,   281,   282,   283,   284,     0,   285,   286,
       0,   269,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,   287,   288,
     270,     0,     0,     0,     0,   289,     0,     0,   271,   272,
     290,     0,   291,     0,   292,   293,   273,   274,   275,   276,
     277,   278,   279,   280,     0,   485,   281,   282,   283,   284,
       0,   285,   286,     0,     0,     0,     0,   269,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,   287,   288,     0,     0,     0,   270,     0,   289,     0,
       0,     0,     0,     0,   271,   272,   290,     0,   291,     0,
     292,   293,   273,   274,   275,   276,   277,   278,   279,   280,
       0,   486,   281,   282,   283,   284,     0,   285,   286,     0,
     269,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,   287,   288,   270,
       0,     0,     0,     0,   289,     0,     0,   271,   272,   290,
       0,   291,     0,   292,   293,   273,   274,   275,   276,   277,
     278,   279,   280,     0,   487,   281,   282,   283,   284,     0,
     285,   286,     0,     0,     0,     0,   269,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
     287,   288,     0,     0,     0,   270,     0,   289,     0,     0,
       0,     0,     0,   271,   272,   290,     0,   291,     0,   292,
     293,   273,   274,   275,   276,   277,   278,   279,   280,     0,
     489,   281,   282,   283,   284,     0,   285,   286,     0,   269,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,   287,   288,   270,     0,
       0,     0,     0,   289,     0,     0,   271,   272,   290,     0,
     291,     0,   292,   293,   273,   274,   275,   276,   277,   278,
     279,   280,     0,   490,   281,   282,   283,   284,     0,   285,
     286,     0,     0,     0,     0,   269,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,   287,
     288,     0,     0,     0,   270,     0,   289,     0,     0,     0,
       0,     0,   271,   272,   290,     0,   291,     0,   292,   293,
     273,   274,   275,   276,   277,   278,   279,   280,     0,   491,
     281,   282,   283,   284,     0,   285,   286,     0,   269,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,   287,   288,   270,     0,     0,
       0,     0,   289,     0,     0,   271,   272,   290,     0,   291,
       0,   292,   293,   273,   274,   275,   276,   277,   278,   279,
     280,     0,   492,   281,   282,   283,   284,     0,   285,   286,
       0,     0,     0,     0,   269,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,   287,   288,
       0,     0,     0,   270,     0,   289,     0,     0,     0,     0,
       0,   271,   272,   290,     0,   291,     0,   292,   293,   273,
     274,   275,   276,   277,   278,   279,   280,     0,   493,   281,
     282,   283,   284,     0,   285,   286,     0,   269,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,   287,   288,   270,     0,     0,     0,
       0,   289,     0,     0,   271,   272,   290,     0,   291,     0,
     292,   293,   273,   274,   275,   276,   277,   278,   279,   280,
       0,   494,   281,   282,   283,   284,     0,   285,   286,     0,
       0,     0,     0,   269,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,   287,   288,     0,
       0,     0,   270,     0,   289,     0,     0,     0,     0,     0,
     271,   272,   290,     0,   291,     0,   292,   293,   273,   274,
     275,   276,   277,   278,   279,   280,     0,   495,   281,   282,
     283,   284,     0,   285,   286,     0,   269,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,   287,   288,   270,     0,     0,     0,     0,
     289,     0,     0,   271,   272,   290,     0,   291,     0,   292,
     293,   273,   274,   275,   276,   277,   278,   279,   280,     0,
     496,   281,   282,   283,   284,     0,   285,   286,     0,     0,
       0,     0,   269,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,   287,   288,     0,     0,
       0,   270,     0,   289,     0,     0,     0,     0,     0,   271,
     272,   290,     0,   291,     0,   292,   293,   273,   274,   275,
     276,   277,   278,   279,   280,     0,   497,   281,   282,   283,
     284,     0,   285,   286,     0,   269,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,   287,   288,   270,     0,     0,     0,     0,   289,
       0,     0,   271,   272,   290,     0,   291,     0,   292,   293,
     273,   274,   275,   276,   277,   278,   279,   280,     0,   498,
     281,   282,   283,   284,     0,   285,   286,     0,     0,     0,
       0,   269,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,   287,   288,     0,     0,     0,
     270,     0,   289,     0,     0,     0,     0,     0,   271,   272,
     290,     0,   291,     0,   292,   293,   273,   274,   275,   276,
     277,   278,   279,   280,     0,   499,   281,   282,   283,   284,
       0,   285,   286,     0,   269,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,   287,   288,   270,     0,     0,     0,     0,   289,     0,
       0,   271,   272,   290,     0,   291,     0,   292,   293,   273,
     274,   275,   276,   277,   278,   279,   280,     0,   500,   281,
     282,   283,   284,     0,   285,   286,     0,     0,     0,     0,
     269,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,   287,   288,     0,     0,     0,   270,
       0,   289,     0,     0,     0,     0,     0,   271,   272,   290,
       0,   291,     0,   292,   293,   273,   274,   275,   276,   277,
     278,   279,   280,     0,   501,   281,   282,   283,   284,     0,
     285,   286,     0,   269,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
     287,   288,   270,     0,     0,     0,     0,   289,     0,     0,
     271,   272,   290,     0,   291,     0,   292,   293,   273,   274,
     275,   276,   277,   278,   279,   280,     0,   502,   281,   282,
     283,   284,     0,   285,   286,     0,     0,     0,     0,   269,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,   287,   288,     0,     0,     0,   270,     0,
     289,     0,     0,     0,     0,     0,   271,   272,   290,     0,
     291,     0,   292,   293,   273,   274,   275,   276,   277,   278,
     279,   280,     0,   503,   281,   282,   283,   284,     0,   285,
     286,     0,   269,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,   287,
     288,   270,     0,     0,     0,     0,   289,     0,     0,   271,
     272,   290,     0,   291,     0,   292,   293,   273,   274,   275,
     276,   277,   278,   279,   280,     0,   623,   281,   282,   283,
     284,     0,   285,   286,     0,     0,     0,     0,   269,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,   287,   288,     0,     0,     0,   270,     0,   289,
       0,     0,     0,     0,     0,   271,   272,   290,     0,   291,
       0,   292,   293,   273,   274,   275,   276,   277,   278,   279,
     280,     0,   632,   281,   282,   283,   284,     0,   285,   286,
       0,   269,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,   287,   288,
     270,     0,     0,     0,     0,   289,     0,     0,   271,   272,
     290,     0,   291,     0,   292,   293,   273,   274,   275,   276,
     277,   278,   279,   280,   515,     0,   281,   282,   283,   284,
       0,   285,   286,     0,     0,     0,     0,   269,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,   287,   288,     0,     0,     0,   270,     0,   289,     0,
       0,     0,     0,     0,   271,   272,   290,     0,   291,     0,
     292,   293,   273,   274,   275,   276,   277,   278,   279,   280,
     591,     0,   281,   282,   283,   284,     0,   285,   286,     0,
     269,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,   287,   288,   270,
       0,     0,     0,     0,   289,     0,     0,   271,   272,   290,
       0,   291,     0,   292,   293,   273,   274,   275,   276,   277,
     278,   279,   280,   653,     0,   281,   282,   283,   284,     0,
     285,   286,     0,     0,     0,     0,   269,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
     287,   288,     0,     0,     0,   270,     0,   289,     0,     0,
       0,     0,     0,   271,   272,   290,     0,   291,     0,   292,
     293,   273,   274,   275,   276,   277,   278,   279,   280,   685,
       0,   281,   282,   283,   284,     0,   285,   286,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,   269,     0,
       0,     0,     0,     0,     0,     0,   287,   288,     0,     0,
       0,     0,     0,   289,     0,     0,     0,   270,   290,     0,
     291,     0,   292,   293,     0,   271,   272,     0,     0,     0,
       0,   319,     0,   273,   274,   275,   276,   277,   278,   279,
     280,     0,     0,   281,   282,   283,   284,     0,   285,   286,
       0,     0,     0,   269,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,   287,   288,
       0,     0,   270,     0,   290,   289,   291,     0,   292,   293,
     271,   272,     0,     0,     0,     0,   386,     0,   273,   274,
     275,   276,   277,   278,   279,   280,     0,     0,   281,   282,
     283,   284,     0,   285,   286,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,   269,     0,     0,     0,     0,
       0,     0,     0,   287,   288,     0,     0,     0,     0,     0,
     289,     0,     0,     0,   270,     0,   290,     0,   291,     0,
     292,   293,   271,   272,     0,     0,     0,     0,   467,     0,
     273,   274,   275,   276,   277,   278,   279,   280,     0,     0,
     281,   282,   283,   284,     0,   285,   286,     0,     0,     0,
     269,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,   287,   288,     0,     0,   270,
       0,   290,   289,   291,     0,   292,   293,   271,   272,     0,
       0,     0,     0,   468,     0,   273,   274,   275,   276,   277,
     278,   279,   280,     0,     0,   281,   282,   283,   284,     0,
     285,   286,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,   269,     0,     0,     0,     0,     0,     0,     0,
     287,   288,     0,     0,     0,     0,     0,   289,     0,     0,
       0,   270,     0,   290,     0,   291,     0,   292,   293,   271,
     272,     0,     0,     0,     0,   479,     0,   273,   274,   275,
     276,   277,   278,   279,   280,     0,     0,   281,   282,   283,
     284,     0,   285,   286,     0,     0,     0,   269,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,   287,   288,     0,     0,   270,     0,   290,   289,
     291,     0,   292,   293,   271,   272,     0,     0,     0,     0,
     488,     0,   273,   274,   275,   276,   277,   278,   279,   280,
       0,     0,   281,   282,   283,   284,     0,   285,   286,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,   269,
       0,     0,     0,     0,     0,     0,     0,   287,   288,     0,
       0,     0,     0,     0,   289,     0,     0,     0,   270,     0,
     290,     0,   291,     0,   292,   293,   271,   272,     0,     0,
       0,     0,   590,     0,   273,   274,   275,   276,   277,   278,
     279,   280,     0,     0,   281,   282,   283,   284,     0,   285,
     286,     0,     0,     0,   269,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,   287,
     288,     0,     0,   270,     0,   290,   289,   291,     0,   292,
     293,   271,   272,     0,     0,     0,     0,   624,     0,   273,
     274,   275,   276,   277,   278,   279,   280,     0,     0,   281,
     282,   283,   284,     0,   285,   286,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,   269,     0,     0,     0,
       0,     0,     0,     0,   287,   288,     0,     0,     0,     0,
       0,   289,     0,     0,     0,   270,     0,   290,     0,   291,
       0,   292,   293,   271,   272,     0,     0,     0,     0,   625,
       0,   273,   274,   275,   276,   277,   278,   279,   280,     0,
       0,   281,   282,   283,   284,     0,   285,   286,     0,     0,
       0,   269,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,   287,   288,     0,     0,
     270,     0,   290,   289,   291,     0,   292,   293,   271,   272,
       0,     0,     0,     0,   626,     0,   273,   274,   275,   276,
     277,   278,   279,   280,     0,     0,   281,   282,   283,   284,
       0,   285,   286,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,   269,     0,     0,     0,     0,     0,     0,
       0,   287,   288,     0,     0,     0,     0,     0,   289,     0,
       0,     0,   270,     0,   290,     0,   291,     0,   292,   293,
     271,   272,     0,     0,     0,     0,   627,     0,   273,   274,
     275,   276,   277,   278,   279,   280,     0,     0,   281,   282,
     283,   284,     0,   285,   286,     0,     0,     0,   269,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,   287,   288,     0,     0,   270,     0,   290,
     289,   291,     0,   292,   293,   271,   272,     0,     0,     0,
       0,   628,     0,   273,   274,   275,   276,   277,   278,   279,
     280,     0,     0,   281,   282,   283,   284,     0,   285,   286,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
     269,     0,     0,     0,     0,     0,     0,     0,   287,   288,
       0,     0,     0,     0,     0,   289,     0,     0,     0,   270,
       0,   290,     0,   291,     0,   292,   293,   271,   272,     0,
       0,     0,     0,   629,     0,   273,   274,   275,   276,   277,
     278,   279,   280,     0,     0,   281,   282,   283,   284,     0,
     285,   286,     0,     0,     0,   269,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
     287,   288,     0,     0,   270,     0,   290,   289,   291,     0,
     292,   293,   271,   272,     0,     0,     0,     0,   630,     0,
     273,   274,   275,   276,   277,   278,   279,   280,     0,     0,
     281,   282,   283,   284,     0,   285,   286,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,   269,     0,     0,
       0,     0,     0,     0,     0,   287,   288,     0,     0,     0,
       0,     0,   289,     0,     0,     0,   270,     0,   290,     0,
     291,     0,   292,   293,   271,   272,     0,     0,     0,     0,
     631,     0,   273,   274,   275,   276,   277,   278,   279,   280,
       0,     0,   281,   282,   283,   284,     0,   285,   286,     0,
       0,     0,   269,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,   287,   288,     0,
       0,   270,     0,   290,   289,   291,     0,   292,   293,   271,
     272,     0,     0,     0,     0,   633,     0,   273,   274,   275,
     276,   277,   278,   279,   280,     0,     0,   281,   282,   283,
     284,     0,   285,   286,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,   269,     0,     0,     0,     0,     0,
       0,     0,   287,   288,     0,     0,     0,     0,     0,   289,
       0,     0,     0,   270,     0,   290,     0,   291,     0,   292,
     293,   271,   272,     0,     0,     0,     0,   634,     0,   273,
     274,   275,   276,   277,   278,   279,   280,     0,     0,   281,
     282,   283,   284,     0,   285,   286,     0,     0,     0,   269,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,   287,   288,     0,     0,   270,     0,
     290,   289,   291,     0,   292,   293,   271,   272,     0,     0,
       0,     0,   635,     0,   273,   274,   275,   276,   277,   278,
     279,   280,     0,     0,   281,   282,   283,   284,     0,   285,
     286,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,   269,     0,     0,     0,     0,     0,     0,     0,   287,
     288,     0,     0,     0,     0,     0,   289,     0,     0,     0,
     270,     0,   290,     0,   291,     0,   292,   293,   271,   272,
       0,     0,     0,     0,   636,     0,   273,   274,   275,   276,
     277,   278,   279,   280,     0,     0,   281,   282,   283,   284,
       0,   285,   286,     0,     0,     0,   269,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,   287,   288,     0,     0,   270,     0,   290,   289,   291,
       0,   292,   293,   271,   272,     0,     0,     0,     0,   637,
       0,   273,   274,   275,   276,   277,   278,   279,   280,     0,
       0,   281,   282,   283,   284,     0,   285,   286,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,   269,     0,
       0,     0,     0,     0,     0,     0,   287,   288,     0,     0,
       0,     0,     0,   289,     0,     0,     0,   270,     0,   290,
       0,   291,     0,   292,   293,   271,   272,     0,     0,     0,
       0,   640,     0,   273,   274,   275,   276,   277,   278,   279,
     280,     0,     0,   281,   282,   283,   284,     0,   285,   286,
       0,     0,     0,   269,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,   287,   288,
       0,     0,   270,     0,   290,   289,   291,     0,   292,   293,
     271,   272,     0,     0,     0,     0,   641,     0,   273,   274,
     275,   276,   277,   278,   279,   280,     0,     0,   281,   282,
     283,   284,     0,   285,   286,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,   269,     0,     0,     0,     0,
       0,     0,     0,   287,   288,     0,     0,     0,     0,     0,
     289,     0,     0,     0,   270,     0,   290,     0,   291,     0,
     292,   293,   271,   272,     0,     0,     0,     0,   642,     0,
     273,   274,   275,   276,   277,   278,   279,   280,     0,     0,
     281,   282,   283,   284,     0,   285,   286,     0,     0,     0,
     269,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,   287,   288,     0,     0,   270,
       0,   290,   289,   291,     0,   292,   293,   271,   272,     0,
       0,     0,     0,   643,     0,   273,   274,   275,   276,   277,
     278,   279,   280,     0,     0,   281,   282,   283,   284,     0,
     285,   286,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,   269,     0,     0,     0,     0,     0,     0,     0,
     287,   288,     0,     0,     0,     0,     0,   289,     0,     0,
       0,   270,     0,   290,     0,   291,     0,   292,   293,   271,
     272,     0,     0,     0,     0,   649,     0,   273,   274,   275,
     276,   277,   278,   279,   280,     0,     0,   281,   282,   283,
     284,     0,   285,   286,     0,     0,     0,   269,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,   287,   288,     0,     0,   270,     0,   290,   289,
     291,     0,   292,   293,   271,   272,     0,     0,     0,     0,
     650,     0,   273,   274,   275,   276,   277,   278,   279,   280,
       0,     0,   281,   282,   283,   284,     0,   285,   286,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,   269,
       0,     0,     0,     0,     0,     0,     0,   287,   288,     0,
       0,     0,     0,     0,   289,     0,     0,     0,   270,     0,
     290,     0,   291,     0,   292,   293,   271,   272,     0,     0,
       0,     0,   651,     0,   273,   274,   275,   276,   277,   278,
     279,   280,     0,     0,   281,   282,   283,   284,     0,   285,
     286,     0,     0,     0,   269,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,   287,
     288,     0,     0,   270,     0,   290,   289,   291,     0,   292,
     293,   271,   272,     0,     0,     0,     0,   652,     0,   273,
     274,   275,   276,   277,   278,   279,   280,     0,     0,   281,
     282,   283,   284,     0,   285,   286,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,   269,     0,     0,     0,
       0,     0,     0,     0,   287,   288,     0,     0,     0,     0,
       0,   289,     0,     0,     0,   270,     0,   290,     0,   291,
       0,   292,   293,   271,   272,     0,     0,     0,     0,   657,
       0,   273,   274,   275,   276,   277,   278,   279,   280,     0,
       0,   281,   282,   283,   284,     0,   285,   286,     0,     0,
       0,   269,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,   287,   288,     0,     0,
     270,     0,   290,   289,   291,     0,   292,   293,   271,   272,
       0,     0,     0,     0,   672,     0,   273,   274,   275,   276,
     277,   278,   279,   280,     0,     0,   281,   282,   283,   284,
       0,   285,   286,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,   287,   288,     0,     0,     0,     0,     0,   289,     0,
       0,     0,     0,     0,   290,     0,   291,     0,   292,   293,
       0,     0,     0,     0,     0,     0,   677,     0,     0,     0,
      83,     0,    84,     0,     0,     0,     0,     0,     0,    85,
      86,    87,     0,    88,    89,    90,    91,    92,    93,     0,
       0,     0,     0,     0,     0,     0,    94,     0,     0,     0,
      95,   612,     0,     0,     0,     0,     0,     0,     0,   290,
      96,   291,     0,   292,   293,     0,     0,     0,     0,     0,
      97,   678,     0,    98,    99,   100,   101,   102,   103,   104,
     105,   106,   107,   108,   109,     0,     0,   110,     0,     0,
     111,     0,     0,   112,   113,   114,   115,   116,     0,   117,
     118,   119,   120,   121,   122,   123,   124,   125,   126,   127,
     128,   129,   130,   131,   132,     0,     0,     0,     0,     0,
      83,     0,    84,     0,     0,     0,     0,     0,     0,    85,
      86,    87,     0,    88,    89,    90,    91,    92,    93,     0,
       0,     0,     0,     0,     0,     0,    94,     0,     0,     0,
      95,     0,     0,     0,     0,     0,     0,     0,     0,     0,
      96,     0,     0,     0,   133,    47,     0,   134,   135,   136,
      97,     0,     0,    98,    99,   100,   101,   102,   103,   104,
     105,   106,   107,   108,   109,     0,     0,   110,     0,     0,
     111,     0,     0,   112,   113,   114,   115,   116,     0,   117,
     118,   119,   120,   121,   122,   123,   124,   125,   126,   127,
     128,   129,   130,   131,   132,     0,     0,     0,     0,     0,
      83,     0,    84,     0,     0,     0,     0,     0,     0,    85,
      86,    87,     0,    88,    89,    90,    91,    92,    93,     0,
       0,     0,     0,     0,     0,     0,    94,     0,     0,     0,
      95,     0,     0,     0,     0,     0,     0,     0,     0,     0,
      96,     0,     0,     0,   133,    47,     0,   134,   135,   136,
      97,     0,     0,    98,    99,   100,   101,   102,   103,   104,
     105,   106,   107,   108,   109,     0,     0,   110,     0,     0,
     111,     0,     0,   112,   113,   114,   115,   116,     0,   117,
     118,   119,   120,   121,   122,   123,   124,   125,   126,   127,
     128,   129,   130,   131,   132,     0,     0,     0,     0,     0,
      83,     0,    84,     0,     0,     1,     0,     0,     0,    85,
      86,    87,     0,    88,    89,    90,    91,    92,    93,     0,
       0,     0,     0,     0,     0,     0,    94,     0,     0,     0,
      95,     0,     0,     0,     2,     0,     0,     0,     0,     0,
      96,     0,     0,     0,   403,    47,     0,   134,   135,   136,
      97,     0,     0,    98,    99,   100,   101,   102,   103,   104,
     105,   106,   107,   108,   109,     0,     0,   110,     0,     0,
     111,     0,     0,   112,   113,   114,   115,   116,     0,   117,
     118,   119,   120,   121,   122,   123,   124,   125,   126,   127,
     128,   129,   130,   131,   132,     0,     3,     4,     5,     6,
       7,     8,     9,    10,    11,    12,    13,    14,    15,    16,
      17,    18,    19,    20,    21,    22,    23,    24,    25,    26,
      27,    28,    29,    30,    31,    32,    33,    34,    35,    36,
      37,    38,    39,    40,    41,    42,    43,    44,    45,    46,
     269,     0,     0,     0,   133,    47,    47,   417,   135,   136,
       0,    48,     0,     0,     0,     0,     0,     0,     0,   270,
       0,     0,     0,     0,     0,     0,     0,   271,   272,     0,
       0,     0,     0,     0,     0,   273,   274,   275,   276,   277,
     278,   279,   280,     0,     0,   281,   282,   283,   284,     0,
     285,   286,     0,   269,     0,     0,     0,   554,   555,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
     287,   288,   270,     0,     0,     0,     0,   289,     0,     0,
     271,   272,     0,     0,     0,     0,     0,     0,   273,   274,
     275,   276,   277,   278,   279,   280,     0,     0,   281,   282,
     283,   284,     0,   285,   286,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,   269,     0,     0,
       0,     0,     0,   287,   288,     0,     0,     0,     0,     0,
     289,     0,     0,     0,     0,     0,   270,     0,   290,     0,
     291,   341,   292,   293,   271,   272,   134,     0,     0,     0,
       0,     0,   273,   274,   275,   276,   277,   278,   279,   280,
       0,     0,   281,   282,   283,   284,     0,   285,   286,     0,
     269,     0,     0,     0,     0,     0,     0,   667,     0,     0,
       0,     0,     0,     0,     0,     0,     0,   287,   288,   270,
       0,   290,     0,   291,   289,   292,   293,   271,   272,     0,
       0,     0,     0,     0,     0,   273,   274,   275,   276,   277,
     278,   279,   280,     0,     0,   281,   282,   283,   284,     0,
     285,   286,     0,     0,     0,     0,   269,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
     287,   288,     0,     0,     0,   270,     0,   289,     0,     0,
     668,     0,     0,   271,   272,   290,     0,   291,     0,   292,
     293,   273,   274,   275,   276,   277,   278,   279,   280,     0,
       0,   281,   282,   283,   284,     0,   285,   286,     0,   269,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,   287,   288,   270,     0,
       0,     0,     0,   289,     0,     0,   271,   272,   290,     0,
     291,     0,   292,   293,   273,   274,   275,   276,   277,   278,
     279,   280,     0,     0,   281,   282,   283,   284,     0,   285,
     286,     0,     0,     0,     0,   269,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,   287,
     288,     0,     0,     0,   270,     0,   289,     0,     0,     0,
       0,     0,   271,   272,   290,     0,   291,     0,   292,   293,
     273,   274,   275,   276,   277,   278,   279,   280,     0,     0,
     281,   282,   283,   284,     0,   285,   286,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,   287,   288,     0,     0,     0,
       0,     0,   289,     0,     0,   271,     0,   290,     0,   291,
       0,   292,   293,   273,     0,     0,   276,   277,   278,   279,
     280,     0,     0,   281,   282,   283,   284,     0,   285,   286,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,   287,   288,
       0,     0,     0,     0,     0,   289,     0,     0,   271,     0,
       0,     0,     0,   290,     0,   658,    -1,   292,   293,   276,
     277,   278,   279,   280,     0,     0,   281,   282,   283,   284,
       0,   285,   286,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,   287,   288,     0,     0,     0,     0,     0,   289,     0,
       0,   271,     0,     0,     0,     0,   290,     0,   291,     0,
     292,   293,   276,   277,   278,   279,   280,     0,     0,    -1,
      -1,    -1,    -1,     0,   285,   286,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,   287,   288,     0,     0,     0,     0,
       0,   289,     0,     0,     0,     0,     0,     0,     0,    -1,
       0,   291,     0,   292,   293,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,   291,     0,   292,   293
};

static const yytype_int16 yycheck[] =
{
       4,     5,     6,    82,     8,   206,    43,   215,    10,    35,
      14,    15,    10,    11,    12,    13,   142,    43,   156,   157,
      18,    19,    71,    69,    72,    22,   148,   147,    72,   155,
      33,    34,    35,    36,    37,    38,    31,    72,    42,    43,
      44,    45,    40,   154,    72,    72,   157,     5,     6,    44,
      45,    46,   149,    72,   154,     4,   162,   157,   150,    54,
      55,    19,   153,     0,   170,   171,    24,    25,    26,    27,
      54,    55,   142,   154,    23,    72,   157,    35,   154,    74,
      75,   157,    31,    32,    88,    43,    81,   153,    92,    93,
      39,    40,    96,    42,    43,    44,    45,    46,   142,   205,
      49,    50,    51,    52,    31,    54,    55,   111,   157,   157,
      68,   157,   149,   150,   142,   142,    54,    55,    45,   154,
     142,   153,   157,   142,   150,    74,    75,    54,    55,   133,
     147,   154,    81,   155,   157,   214,    74,    75,   155,   154,
     157,   220,   157,    81,   615,   155,   617,    74,    75,   144,
      72,   146,   147,   147,    81,   157,   159,   148,   147,   150,
     144,   159,   146,   147,   144,   147,   146,   170,   148,   144,
     147,   146,   144,   148,   146,   147,   216,   217,   154,   219,
     154,   157,   186,   157,   154,   154,   144,   157,   157,   147,
     148,   154,   150,   142,   157,   144,   199,   146,   147,   147,
     147,   147,    54,    55,   147,   147,   144,   147,   146,   147,
      15,   317,   147,   319,   293,   321,   147,   144,   147,   146,
     147,   147,    74,   227,   147,   229,   147,   147,   232,   233,
     234,   235,   236,   237,   238,   239,   240,   147,   147,   345,
     448,   147,   246,   247,   248,   249,   250,   251,   252,   253,
     254,   255,   256,   257,   258,   259,   260,   261,   262,   263,
     264,   265,   266,   147,   147,   269,   270,   147,   272,   273,
     274,   275,   276,   277,   278,   279,   280,   281,   282,   283,
     284,   147,   147,   287,   288,   289,   290,   291,   147,   292,
     294,   295,   144,   296,   146,   147,   147,   147,   147,   147,
     304,   147,   305,   147,   147,   147,   147,   310,    54,    55,
     147,    31,   147,   147,   147,   147,   147,   147,   147,   425,
      38,   157,   428,   150,   150,   150,   432,   150,    74,    75,
     436,   437,   336,   439,    54,    55,   157,   341,   150,   540,
     344,   447,   346,    15,   450,    37,   452,   157,   155,   157,
     154,     0,     1,   155,    74,    75,   157,   142,   362,   155,
     147,    81,    75,   154,   157,   157,   155,    16,    17,     4,
      38,   157,    30,   157,   154,    72,   155,   155,   155,   155,
     155,   150,   150,   387,   150,   150,   390,   150,   391,   150,
     469,   150,    41,   150,   142,   155,    31,    46,   144,   403,
     146,   147,   156,   156,    39,   157,   156,    42,    43,    44,
      45,    46,   154,   154,    49,    50,    51,    52,   154,    54,
      55,   154,   426,   154,   144,   154,   146,   147,   534,   150,
       5,     6,   158,   539,    38,   147,   155,   440,   154,    74,
      75,   211,    91,   454,    19,   610,    81,   451,   434,    24,
      25,    26,    27,   446,   171,    30,   676,   553,   508,   364,
     347,   110,   429,    -1,    -1,    -1,   470,   471,   472,   473,
     474,   475,   476,   477,   478,    -1,   480,    -1,    -1,   483,
     484,   485,   486,   487,    -1,    -1,    -1,   491,   492,   493,
     494,    -1,    -1,    68,    -1,    -1,   500,   501,   502,   503,
      -1,    -1,   608,    -1,    -1,   509,   510,   142,   511,   144,
      -1,   146,   147,   162,    -1,   164,    -1,    -1,    -1,   523,
     169,   170,   171,     5,     6,    -1,    -1,    -1,   531,    -1,
      -1,   535,    -1,    -1,    -1,    -1,    -1,    19,    -1,    -1,
      -1,    -1,    24,    25,    26,    27,    -1,   551,   552,   553,
     554,   555,    -1,   557,   558,   204,   205,   206,    -1,    -1,
     209,    -1,   211,    -1,    -1,    -1,   215,   216,   217,   144,
     219,    -1,   147,   148,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,   663,    -1,    68,    -1,    -1,    -1,
      -1,    -1,    -1,   597,    -1,   599,     5,     6,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      19,   615,    -1,   617,    -1,    24,    25,    26,    27,   623,
      -1,    30,   271,    -1,    -1,     5,     6,    -1,   632,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    19,
      -1,    -1,    -1,   292,    24,    25,    26,    27,    -1,    -1,
      -1,    -1,    -1,    -1,   658,   659,    -1,    -1,    -1,    68,
      -1,    -1,   144,   145,   668,   147,   148,    -1,   317,    -1,
     319,    -1,   321,    -1,    -1,    -1,   680,    -1,    -1,    -1,
      -1,     4,    -1,    -1,    -1,    -1,    -1,    -1,    68,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,   345,    -1,   347,    -1,
      23,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    31,    32,
      -1,    -1,    -1,    -1,    -1,   364,    39,    40,    41,    42,
      43,    44,    45,    46,    -1,    -1,    49,    50,    51,    52,
      -1,    54,    55,    -1,    -1,   144,    -1,    -1,   147,   148,
      -1,    -1,   391,    -1,    -1,    -1,    -1,   396,    -1,    -1,
      -1,    74,    75,    -1,    -1,    -1,    -1,    -1,    81,    -1,
      -1,    -1,    -1,    -1,   144,    -1,    -1,   147,   148,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,   425,    -1,    -1,   428,
     429,    -1,    -1,   432,    -1,   434,    -1,   436,   437,    -1,
     439,    -1,    -1,    -1,    -1,    -1,    -1,   446,   447,   448,
      -1,   450,    -1,   452,   453,   454,    -1,    -1,    -1,    -1,
       4,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,   142,
      -1,   144,    -1,   146,   147,    -1,    -1,    -1,    -1,    23,
      -1,   154,    -1,    -1,   157,    -1,    -1,    31,    32,    -1,
      -1,    -1,    -1,    -1,    -1,    39,    40,    41,    42,    43,
      44,    45,    46,    -1,    -1,    49,    50,    51,    52,   508,
      54,    55,   511,    -1,    -1,     4,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      74,    75,    -1,    -1,    23,   534,    -1,    81,    -1,    -1,
     539,   540,    31,    32,    -1,    -1,    -1,    -1,    -1,    -1,
      39,    40,    41,    42,    43,    44,    45,    46,    -1,    -1,
      49,    50,    51,    52,    -1,    54,    55,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    74,    75,    -1,    -1,    -1,
      -1,    -1,    81,     4,    -1,    -1,    -1,    -1,   142,    -1,
     144,    -1,   146,   147,    -1,    -1,    -1,    -1,    -1,   608,
     154,   610,    23,   157,    -1,    -1,    -1,    -1,    -1,    -1,
      31,    32,    -1,    -1,    -1,    -1,    -1,    -1,    39,    40,
      41,    42,    43,    44,    45,    46,    -1,    -1,    49,    50,
      51,    52,    -1,    54,    55,    -1,     4,    -1,    -1,    -1,
      -1,    -1,    -1,   142,    -1,   144,    -1,   146,   147,   658,
      -1,    -1,    -1,    74,    75,    23,    -1,    -1,   157,    -1,
      81,    -1,    -1,    31,    32,    -1,    -1,    -1,    -1,    -1,
      -1,    39,    40,    41,    42,    43,    44,    45,    46,    -1,
      -1,    49,    50,    51,    52,    -1,    54,    55,    -1,    -1,
      -1,    -1,     4,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    74,    75,    -1,    -1,
      -1,    23,    -1,    81,    -1,    -1,    -1,    -1,    -1,    31,
      32,   142,    -1,   144,    -1,   146,   147,    39,    40,    41,
      42,    43,    44,    45,    46,    -1,   157,    49,    50,    51,
      52,    -1,    54,    55,    -1,     4,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    74,    75,    23,    -1,    -1,    -1,    -1,    81,
      -1,    -1,    31,    32,   142,    -1,   144,    -1,   146,   147,
      39,    40,    41,    42,    43,    44,    45,    46,    -1,   157,
      49,    50,    51,    52,    -1,    54,    55,    -1,    -1,    -1,
      -1,     4,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    74,    75,    -1,    -1,    -1,
      23,    -1,    81,    -1,    -1,    -1,    -1,    -1,    31,    32,
     142,    -1,   144,    -1,   146,   147,    39,    40,    41,    42,
      43,    44,    45,    46,    -1,   157,    49,    50,    51,    52,
      -1,    54,    55,    -1,     4,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    74,    75,    23,    -1,    -1,    -1,    -1,    81,    -1,
      -1,    31,    32,   142,    -1,   144,    -1,   146,   147,    39,
      40,    41,    42,    43,    44,    45,    46,    -1,   157,    49,
      50,    51,    52,    -1,    54,    55,    -1,    -1,    -1,    -1,
       4,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    74,    75,    -1,    -1,    -1,    23,
      -1,    81,    -1,    -1,    -1,    -1,    -1,    31,    32,   142,
      -1,   144,    -1,   146,   147,    39,    40,    41,    42,    43,
      44,    45,    46,    -1,   157,    49,    50,    51,    52,    -1,
      54,    55,    -1,     4,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      74,    75,    23,    -1,    -1,    -1,    -1,    81,    -1,    -1,
      31,    32,   142,    -1,   144,    -1,   146,   147,    39,    40,
      41,    42,    43,    44,    45,    46,    -1,   157,    49,    50,
      51,    52,    -1,    54,    55,    -1,    -1,    -1,    -1,     4,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    74,    75,    -1,    -1,    -1,    23,    -1,
      81,    -1,    -1,    -1,    -1,    -1,    31,    32,   142,    -1,
     144,    -1,   146,   147,    39,    40,    41,    42,    43,    44,
      45,    46,    -1,   157,    49,    50,    51,    52,    -1,    54,
      55,    -1,     4,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    74,
      75,    23,    -1,    -1,    -1,    -1,    81,    -1,    -1,    31,
      32,   142,    -1,   144,    -1,   146,   147,    39,    40,    41,
      42,    43,    44,    45,    46,    -1,   157,    49,    50,    51,
      52,    -1,    54,    55,    -1,    -1,    -1,    -1,     4,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    74,    75,    -1,    -1,    -1,    23,    -1,    81,
      -1,    -1,    -1,    -1,    -1,    31,    32,   142,    -1,   144,
      -1,   146,   147,    39,    40,    41,    42,    43,    44,    45,
      46,    -1,   157,    49,    50,    51,    52,    -1,    54,    55,
      -1,     4,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    74,    75,
      23,    -1,    -1,    -1,    -1,    81,    -1,    -1,    31,    32,
     142,    -1,   144,    -1,   146,   147,    39,    40,    41,    42,
      43,    44,    45,    46,    -1,   157,    49,    50,    51,    52,
      -1,    54,    55,    -1,    -1,    -1,    -1,     4,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    74,    75,    -1,    -1,    -1,    23,    -1,    81,    -1,
      -1,    -1,    -1,    -1,    31,    32,   142,    -1,   144,    -1,
     146,   147,    39,    40,    41,    42,    43,    44,    45,    46,
      -1,   157,    49,    50,    51,    52,    -1,    54,    55,    -1,
       4,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    74,    75,    23,
      -1,    -1,    -1,    -1,    81,    -1,    -1,    31,    32,   142,
      -1,   144,    -1,   146,   147,    39,    40,    41,    42,    43,
      44,    45,    46,    -1,   157,    49,    50,    51,    52,    -1,
      54,    55,    -1,    -1,    -1,    -1,     4,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      74,    75,    -1,    -1,    -1,    23,    -1,    81,    -1,    -1,
      -1,    -1,    -1,    31,    32,   142,    -1,   144,    -1,   146,
     147,    39,    40,    41,    42,    43,    44,    45,    46,    -1,
     157,    49,    50,    51,    52,    -1,    54,    55,    -1,     4,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    74,    75,    23,    -1,
      -1,    -1,    -1,    81,    -1,    -1,    31,    32,   142,    -1,
     144,    -1,   146,   147,    39,    40,    41,    42,    43,    44,
      45,    46,    -1,   157,    49,    50,    51,    52,    -1,    54,
      55,    -1,    -1,    -1,    -1,     4,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    74,
      75,    -1,    -1,    -1,    23,    -1,    81,    -1,    -1,    -1,
      -1,    -1,    31,    32,   142,    -1,   144,    -1,   146,   147,
      39,    40,    41,    42,    43,    44,    45,    46,    -1,   157,
      49,    50,    51,    52,    -1,    54,    55,    -1,     4,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    74,    75,    23,    -1,    -1,
      -1,    -1,    81,    -1,    -1,    31,    32,   142,    -1,   144,
      -1,   146,   147,    39,    40,    41,    42,    43,    44,    45,
      46,    -1,   157,    49,    50,    51,    52,    -1,    54,    55,
      -1,    -1,    -1,    -1,     4,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    74,    75,
      -1,    -1,    -1,    23,    -1,    81,    -1,    -1,    -1,    -1,
      -1,    31,    32,   142,    -1,   144,    -1,   146,   147,    39,
      40,    41,    42,    43,    44,    45,    46,    -1,   157,    49,
      50,    51,    52,    -1,    54,    55,    -1,     4,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    74,    75,    23,    -1,    -1,    -1,
      -1,    81,    -1,    -1,    31,    32,   142,    -1,   144,    -1,
     146,   147,    39,    40,    41,    42,    43,    44,    45,    46,
      -1,   157,    49,    50,    51,    52,    -1,    54,    55,    -1,
      -1,    -1,    -1,     4,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    74,    75,    -1,
      -1,    -1,    23,    -1,    81,    -1,    -1,    -1,    -1,    -1,
      31,    32,   142,    -1,   144,    -1,   146,   147,    39,    40,
      41,    42,    43,    44,    45,    46,    -1,   157,    49,    50,
      51,    52,    -1,    54,    55,    -1,     4,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    74,    75,    23,    -1,    -1,    -1,    -1,
      81,    -1,    -1,    31,    32,   142,    -1,   144,    -1,   146,
     147,    39,    40,    41,    42,    43,    44,    45,    46,    -1,
     157,    49,    50,    51,    52,    -1,    54,    55,    -1,    -1,
      -1,    -1,     4,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    74,    75,    -1,    -1,
      -1,    23,    -1,    81,    -1,    -1,    -1,    -1,    -1,    31,
      32,   142,    -1,   144,    -1,   146,   147,    39,    40,    41,
      42,    43,    44,    45,    46,    -1,   157,    49,    50,    51,
      52,    -1,    54,    55,    -1,     4,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    74,    75,    23,    -1,    -1,    -1,    -1,    81,
      -1,    -1,    31,    32,   142,    -1,   144,    -1,   146,   147,
      39,    40,    41,    42,    43,    44,    45,    46,    -1,   157,
      49,    50,    51,    52,    -1,    54,    55,    -1,    -1,    -1,
      -1,     4,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    74,    75,    -1,    -1,    -1,
      23,    -1,    81,    -1,    -1,    -1,    -1,    -1,    31,    32,
     142,    -1,   144,    -1,   146,   147,    39,    40,    41,    42,
      43,    44,    45,    46,    -1,   157,    49,    50,    51,    52,
      -1,    54,    55,    -1,     4,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    74,    75,    23,    -1,    -1,    -1,    -1,    81,    -1,
      -1,    31,    32,   142,    -1,   144,    -1,   146,   147,    39,
      40,    41,    42,    43,    44,    45,    46,    -1,   157,    49,
      50,    51,    52,    -1,    54,    55,    -1,    -1,    -1,    -1,
       4,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    74,    75,    -1,    -1,    -1,    23,
      -1,    81,    -1,    -1,    -1,    -1,    -1,    31,    32,   142,
      -1,   144,    -1,   146,   147,    39,    40,    41,    42,    43,
      44,    45,    46,    -1,   157,    49,    50,    51,    52,    -1,
      54,    55,    -1,     4,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      74,    75,    23,    -1,    -1,    -1,    -1,    81,    -1,    -1,
      31,    32,   142,    -1,   144,    -1,   146,   147,    39,    40,
      41,    42,    43,    44,    45,    46,    -1,   157,    49,    50,
      51,    52,    -1,    54,    55,    -1,    -1,    -1,    -1,     4,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    74,    75,    -1,    -1,    -1,    23,    -1,
      81,    -1,    -1,    -1,    -1,    -1,    31,    32,   142,    -1,
     144,    -1,   146,   147,    39,    40,    41,    42,    43,    44,
      45,    46,    -1,   157,    49,    50,    51,    52,    -1,    54,
      55,    -1,     4,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    74,
      75,    23,    -1,    -1,    -1,    -1,    81,    -1,    -1,    31,
      32,   142,    -1,   144,    -1,   146,   147,    39,    40,    41,
      42,    43,    44,    45,    46,    -1,   157,    49,    50,    51,
      52,    -1,    54,    55,    -1,    -1,    -1,    -1,     4,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    74,    75,    -1,    -1,    -1,    23,    -1,    81,
      -1,    -1,    -1,    -1,    -1,    31,    32,   142,    -1,   144,
      -1,   146,   147,    39,    40,    41,    42,    43,    44,    45,
      46,    -1,   157,    49,    50,    51,    52,    -1,    54,    55,
      -1,     4,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    74,    75,
      23,    -1,    -1,    -1,    -1,    81,    -1,    -1,    31,    32,
     142,    -1,   144,    -1,   146,   147,    39,    40,    41,    42,
      43,    44,    45,    46,   156,    -1,    49,    50,    51,    52,
      -1,    54,    55,    -1,    -1,    -1,    -1,     4,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    74,    75,    -1,    -1,    -1,    23,    -1,    81,    -1,
      -1,    -1,    -1,    -1,    31,    32,   142,    -1,   144,    -1,
     146,   147,    39,    40,    41,    42,    43,    44,    45,    46,
     156,    -1,    49,    50,    51,    52,    -1,    54,    55,    -1,
       4,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    74,    75,    23,
      -1,    -1,    -1,    -1,    81,    -1,    -1,    31,    32,   142,
      -1,   144,    -1,   146,   147,    39,    40,    41,    42,    43,
      44,    45,    46,   156,    -1,    49,    50,    51,    52,    -1,
      54,    55,    -1,    -1,    -1,    -1,     4,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      74,    75,    -1,    -1,    -1,    23,    -1,    81,    -1,    -1,
      -1,    -1,    -1,    31,    32,   142,    -1,   144,    -1,   146,
     147,    39,    40,    41,    42,    43,    44,    45,    46,   156,
      -1,    49,    50,    51,    52,    -1,    54,    55,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,     4,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    74,    75,    -1,    -1,
      -1,    -1,    -1,    81,    -1,    -1,    -1,    23,   142,    -1,
     144,    -1,   146,   147,    -1,    31,    32,    -1,    -1,    -1,
      -1,   155,    -1,    39,    40,    41,    42,    43,    44,    45,
      46,    -1,    -1,    49,    50,    51,    52,    -1,    54,    55,
      -1,    -1,    -1,     4,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    74,    75,
      -1,    -1,    23,    -1,   142,    81,   144,    -1,   146,   147,
      31,    32,    -1,    -1,    -1,    -1,   154,    -1,    39,    40,
      41,    42,    43,    44,    45,    46,    -1,    -1,    49,    50,
      51,    52,    -1,    54,    55,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,     4,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    74,    75,    -1,    -1,    -1,    -1,    -1,
      81,    -1,    -1,    -1,    23,    -1,   142,    -1,   144,    -1,
     146,   147,    31,    32,    -1,    -1,    -1,    -1,   154,    -1,
      39,    40,    41,    42,    43,    44,    45,    46,    -1,    -1,
      49,    50,    51,    52,    -1,    54,    55,    -1,    -1,    -1,
       4,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    74,    75,    -1,    -1,    23,
      -1,   142,    81,   144,    -1,   146,   147,    31,    32,    -1,
      -1,    -1,    -1,   154,    -1,    39,    40,    41,    42,    43,
      44,    45,    46,    -1,    -1,    49,    50,    51,    52,    -1,
      54,    55,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,     4,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      74,    75,    -1,    -1,    -1,    -1,    -1,    81,    -1,    -1,
      -1,    23,    -1,   142,    -1,   144,    -1,   146,   147,    31,
      32,    -1,    -1,    -1,    -1,   154,    -1,    39,    40,    41,
      42,    43,    44,    45,    46,    -1,    -1,    49,    50,    51,
      52,    -1,    54,    55,    -1,    -1,    -1,     4,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    74,    75,    -1,    -1,    23,    -1,   142,    81,
     144,    -1,   146,   147,    31,    32,    -1,    -1,    -1,    -1,
     154,    -1,    39,    40,    41,    42,    43,    44,    45,    46,
      -1,    -1,    49,    50,    51,    52,    -1,    54,    55,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,     4,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    74,    75,    -1,
      -1,    -1,    -1,    -1,    81,    -1,    -1,    -1,    23,    -1,
     142,    -1,   144,    -1,   146,   147,    31,    32,    -1,    -1,
      -1,    -1,   154,    -1,    39,    40,    41,    42,    43,    44,
      45,    46,    -1,    -1,    49,    50,    51,    52,    -1,    54,
      55,    -1,    -1,    -1,     4,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    74,
      75,    -1,    -1,    23,    -1,   142,    81,   144,    -1,   146,
     147,    31,    32,    -1,    -1,    -1,    -1,   154,    -1,    39,
      40,    41,    42,    43,    44,    45,    46,    -1,    -1,    49,
      50,    51,    52,    -1,    54,    55,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,     4,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    74,    75,    -1,    -1,    -1,    -1,
      -1,    81,    -1,    -1,    -1,    23,    -1,   142,    -1,   144,
      -1,   146,   147,    31,    32,    -1,    -1,    -1,    -1,   154,
      -1,    39,    40,    41,    42,    43,    44,    45,    46,    -1,
      -1,    49,    50,    51,    52,    -1,    54,    55,    -1,    -1,
      -1,     4,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    74,    75,    -1,    -1,
      23,    -1,   142,    81,   144,    -1,   146,   147,    31,    32,
      -1,    -1,    -1,    -1,   154,    -1,    39,    40,    41,    42,
      43,    44,    45,    46,    -1,    -1,    49,    50,    51,    52,
      -1,    54,    55,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,     4,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    74,    75,    -1,    -1,    -1,    -1,    -1,    81,    -1,
      -1,    -1,    23,    -1,   142,    -1,   144,    -1,   146,   147,
      31,    32,    -1,    -1,    -1,    -1,   154,    -1,    39,    40,
      41,    42,    43,    44,    45,    46,    -1,    -1,    49,    50,
      51,    52,    -1,    54,    55,    -1,    -1,    -1,     4,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    74,    75,    -1,    -1,    23,    -1,   142,
      81,   144,    -1,   146,   147,    31,    32,    -1,    -1,    -1,
      -1,   154,    -1,    39,    40,    41,    42,    43,    44,    45,
      46,    -1,    -1,    49,    50,    51,    52,    -1,    54,    55,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
       4,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    74,    75,
      -1,    -1,    -1,    -1,    -1,    81,    -1,    -1,    -1,    23,
      -1,   142,    -1,   144,    -1,   146,   147,    31,    32,    -1,
      -1,    -1,    -1,   154,    -1,    39,    40,    41,    42,    43,
      44,    45,    46,    -1,    -1,    49,    50,    51,    52,    -1,
      54,    55,    -1,    -1,    -1,     4,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      74,    75,    -1,    -1,    23,    -1,   142,    81,   144,    -1,
     146,   147,    31,    32,    -1,    -1,    -1,    -1,   154,    -1,
      39,    40,    41,    42,    43,    44,    45,    46,    -1,    -1,
      49,    50,    51,    52,    -1,    54,    55,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,     4,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    74,    75,    -1,    -1,    -1,
      -1,    -1,    81,    -1,    -1,    -1,    23,    -1,   142,    -1,
     144,    -1,   146,   147,    31,    32,    -1,    -1,    -1,    -1,
     154,    -1,    39,    40,    41,    42,    43,    44,    45,    46,
      -1,    -1,    49,    50,    51,    52,    -1,    54,    55,    -1,
      -1,    -1,     4,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    74,    75,    -1,
      -1,    23,    -1,   142,    81,   144,    -1,   146,   147,    31,
      32,    -1,    -1,    -1,    -1,   154,    -1,    39,    40,    41,
      42,    43,    44,    45,    46,    -1,    -1,    49,    50,    51,
      52,    -1,    54,    55,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,     4,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    74,    75,    -1,    -1,    -1,    -1,    -1,    81,
      -1,    -1,    -1,    23,    -1,   142,    -1,   144,    -1,   146,
     147,    31,    32,    -1,    -1,    -1,    -1,   154,    -1,    39,
      40,    41,    42,    43,    44,    45,    46,    -1,    -1,    49,
      50,    51,    52,    -1,    54,    55,    -1,    -1,    -1,     4,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    74,    75,    -1,    -1,    23,    -1,
     142,    81,   144,    -1,   146,   147,    31,    32,    -1,    -1,
      -1,    -1,   154,    -1,    39,    40,    41,    42,    43,    44,
      45,    46,    -1,    -1,    49,    50,    51,    52,    -1,    54,
      55,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,     4,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    74,
      75,    -1,    -1,    -1,    -1,    -1,    81,    -1,    -1,    -1,
      23,    -1,   142,    -1,   144,    -1,   146,   147,    31,    32,
      -1,    -1,    -1,    -1,   154,    -1,    39,    40,    41,    42,
      43,    44,    45,    46,    -1,    -1,    49,    50,    51,    52,
      -1,    54,    55,    -1,    -1,    -1,     4,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    74,    75,    -1,    -1,    23,    -1,   142,    81,   144,
      -1,   146,   147,    31,    32,    -1,    -1,    -1,    -1,   154,
      -1,    39,    40,    41,    42,    43,    44,    45,    46,    -1,
      -1,    49,    50,    51,    52,    -1,    54,    55,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,     4,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    74,    75,    -1,    -1,
      -1,    -1,    -1,    81,    -1,    -1,    -1,    23,    -1,   142,
      -1,   144,    -1,   146,   147,    31,    32,    -1,    -1,    -1,
      -1,   154,    -1,    39,    40,    41,    42,    43,    44,    45,
      46,    -1,    -1,    49,    50,    51,    52,    -1,    54,    55,
      -1,    -1,    -1,     4,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    74,    75,
      -1,    -1,    23,    -1,   142,    81,   144,    -1,   146,   147,
      31,    32,    -1,    -1,    -1,    -1,   154,    -1,    39,    40,
      41,    42,    43,    44,    45,    46,    -1,    -1,    49,    50,
      51,    52,    -1,    54,    55,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,     4,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    74,    75,    -1,    -1,    -1,    -1,    -1,
      81,    -1,    -1,    -1,    23,    -1,   142,    -1,   144,    -1,
     146,   147,    31,    32,    -1,    -1,    -1,    -1,   154,    -1,
      39,    40,    41,    42,    43,    44,    45,    46,    -1,    -1,
      49,    50,    51,    52,    -1,    54,    55,    -1,    -1,    -1,
       4,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    74,    75,    -1,    -1,    23,
      -1,   142,    81,   144,    -1,   146,   147,    31,    32,    -1,
      -1,    -1,    -1,   154,    -1,    39,    40,    41,    42,    43,
      44,    45,    46,    -1,    -1,    49,    50,    51,    52,    -1,
      54,    55,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,     4,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      74,    75,    -1,    -1,    -1,    -1,    -1,    81,    -1,    -1,
      -1,    23,    -1,   142,    -1,   144,    -1,   146,   147,    31,
      32,    -1,    -1,    -1,    -1,   154,    -1,    39,    40,    41,
      42,    43,    44,    45,    46,    -1,    -1,    49,    50,    51,
      52,    -1,    54,    55,    -1,    -1,    -1,     4,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    74,    75,    -1,    -1,    23,    -1,   142,    81,
     144,    -1,   146,   147,    31,    32,    -1,    -1,    -1,    -1,
     154,    -1,    39,    40,    41,    42,    43,    44,    45,    46,
      -1,    -1,    49,    50,    51,    52,    -1,    54,    55,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,     4,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    74,    75,    -1,
      -1,    -1,    -1,    -1,    81,    -1,    -1,    -1,    23,    -1,
     142,    -1,   144,    -1,   146,   147,    31,    32,    -1,    -1,
      -1,    -1,   154,    -1,    39,    40,    41,    42,    43,    44,
      45,    46,    -1,    -1,    49,    50,    51,    52,    -1,    54,
      55,    -1,    -1,    -1,     4,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    74,
      75,    -1,    -1,    23,    -1,   142,    81,   144,    -1,   146,
     147,    31,    32,    -1,    -1,    -1,    -1,   154,    -1,    39,
      40,    41,    42,    43,    44,    45,    46,    -1,    -1,    49,
      50,    51,    52,    -1,    54,    55,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,     4,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    74,    75,    -1,    -1,    -1,    -1,
      -1,    81,    -1,    -1,    -1,    23,    -1,   142,    -1,   144,
      -1,   146,   147,    31,    32,    -1,    -1,    -1,    -1,   154,
      -1,    39,    40,    41,    42,    43,    44,    45,    46,    -1,
      -1,    49,    50,    51,    52,    -1,    54,    55,    -1,    -1,
      -1,     4,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    74,    75,    -1,    -1,
      23,    -1,   142,    81,   144,    -1,   146,   147,    31,    32,
      -1,    -1,    -1,    -1,   154,    -1,    39,    40,    41,    42,
      43,    44,    45,    46,    -1,    -1,    49,    50,    51,    52,
      -1,    54,    55,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    74,    75,    -1,    -1,    -1,    -1,    -1,    81,    -1,
      -1,    -1,    -1,    -1,   142,    -1,   144,    -1,   146,   147,
      -1,    -1,    -1,    -1,    -1,    -1,   154,    -1,    -1,    -1,
       3,    -1,     5,    -1,    -1,    -1,    -1,    -1,    -1,    12,
      13,    14,    -1,    16,    17,    18,    19,    20,    21,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    29,    -1,    -1,    -1,
      33,    34,    -1,    -1,    -1,    -1,    -1,    -1,    -1,   142,
      43,   144,    -1,   146,   147,    -1,    -1,    -1,    -1,    -1,
      53,   154,    -1,    56,    57,    58,    59,    60,    61,    62,
      63,    64,    65,    66,    67,    -1,    -1,    70,    -1,    -1,
      73,    -1,    -1,    76,    77,    78,    79,    80,    -1,    82,
      83,    84,    85,    86,    87,    88,    89,    90,    91,    92,
      93,    94,    95,    96,    97,    -1,    -1,    -1,    -1,    -1,
       3,    -1,     5,    -1,    -1,    -1,    -1,    -1,    -1,    12,
      13,    14,    -1,    16,    17,    18,    19,    20,    21,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    29,    -1,    -1,    -1,
      33,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      43,    -1,    -1,    -1,   147,   148,    -1,   150,   151,   152,
      53,    -1,    -1,    56,    57,    58,    59,    60,    61,    62,
      63,    64,    65,    66,    67,    -1,    -1,    70,    -1,    -1,
      73,    -1,    -1,    76,    77,    78,    79,    80,    -1,    82,
      83,    84,    85,    86,    87,    88,    89,    90,    91,    92,
      93,    94,    95,    96,    97,    -1,    -1,    -1,    -1,    -1,
       3,    -1,     5,    -1,    -1,    -1,    -1,    -1,    -1,    12,
      13,    14,    -1,    16,    17,    18,    19,    20,    21,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    29,    -1,    -1,    -1,
      33,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      43,    -1,    -1,    -1,   147,   148,    -1,   150,   151,   152,
      53,    -1,    -1,    56,    57,    58,    59,    60,    61,    62,
      63,    64,    65,    66,    67,    -1,    -1,    70,    -1,    -1,
      73,    -1,    -1,    76,    77,    78,    79,    80,    -1,    82,
      83,    84,    85,    86,    87,    88,    89,    90,    91,    92,
      93,    94,    95,    96,    97,    -1,    -1,    -1,    -1,    -1,
       3,    -1,     5,    -1,    -1,     7,    -1,    -1,    -1,    12,
      13,    14,    -1,    16,    17,    18,    19,    20,    21,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    29,    -1,    -1,    -1,
      33,    -1,    -1,    -1,    36,    -1,    -1,    -1,    -1,    -1,
      43,    -1,    -1,    -1,   147,   148,    -1,   150,   151,   152,
      53,    -1,    -1,    56,    57,    58,    59,    60,    61,    62,
      63,    64,    65,    66,    67,    -1,    -1,    70,    -1,    -1,
      73,    -1,    -1,    76,    77,    78,    79,    80,    -1,    82,
      83,    84,    85,    86,    87,    88,    89,    90,    91,    92,
      93,    94,    95,    96,    97,    -1,    98,    99,   100,   101,
     102,   103,   104,   105,   106,   107,   108,   109,   110,   111,
     112,   113,   114,   115,   116,   117,   118,   119,   120,   121,
     122,   123,   124,   125,   126,   127,   128,   129,   130,   131,
     132,   133,   134,   135,   136,   137,   138,   139,   140,   141,
       4,    -1,    -1,    -1,   147,   148,   148,   150,   151,   152,
      -1,   153,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    23,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    31,    32,    -1,
      -1,    -1,    -1,    -1,    -1,    39,    40,    41,    42,    43,
      44,    45,    46,    -1,    -1,    49,    50,    51,    52,    -1,
      54,    55,    -1,     4,    -1,    -1,    -1,     8,     9,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      74,    75,    23,    -1,    -1,    -1,    -1,    81,    -1,    -1,
      31,    32,    -1,    -1,    -1,    -1,    -1,    -1,    39,    40,
      41,    42,    43,    44,    45,    46,    -1,    -1,    49,    50,
      51,    52,    -1,    54,    55,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,     4,    -1,    -1,
      -1,    -1,    -1,    74,    75,    -1,    -1,    -1,    -1,    -1,
      81,    -1,    -1,    -1,    -1,    -1,    23,    -1,   142,    -1,
     144,    28,   146,   147,    31,    32,   150,    -1,    -1,    -1,
      -1,    -1,    39,    40,    41,    42,    43,    44,    45,    46,
      -1,    -1,    49,    50,    51,    52,    -1,    54,    55,    -1,
       4,    -1,    -1,    -1,    -1,    -1,    -1,    11,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    74,    75,    23,
      -1,   142,    -1,   144,    81,   146,   147,    31,    32,    -1,
      -1,    -1,    -1,    -1,    -1,    39,    40,    41,    42,    43,
      44,    45,    46,    -1,    -1,    49,    50,    51,    52,    -1,
      54,    55,    -1,    -1,    -1,    -1,     4,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      74,    75,    -1,    -1,    -1,    23,    -1,    81,    -1,    -1,
      28,    -1,    -1,    31,    32,   142,    -1,   144,    -1,   146,
     147,    39,    40,    41,    42,    43,    44,    45,    46,    -1,
      -1,    49,    50,    51,    52,    -1,    54,    55,    -1,     4,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    74,    75,    23,    -1,
      -1,    -1,    -1,    81,    -1,    -1,    31,    32,   142,    -1,
     144,    -1,   146,   147,    39,    40,    41,    42,    43,    44,
      45,    46,    -1,    -1,    49,    50,    51,    52,    -1,    54,
      55,    -1,    -1,    -1,    -1,     4,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    74,
      75,    -1,    -1,    -1,    23,    -1,    81,    -1,    -1,    -1,
      -1,    -1,    31,    32,   142,    -1,   144,    -1,   146,   147,
      39,    40,    41,    42,    43,    44,    45,    46,    -1,    -1,
      49,    50,    51,    52,    -1,    54,    55,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    74,    75,    -1,    -1,    -1,
      -1,    -1,    81,    -1,    -1,    31,    -1,   142,    -1,   144,
      -1,   146,   147,    39,    -1,    -1,    42,    43,    44,    45,
      46,    -1,    -1,    49,    50,    51,    52,    -1,    54,    55,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    74,    75,
      -1,    -1,    -1,    -1,    -1,    81,    -1,    -1,    31,    -1,
      -1,    -1,    -1,   142,    -1,   144,    39,   146,   147,    42,
      43,    44,    45,    46,    -1,    -1,    49,    50,    51,    52,
      -1,    54,    55,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    74,    75,    -1,    -1,    -1,    -1,    -1,    81,    -1,
      -1,    31,    -1,    -1,    -1,    -1,   142,    -1,   144,    -1,
     146,   147,    42,    43,    44,    45,    46,    -1,    -1,    49,
      50,    51,    52,    -1,    54,    55,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    74,    75,    -1,    -1,    -1,    -1,
      -1,    81,    -1,    -1,    -1,    -1,    -1,    -1,    -1,   142,
      -1,   144,    -1,   146,   147,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,   144,    -1,   146,   147
};

/* YYSTOS[STATE-NUM] -- The (internal number of the) accessing
   symbol of state STATE-NUM.  */
static const yytype_uint8 yystos[] =
{
       0,     7,    36,    98,    99,   100,   101,   102,   103,   104,
     105,   106,   107,   108,   109,   110,   111,   112,   113,   114,
     115,   116,   117,   118,   119,   120,   121,   122,   123,   124,
     125,   126,   127,   128,   129,   130,   131,   132,   133,   134,
     135,   136,   137,   138,   139,   140,   141,   148,   153,   160,
     161,   162,   163,   164,   165,   166,   167,   168,   169,   170,
     171,   172,   173,   174,   175,   176,   177,   178,   179,   180,
     181,   182,   183,   184,   185,   186,   194,   249,   250,   186,
     195,   196,   147,     3,     5,    12,    13,    14,    16,    17,
      18,    19,    20,    21,    29,    33,    43,    53,    56,    57,
      58,    59,    60,    61,    62,    63,    64,    65,    66,    67,
      70,    73,    76,    77,    78,    79,    80,    82,    83,    84,
      85,    86,    87,    88,    89,    90,    91,    92,    93,    94,
      95,    96,    97,   147,   150,   151,   152,   186,   188,   189,
     190,   219,   220,   221,   222,   231,   232,   233,   234,   237,
     241,   219,   219,   219,   149,   187,   187,   187,   187,   187,
     219,   219,     5,     6,    19,    24,    25,    26,    27,    68,
     144,   147,   186,   191,   192,   201,   202,   205,   207,   209,
     210,   211,   212,   213,   214,   245,   186,   187,   187,   188,
     188,   188,   188,   188,   188,   187,   186,   219,   219,   219,
     219,   186,     0,   153,   147,   155,   157,   153,   153,   142,
      10,   157,   219,   224,   147,   147,   147,   147,   219,   147,
     147,   186,   238,   239,   240,   219,   219,   147,   219,   147,
     147,   147,   147,   147,   147,   147,   147,   147,   147,   147,
     147,   147,   186,   235,   236,   219,   147,   147,   147,   147,
     147,   147,   147,   147,   147,   147,   147,   147,   147,   147,
     147,   147,   147,   147,   147,   147,   147,   219,   224,     4,
      23,    31,    32,    39,    40,    41,    42,    43,    44,    45,
      46,    49,    50,    51,    52,    54,    55,    74,    75,    81,
     142,   144,   146,   147,     4,    23,    43,   187,   188,   191,
     186,   242,   243,   244,   147,   147,   186,   203,   204,    35,
      43,   188,   191,   206,   215,   191,   206,    72,   219,   155,
     188,   155,   186,   217,   218,   246,   247,   248,    30,   191,
     218,   186,   197,   198,   196,   154,   157,   224,   246,   247,
     247,    28,   247,   224,   142,   155,    15,   157,   219,   219,
     150,   150,   219,   219,   219,   219,   219,   219,   219,   219,
     219,   150,    38,    71,   157,   219,   219,   219,   219,   219,
     219,   219,   219,   219,   219,   219,   219,   219,   219,   219,
     219,   219,   219,   219,   219,   219,   154,   157,   219,   219,
     144,   146,   186,   227,   228,   229,   230,   219,   219,   219,
     219,   219,   219,   147,   219,   219,   219,   219,   219,   219,
     219,   150,   150,   219,   219,   219,   219,   150,   219,   186,
     188,   224,   219,   219,   188,    22,   142,   155,    15,   157,
     219,   188,   155,    69,   157,   188,    72,   157,   156,   157,
      37,   154,   154,   191,   191,   191,   157,   155,   157,   154,
     142,   142,   155,   147,    75,   219,   154,   154,   154,   154,
     219,   154,   154,   219,   191,   219,   240,   154,   154,   157,
     157,   157,   157,   157,   157,   157,   157,   157,   157,   154,
     157,   219,   236,   157,   157,   157,   157,   157,   154,   157,
     157,   157,   157,   157,   157,   157,   157,   157,   157,   157,
     157,   157,   157,   157,   219,   219,   186,   188,   157,    38,
     144,   146,   186,   219,   155,   156,   154,   191,   219,    30,
     191,   244,   154,   157,   154,   191,   204,   191,   191,   191,
      35,    43,   188,   216,    72,   142,   217,   191,   246,   155,
     145,   191,   193,   208,   219,    30,   191,   186,   199,   200,
     198,   155,   155,   155,     8,     9,   223,   155,   142,   224,
     219,   219,   219,   219,   219,   219,   219,   219,   219,   219,
     219,   219,   219,   219,   219,   150,   150,   219,   219,   219,
     219,   150,   150,   150,   150,   150,   219,   219,   219,   219,
     154,   156,   227,   219,   219,   186,   188,   157,   150,   142,
     219,   156,   188,   156,   191,   219,   191,   218,   155,   154,
     157,   219,    34,   219,   225,   226,   219,   226,   219,   219,
     219,   219,   154,   157,   154,   154,   154,   154,   154,   154,
     154,   154,   157,   154,   154,   154,   154,   154,   157,   154,
     154,   154,   154,   154,   154,   154,   154,   154,   154,   154,
     154,   154,   154,   156,   219,   156,   219,   154,   144,   142,
     158,   191,   200,   147,   219,   225,   219,    11,    28,   219,
     219,   150,   154,   186,   219,   224,   219,   154,   154,   154,
      38,   154,   223,   219,   155,   156
};

#define yyerrok		(yyerrstatus = 0)
#define yyclearin	(yychar = YYEMPTY)
#define YYEMPTY		(-2)
#define YYEOF		0

#define YYACCEPT	goto yyacceptlab
#define YYABORT		goto yyabortlab
#define YYERROR		goto yyerrorlab


/* Like YYERROR except do call yyerror.  This remains here temporarily
   to ease the transition to the new meaning of YYERROR, for GCC.
   Once GCC version 2 has supplanted version 1, this can go.  */

#define YYFAIL		goto yyerrlab

#define YYRECOVERING()  (!!yyerrstatus)

#define YYBACKUP(Token, Value)					\
do								\
  if (yychar == YYEMPTY && yylen == 1)				\
    {								\
      yychar = (Token);						\
      yylval = (Value);						\
      yytoken = YYTRANSLATE (yychar);				\
      YYPOPSTACK (1);						\
      goto yybackup;						\
    }								\
  else								\
    {								\
      yyerror (YY_("syntax error: cannot back up")); \
      YYERROR;							\
    }								\
while (YYID (0))


#define YYTERROR	1
#define YYERRCODE	256


/* YYLLOC_DEFAULT -- Set CURRENT to span from RHS[1] to RHS[N].
   If N is 0, then set CURRENT to the empty location which ends
   the previous symbol: RHS[0] (always defined).  */

#define YYRHSLOC(Rhs, K) ((Rhs)[K])
#ifndef YYLLOC_DEFAULT
# define YYLLOC_DEFAULT(Current, Rhs, N)				\
    do									\
      if (YYID (N))                                                    \
	{								\
	  (Current).first_line   = YYRHSLOC (Rhs, 1).first_line;	\
	  (Current).first_column = YYRHSLOC (Rhs, 1).first_column;	\
	  (Current).last_line    = YYRHSLOC (Rhs, N).last_line;		\
	  (Current).last_column  = YYRHSLOC (Rhs, N).last_column;	\
	}								\
      else								\
	{								\
	  (Current).first_line   = (Current).last_line   =		\
	    YYRHSLOC (Rhs, 0).last_line;				\
	  (Current).first_column = (Current).last_column =		\
	    YYRHSLOC (Rhs, 0).last_column;				\
	}								\
    while (YYID (0))
#endif


/* YY_LOCATION_PRINT -- Print the location on the stream.
   This macro was not mandated originally: define only if we know
   we won't break user code: when these are the locations we know.  */

#ifndef YY_LOCATION_PRINT
# if YYLTYPE_IS_TRIVIAL
#  define YY_LOCATION_PRINT(File, Loc)			\
     fprintf (File, "%d.%d-%d.%d",			\
	      (Loc).first_line, (Loc).first_column,	\
	      (Loc).last_line,  (Loc).last_column)
# else
#  define YY_LOCATION_PRINT(File, Loc) ((void) 0)
# endif
#endif


/* YYLEX -- calling `yylex' with the right arguments.  */

#ifdef YYLEX_PARAM
# define YYLEX yylex (YYLEX_PARAM)
#else
# define YYLEX yylex ()
#endif

/* Enable debugging if requested.  */
#if YYDEBUG

# ifndef YYFPRINTF
#  include <stdio.h> /* INFRINGES ON USER NAME SPACE */
#  define YYFPRINTF fprintf
# endif

# define YYDPRINTF(Args)			\
do {						\
  if (yydebug)					\
    YYFPRINTF Args;				\
} while (YYID (0))

# define YY_SYMBOL_PRINT(Title, Type, Value, Location)			  \
do {									  \
  if (yydebug)								  \
    {									  \
      YYFPRINTF (stderr, "%s ", Title);					  \
      yy_symbol_print (stderr,						  \
		  Type, Value); \
      YYFPRINTF (stderr, "\n");						  \
    }									  \
} while (YYID (0))


/*--------------------------------.
| Print this symbol on YYOUTPUT.  |
`--------------------------------*/

/*ARGSUSED*/
#if (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
static void
yy_symbol_value_print (FILE *yyoutput, int yytype, YYSTYPE const * const yyvaluep)
#else
static void
yy_symbol_value_print (yyoutput, yytype, yyvaluep)
    FILE *yyoutput;
    int yytype;
    YYSTYPE const * const yyvaluep;
#endif
{
  if (!yyvaluep)
    return;
# ifdef YYPRINT
  if (yytype < YYNTOKENS)
    YYPRINT (yyoutput, yytoknum[yytype], *yyvaluep);
# else
  YYUSE (yyoutput);
# endif
  switch (yytype)
    {
      default:
	break;
    }
}


/*--------------------------------.
| Print this symbol on YYOUTPUT.  |
`--------------------------------*/

#if (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
static void
yy_symbol_print (FILE *yyoutput, int yytype, YYSTYPE const * const yyvaluep)
#else
static void
yy_symbol_print (yyoutput, yytype, yyvaluep)
    FILE *yyoutput;
    int yytype;
    YYSTYPE const * const yyvaluep;
#endif
{
  if (yytype < YYNTOKENS)
    YYFPRINTF (yyoutput, "token %s (", yytname[yytype]);
  else
    YYFPRINTF (yyoutput, "nterm %s (", yytname[yytype]);

  yy_symbol_value_print (yyoutput, yytype, yyvaluep);
  YYFPRINTF (yyoutput, ")");
}

/*------------------------------------------------------------------.
| yy_stack_print -- Print the state stack from its BOTTOM up to its |
| TOP (included).                                                   |
`------------------------------------------------------------------*/

#if (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
static void
yy_stack_print (yytype_int16 *bottom, yytype_int16 *top)
#else
static void
yy_stack_print (bottom, top)
    yytype_int16 *bottom;
    yytype_int16 *top;
#endif
{
  YYFPRINTF (stderr, "Stack now");
  for (; bottom <= top; ++bottom)
    YYFPRINTF (stderr, " %d", *bottom);
  YYFPRINTF (stderr, "\n");
}

# define YY_STACK_PRINT(Bottom, Top)				\
do {								\
  if (yydebug)							\
    yy_stack_print ((Bottom), (Top));				\
} while (YYID (0))


/*------------------------------------------------.
| Report that the YYRULE is going to be reduced.  |
`------------------------------------------------*/

#if (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
static void
yy_reduce_print (YYSTYPE *yyvsp, int yyrule)
#else
static void
yy_reduce_print (yyvsp, yyrule)
    YYSTYPE *yyvsp;
    int yyrule;
#endif
{
  int yynrhs = yyr2[yyrule];
  int yyi;
  unsigned long int yylno = yyrline[yyrule];
  YYFPRINTF (stderr, "Reducing stack by rule %d (line %lu):\n",
	     yyrule - 1, yylno);
  /* The symbols being reduced.  */
  for (yyi = 0; yyi < yynrhs; yyi++)
    {
      fprintf (stderr, "   $%d = ", yyi + 1);
      yy_symbol_print (stderr, yyrhs[yyprhs[yyrule] + yyi],
		       &(yyvsp[(yyi + 1) - (yynrhs)])
		       		       );
      fprintf (stderr, "\n");
    }
}

# define YY_REDUCE_PRINT(Rule)		\
do {					\
  if (yydebug)				\
    yy_reduce_print (yyvsp, Rule); \
} while (YYID (0))

/* Nonzero means print parse trace.  It is left uninitialized so that
   multiple parsers can coexist.  */
int yydebug;
#else /* !YYDEBUG */
# define YYDPRINTF(Args)
# define YY_SYMBOL_PRINT(Title, Type, Value, Location)
# define YY_STACK_PRINT(Bottom, Top)
# define YY_REDUCE_PRINT(Rule)
#endif /* !YYDEBUG */


/* YYINITDEPTH -- initial size of the parser's stacks.  */
#ifndef	YYINITDEPTH
# define YYINITDEPTH 200
#endif

/* YYMAXDEPTH -- maximum size the stacks can grow to (effective only
   if the built-in stack extension method is used).

   Do not make this value too large; the results are undefined if
   YYSTACK_ALLOC_MAXIMUM < YYSTACK_BYTES (YYMAXDEPTH)
   evaluated with infinite-precision integer arithmetic.  */

#ifndef YYMAXDEPTH
# define YYMAXDEPTH 10000
#endif



#if YYERROR_VERBOSE

# ifndef yystrlen
#  if defined __GLIBC__ && defined _STRING_H
#   define yystrlen strlen
#  else
/* Return the length of YYSTR.  */
#if (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
static YYSIZE_T
yystrlen (const char *yystr)
#else
static YYSIZE_T
yystrlen (yystr)
    const char *yystr;
#endif
{
  YYSIZE_T yylen;
  for (yylen = 0; yystr[yylen]; yylen++)
    continue;
  return yylen;
}
#  endif
# endif

# ifndef yystpcpy
#  if defined __GLIBC__ && defined _STRING_H && defined _GNU_SOURCE
#   define yystpcpy stpcpy
#  else
/* Copy YYSRC to YYDEST, returning the address of the terminating '\0' in
   YYDEST.  */
#if (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
static char *
yystpcpy (char *yydest, const char *yysrc)
#else
static char *
yystpcpy (yydest, yysrc)
    char *yydest;
    const char *yysrc;
#endif
{
  char *yyd = yydest;
  const char *yys = yysrc;

  while ((*yyd++ = *yys++) != '\0')
    continue;

  return yyd - 1;
}
#  endif
# endif

# ifndef yytnamerr
/* Copy to YYRES the contents of YYSTR after stripping away unnecessary
   quotes and backslashes, so that it's suitable for yyerror.  The
   heuristic is that double-quoting is unnecessary unless the string
   contains an apostrophe, a comma, or backslash (other than
   backslash-backslash).  YYSTR is taken from yytname.  If YYRES is
   null, do not copy; instead, return the length of what the result
   would have been.  */
static YYSIZE_T
yytnamerr (char *yyres, const char *yystr)
{
  if (*yystr == '"')
    {
      YYSIZE_T yyn = 0;
      char const *yyp = yystr;

      for (;;)
	switch (*++yyp)
	  {
	  case '\'':
	  case ',':
	    goto do_not_strip_quotes;

	  case '\\':
	    if (*++yyp != '\\')
	      goto do_not_strip_quotes;
	    /* Fall through.  */
	  default:
	    if (yyres)
	      yyres[yyn] = *yyp;
	    yyn++;
	    break;

	  case '"':
	    if (yyres)
	      yyres[yyn] = '\0';
	    return yyn;
	  }
    do_not_strip_quotes: ;
    }

  if (! yyres)
    return yystrlen (yystr);

  return yystpcpy (yyres, yystr) - yyres;
}
# endif

/* Copy into YYRESULT an error message about the unexpected token
   YYCHAR while in state YYSTATE.  Return the number of bytes copied,
   including the terminating null byte.  If YYRESULT is null, do not
   copy anything; just return the number of bytes that would be
   copied.  As a special case, return 0 if an ordinary "syntax error"
   message will do.  Return YYSIZE_MAXIMUM if overflow occurs during
   size calculation.  */
static YYSIZE_T
yysyntax_error (char *yyresult, int yystate, int yychar)
{
  int yyn = yypact[yystate];

  if (! (YYPACT_NINF < yyn && yyn <= YYLAST))
    return 0;
  else
    {
      int yytype = YYTRANSLATE (yychar);
      YYSIZE_T yysize0 = yytnamerr (0, yytname[yytype]);
      YYSIZE_T yysize = yysize0;
      YYSIZE_T yysize1;
      int yysize_overflow = 0;
      enum { YYERROR_VERBOSE_ARGS_MAXIMUM = 5 };
      char const *yyarg[YYERROR_VERBOSE_ARGS_MAXIMUM];
      int yyx;

# if 0
      /* This is so xgettext sees the translatable formats that are
	 constructed on the fly.  */
      YY_("syntax error, unexpected %s");
      YY_("syntax error, unexpected %s, expecting %s");
      YY_("syntax error, unexpected %s, expecting %s or %s");
      YY_("syntax error, unexpected %s, expecting %s or %s or %s");
      YY_("syntax error, unexpected %s, expecting %s or %s or %s or %s");
# endif
      char *yyfmt;
      char const *yyf;
      static char const yyunexpected[] = "syntax error, unexpected %s";
      static char const yyexpecting[] = ", expecting %s";
      static char const yyor[] = " or %s";
      char yyformat[sizeof yyunexpected
		    + sizeof yyexpecting - 1
		    + ((YYERROR_VERBOSE_ARGS_MAXIMUM - 2)
		       * (sizeof yyor - 1))];
      char const *yyprefix = yyexpecting;

      /* Start YYX at -YYN if negative to avoid negative indexes in
	 YYCHECK.  */
      int yyxbegin = yyn < 0 ? -yyn : 0;

      /* Stay within bounds of both yycheck and yytname.  */
      int yychecklim = YYLAST - yyn + 1;
      int yyxend = yychecklim < YYNTOKENS ? yychecklim : YYNTOKENS;
      int yycount = 1;

      yyarg[0] = yytname[yytype];
      yyfmt = yystpcpy (yyformat, yyunexpected);

      for (yyx = yyxbegin; yyx < yyxend; ++yyx)
	if (yycheck[yyx + yyn] == yyx && yyx != YYTERROR)
	  {
	    if (yycount == YYERROR_VERBOSE_ARGS_MAXIMUM)
	      {
		yycount = 1;
		yysize = yysize0;
		yyformat[sizeof yyunexpected - 1] = '\0';
		break;
	      }
	    yyarg[yycount++] = yytname[yyx];
	    yysize1 = yysize + yytnamerr (0, yytname[yyx]);
	    yysize_overflow |= (yysize1 < yysize);
	    yysize = yysize1;
	    yyfmt = yystpcpy (yyfmt, yyprefix);
	    yyprefix = yyor;
	  }

      yyf = YY_(yyformat);
      yysize1 = yysize + yystrlen (yyf);
      yysize_overflow |= (yysize1 < yysize);
      yysize = yysize1;

      if (yysize_overflow)
	return YYSIZE_MAXIMUM;

      if (yyresult)
	{
	  /* Avoid sprintf, as that infringes on the user's name space.
	     Don't have undefined behavior even if the translation
	     produced a string with the wrong number of "%s"s.  */
	  char *yyp = yyresult;
	  int yyi = 0;
	  while ((*yyp = *yyf) != '\0')
	    {
	      if (*yyp == '%' && yyf[1] == 's' && yyi < yycount)
		{
		  yyp += yytnamerr (yyp, yyarg[yyi++]);
		  yyf += 2;
		}
	      else
		{
		  yyp++;
		  yyf++;
		}
	    }
	}
      return yysize;
    }
}
#endif /* YYERROR_VERBOSE */


/*-----------------------------------------------.
| Release the memory associated to this symbol.  |
`-----------------------------------------------*/

/*ARGSUSED*/
#if (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
static void
yydestruct (const char *yymsg, int yytype, YYSTYPE *yyvaluep)
#else
static void
yydestruct (yymsg, yytype, yyvaluep)
    const char *yymsg;
    int yytype;
    YYSTYPE *yyvaluep;
#endif
{
  YYUSE (yyvaluep);

  if (!yymsg)
    yymsg = "Deleting";
  YY_SYMBOL_PRINT (yymsg, yytype, yyvaluep, yylocationp);

  switch (yytype)
    {

      default:
	break;
    }
}


/* Prevent warnings from -Wmissing-prototypes.  */

#ifdef YYPARSE_PARAM
#if defined __STDC__ || defined __cplusplus
int yyparse (void *YYPARSE_PARAM);
#else
int yyparse ();
#endif
#else /* ! YYPARSE_PARAM */
#if defined __STDC__ || defined __cplusplus
int yyparse (void);
#else
int yyparse ();
#endif
#endif /* ! YYPARSE_PARAM */



/* The look-ahead symbol.  */
int yychar;

/* The semantic value of the look-ahead symbol.  */
YYSTYPE yylval;

/* Number of syntax errors so far.  */
int yynerrs;



/*----------.
| yyparse.  |
`----------*/

#ifdef YYPARSE_PARAM
#if (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
int
yyparse (void *YYPARSE_PARAM)
#else
int
yyparse (YYPARSE_PARAM)
    void *YYPARSE_PARAM;
#endif
#else /* ! YYPARSE_PARAM */
#if (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
int
yyparse (void)
#else
int
yyparse ()

#endif
#endif
{
  
  int yystate;
  int yyn;
  int yyresult;
  /* Number of tokens to shift before error messages enabled.  */
  int yyerrstatus;
  /* Look-ahead token as an internal (translated) token number.  */
  int yytoken = 0;
#if YYERROR_VERBOSE
  /* Buffer for error messages, and its allocated size.  */
  char yymsgbuf[128];
  char *yymsg = yymsgbuf;
  YYSIZE_T yymsg_alloc = sizeof yymsgbuf;
#endif

  /* Three stacks and their tools:
     `yyss': related to states,
     `yyvs': related to semantic values,
     `yyls': related to locations.

     Refer to the stacks thru separate pointers, to allow yyoverflow
     to reallocate them elsewhere.  */

  /* The state stack.  */
  yytype_int16 yyssa[YYINITDEPTH];
  yytype_int16 *yyss = yyssa;
  yytype_int16 *yyssp;

  /* The semantic value stack.  */
  YYSTYPE yyvsa[YYINITDEPTH];
  YYSTYPE *yyvs = yyvsa;
  YYSTYPE *yyvsp;



#define YYPOPSTACK(N)   (yyvsp -= (N), yyssp -= (N))

  YYSIZE_T yystacksize = YYINITDEPTH;

  /* The variables used to return semantic value and location from the
     action routines.  */
  YYSTYPE yyval;


  /* The number of symbols on the RHS of the reduced rule.
     Keep to zero when no symbol should be popped.  */
  int yylen = 0;

  YYDPRINTF ((stderr, "Starting parse\n"));

  yystate = 0;
  yyerrstatus = 0;
  yynerrs = 0;
  yychar = YYEMPTY;		/* Cause a token to be read.  */

  /* Initialize stack pointers.
     Waste one element of value and location stack
     so that they stay on the same level as the state stack.
     The wasted elements are never initialized.  */

  yyssp = yyss;
  yyvsp = yyvs;

  goto yysetstate;

/*------------------------------------------------------------.
| yynewstate -- Push a new state, which is found in yystate.  |
`------------------------------------------------------------*/
 yynewstate:
  /* In all cases, when you get here, the value and location stacks
     have just been pushed.  So pushing a state here evens the stacks.  */
  yyssp++;

 yysetstate:
  *yyssp = yystate;

  if (yyss + yystacksize - 1 <= yyssp)
    {
      /* Get the current used size of the three stacks, in elements.  */
      YYSIZE_T yysize = yyssp - yyss + 1;

#ifdef yyoverflow
      {
	/* Give user a chance to reallocate the stack.  Use copies of
	   these so that the &'s don't force the real ones into
	   memory.  */
	YYSTYPE *yyvs1 = yyvs;
	yytype_int16 *yyss1 = yyss;


	/* Each stack pointer address is followed by the size of the
	   data in use in that stack, in bytes.  This used to be a
	   conditional around just the two extra args, but that might
	   be undefined if yyoverflow is a macro.  */
	yyoverflow (YY_("memory exhausted"),
		    &yyss1, yysize * sizeof (*yyssp),
		    &yyvs1, yysize * sizeof (*yyvsp),

		    &yystacksize);

	yyss = yyss1;
	yyvs = yyvs1;
      }
#else /* no yyoverflow */
# ifndef YYSTACK_RELOCATE
      goto yyexhaustedlab;
# else
      /* Extend the stack our own way.  */
      if (YYMAXDEPTH <= yystacksize)
	goto yyexhaustedlab;
      yystacksize *= 2;
      if (YYMAXDEPTH < yystacksize)
	yystacksize = YYMAXDEPTH;

      {
	yytype_int16 *yyss1 = yyss;
	union yyalloc *yyptr =
	  (union yyalloc *) YYSTACK_ALLOC (YYSTACK_BYTES (yystacksize));
	if (! yyptr)
	  goto yyexhaustedlab;
	YYSTACK_RELOCATE (yyss);
	YYSTACK_RELOCATE (yyvs);

#  undef YYSTACK_RELOCATE
	if (yyss1 != yyssa)
	  YYSTACK_FREE (yyss1);
      }
# endif
#endif /* no yyoverflow */

      yyssp = yyss + yysize - 1;
      yyvsp = yyvs + yysize - 1;


      YYDPRINTF ((stderr, "Stack size increased to %lu\n",
		  (unsigned long int) yystacksize));

      if (yyss + yystacksize - 1 <= yyssp)
	YYABORT;
    }

  YYDPRINTF ((stderr, "Entering state %d\n", yystate));

  goto yybackup;

/*-----------.
| yybackup.  |
`-----------*/
yybackup:

  /* Do appropriate processing given the current state.  Read a
     look-ahead token if we need one and don't already have one.  */

  /* First try to decide what to do without reference to look-ahead token.  */
  yyn = yypact[yystate];
  if (yyn == YYPACT_NINF)
    goto yydefault;

  /* Not known => get a look-ahead token if don't already have one.  */

  /* YYCHAR is either YYEMPTY or YYEOF or a valid look-ahead symbol.  */
  if (yychar == YYEMPTY)
    {
      YYDPRINTF ((stderr, "Reading a token: "));
      yychar = YYLEX;
    }

  if (yychar <= YYEOF)
    {
      yychar = yytoken = YYEOF;
      YYDPRINTF ((stderr, "Now at end of input.\n"));
    }
  else
    {
      yytoken = YYTRANSLATE (yychar);
      YY_SYMBOL_PRINT ("Next token is", yytoken, &yylval, &yylloc);
    }

  /* If the proper action on seeing token YYTOKEN is to reduce or to
     detect an error, take that action.  */
  yyn += yytoken;
  if (yyn < 0 || YYLAST < yyn || yycheck[yyn] != yytoken)
    goto yydefault;
  yyn = yytable[yyn];
  if (yyn <= 0)
    {
      if (yyn == 0 || yyn == YYTABLE_NINF)
	goto yyerrlab;
      yyn = -yyn;
      goto yyreduce;
    }

  if (yyn == YYFINAL)
    YYACCEPT;

  /* Count tokens shifted since error; after three, turn off error
     status.  */
  if (yyerrstatus)
    yyerrstatus--;

  /* Shift the look-ahead token.  */
  YY_SYMBOL_PRINT ("Shifting", yytoken, &yylval, &yylloc);

  /* Discard the shifted token unless it is eof.  */
  if (yychar != YYEOF)
    yychar = YYEMPTY;

  yystate = yyn;
  *++yyvsp = yylval;

  goto yynewstate;


/*-----------------------------------------------------------.
| yydefault -- do the default action for the current state.  |
`-----------------------------------------------------------*/
yydefault:
  yyn = yydefact[yystate];
  if (yyn == 0)
    goto yyerrlab;
  goto yyreduce;


/*-----------------------------.
| yyreduce -- Do a reduction.  |
`-----------------------------*/
yyreduce:
  /* yyn is the number of a rule to reduce with.  */
  yylen = yyr2[yyn];

  /* If YYLEN is nonzero, implement the default value of the action:
     `$$ = $1'.

     Otherwise, the following line sets YYVAL to garbage.
     This behavior is undocumented and Bison
     users should not rely upon it.  Assigning to YYVAL
     unconditionally makes the parser a bit smaller, and it avoids a
     GCC warning that YYVAL may be used uninitialized.  */
  yyval = yyvsp[1-yylen];


  YY_REDUCE_PRINT (yyn);
  switch (yyn)
    {
        case 2:
#line 403 "PL.y"
    {
			  EXPR = *(yyvsp[(1) - (2)].node);
			  delete (yyvsp[(1) - (2)].node);
			  YYACCEPT;
			}
    break;

  case 3:
#line 409 "PL.y"
    {
			  EXPR = *(yyvsp[(1) - (2)].node);
			  delete (yyvsp[(1) - (2)].node);
			  YYACCEPT;
			}
    break;

  case 4:
#line 414 "PL.y"
    {
			  EXPR = *(yyvsp[(1) - (2)].node);
			  delete (yyvsp[(1) - (2)].node);
			  YYACCEPT;
			}
    break;

  case 5:
#line 420 "PL.y"
    {
			  EXPR = CVC3::Expr();
			  YYACCEPT;
			}
    break;

  case 6:
#line 425 "PL.y"
    {
			  TMP->done = true;
			  EXPR = CVC3::Expr();
			  YYACCEPT;
			}
    break;

  case 7:
#line 432 "PL.y"
    { (yyval.node) = (yyvsp[(1) - (1)].node); }
    break;

  case 8:
#line 433 "PL.y"
    { (yyval.node) = (yyvsp[(1) - (1)].node); }
    break;

  case 9:
#line 434 "PL.y"
    { (yyval.node) = (yyvsp[(1) - (1)].node); }
    break;

  case 10:
#line 435 "PL.y"
    { (yyval.node) = (yyvsp[(1) - (1)].node); }
    break;

  case 11:
#line 436 "PL.y"
    { (yyval.node) = (yyvsp[(1) - (1)].node); }
    break;

  case 12:
#line 437 "PL.y"
    { (yyval.node) = (yyvsp[(1) - (1)].node); }
    break;

  case 13:
#line 438 "PL.y"
    { (yyval.node) = (yyvsp[(1) - (1)].node); }
    break;

  case 14:
#line 439 "PL.y"
    { (yyval.node) = (yyvsp[(1) - (1)].node); }
    break;

  case 15:
#line 440 "PL.y"
    { (yyval.node) = (yyvsp[(1) - (1)].node); }
    break;

  case 16:
#line 441 "PL.y"
    { (yyval.node) = (yyvsp[(1) - (1)].node); }
    break;

  case 17:
#line 442 "PL.y"
    { (yyval.node) = (yyvsp[(1) - (1)].node); }
    break;

  case 18:
#line 443 "PL.y"
    { (yyval.node) = (yyvsp[(1) - (1)].node); }
    break;

  case 19:
#line 444 "PL.y"
    { (yyval.node) = (yyvsp[(1) - (1)].node); }
    break;

  case 20:
#line 445 "PL.y"
    { (yyval.node) = (yyvsp[(1) - (1)].node); }
    break;

  case 21:
#line 446 "PL.y"
    { (yyval.node) = (yyvsp[(1) - (1)].node); }
    break;

  case 22:
#line 447 "PL.y"
    { (yyval.node) = (yyvsp[(1) - (1)].node); }
    break;

  case 23:
#line 448 "PL.y"
    { (yyval.node) = (yyvsp[(1) - (1)].node); }
    break;

  case 24:
#line 449 "PL.y"
    { (yyval.node) = (yyvsp[(1) - (1)].node); }
    break;

  case 25:
#line 450 "PL.y"
    { (yyval.node) = (yyvsp[(1) - (1)].node); }
    break;

  case 26:
#line 451 "PL.y"
    { (yyval.node) = (yyvsp[(1) - (1)].node); }
    break;

  case 27:
#line 452 "PL.y"
    { (yyval.node) = (yyvsp[(1) - (1)].node); }
    break;

  case 28:
#line 453 "PL.y"
    { (yyval.node) = (yyvsp[(1) - (1)].node); }
    break;

  case 29:
#line 454 "PL.y"
    { (yyval.node) = (yyvsp[(1) - (1)].node); }
    break;

  case 30:
#line 455 "PL.y"
    { (yyval.node) = (yyvsp[(1) - (1)].node); }
    break;

  case 31:
#line 459 "PL.y"
    {
                            (yyval.node) = new CVC3::Expr(VC->listExpr("_ARITH_VAR_ORDER", *(yyvsp[(3) - (4)].vec)));
                            delete (yyvsp[(3) - (4)].vec);
                        }
    break;

  case 32:
#line 465 "PL.y"
    { 

                          (yyval.node) = new CVC3::Expr(VC->listExpr("_ASSERT", *(yyvsp[(2) - (2)].node)));
			  delete (yyvsp[(2) - (2)].node);
                        }
    break;

  case 33:
#line 472 "PL.y"
    { 
                          (yyval.node) = new CVC3::Expr(VC->listExpr("_QUERY", *(yyvsp[(2) - (2)].node)));
			  delete (yyvsp[(2) - (2)].node);
                        }
    break;

  case 34:
#line 476 "PL.y"
    {
                          (yyval.node) = new CVC3::Expr(VC->listExpr("_CHECKSAT", *(yyvsp[(2) - (2)].node)));
                          delete (yyvsp[(2) - (2)].node);
                        }
    break;

  case 35:
#line 480 "PL.y"
    {
                          (yyval.node) = new CVC3::Expr(VC->listExpr(VC->idExpr("_CHECKSAT")));
                        }
    break;

  case 36:
#line 483 "PL.y"
    {
                          (yyval.node) = new CVC3::Expr(VC->listExpr(VC->idExpr("_CONTINUE")));
                        }
    break;

  case 37:
#line 486 "PL.y"
    {
                          (yyval.node) = new CVC3::Expr(VC->listExpr("_RESTART", *(yyvsp[(2) - (2)].node)));
                          delete (yyvsp[(2) - (2)].node);
                        }
    break;

  case 38:
#line 491 "PL.y"
    { 
                          (yyval.node) = new CVC3::Expr(VC->listExpr("_DBG", *(yyvsp[(2) - (2)].node)));
			  delete (yyvsp[(2) - (2)].node);
                        }
    break;

  case 39:
#line 495 "PL.y"
    {
                          (yyval.node) = new CVC3::Expr(VC->listExpr(VC->idExpr("_DBG")));
		}
    break;

  case 40:
#line 499 "PL.y"
    { 
                          (yyval.node) = new CVC3::Expr(VC->listExpr("_TRACE", *(yyvsp[(2) - (2)].node)));
			  delete (yyvsp[(2) - (2)].node);
                        }
    break;

  case 41:
#line 503 "PL.y"
    { 
                          (yyval.node) = new CVC3::Expr(VC->listExpr("_UNTRACE", *(yyvsp[(2) - (2)].node)));
			  delete (yyvsp[(2) - (2)].node);
                        }
    break;

  case 42:
#line 508 "PL.y"
    { 
                          (yyval.node) = new CVC3::Expr(VC->listExpr("_OPTION",  *(yyvsp[(2) - (3)].node), *(yyvsp[(3) - (3)].node)));
			  delete (yyvsp[(2) - (3)].node);
			  delete (yyvsp[(3) - (3)].node);
                        }
    break;

  case 43:
#line 513 "PL.y"
    {
			  CVC3::Rational value= -(yyvsp[(4) - (4)].node)->getRational();
                          CVC3::Expr e = CVC3::Expr(VC->ratExpr(value.toString()));
                          (yyval.node) = new CVC3::Expr(VC->listExpr("_OPTION",  *(yyvsp[(2) - (4)].node), e));
			  delete (yyvsp[(2) - (4)].node);
			  delete (yyvsp[(4) - (4)].node);
                        }
    break;

  case 44:
#line 520 "PL.y"
    { 
                          (yyval.node) = new CVC3::Expr(VC->listExpr("_OPTION",  *(yyvsp[(2) - (3)].node),  *(yyvsp[(3) - (3)].node)));
			  delete (yyvsp[(2) - (3)].node);
			  delete (yyvsp[(3) - (3)].node);
                        }
    break;

  case 45:
#line 526 "PL.y"
    { 
                          (yyval.node) = new CVC3::Expr(VC->listExpr("_HELP", *(yyvsp[(2) - (2)].node)));
			  delete (yyvsp[(2) - (2)].node);
                        }
    break;

  case 46:
#line 530 "PL.y"
    {
                          (yyval.node) = new CVC3::Expr(VC->listExpr(VC->idExpr("_HELP")));
		}
    break;

  case 47:
#line 535 "PL.y"
    { 
                          (yyval.node) = new CVC3::Expr(VC->listExpr("_TRANSFORM", *(yyvsp[(2) - (2)].node)));
			  delete (yyvsp[(2) - (2)].node);
                        }
    break;

  case 48:
#line 541 "PL.y"
    { 
                          (yyval.node) = new CVC3::Expr(VC->listExpr("_PRINT", *(yyvsp[(2) - (2)].node)));
			  delete (yyvsp[(2) - (2)].node);
                        }
    break;

  case 49:
#line 545 "PL.y"
    { 
                          (yyval.node) = new CVC3::Expr(VC->listExpr("_PRINT", *(yyvsp[(2) - (2)].node)));
			  delete (yyvsp[(2) - (2)].node);
                        }
    break;

  case 50:
#line 551 "PL.y"
    { 
                          (yyval.node) = new CVC3::Expr(VC->listExpr("_CALL", *(yyvsp[(2) - (3)].node), *(yyvsp[(3) - (3)].node)));
			  delete (yyvsp[(2) - (3)].node);
			  delete (yyvsp[(3) - (3)].node);
                        }
    break;

  case 51:
#line 558 "PL.y"
    { 
                          (yyval.node) = new CVC3::Expr(VC->listExpr("_ECHO", *(yyvsp[(2) - (2)].node)));
			  delete (yyvsp[(2) - (2)].node);
                        }
    break;

  case 52:
#line 562 "PL.y"
    { 
                          (yyval.node) = new CVC3::Expr(VC->listExpr(VC->idExpr("_ECHO")));
                        }
    break;

  case 53:
#line 567 "PL.y"
    { 
                          (yyval.node) = new CVC3::Expr(VC->listExpr("_INCLUDE",  *(yyvsp[(2) - (2)].node)));
			  delete (yyvsp[(2) - (2)].node);
                        }
    break;

  case 54:
#line 573 "PL.y"
    { 
                          (yyval.node) = new CVC3::Expr(VC->listExpr(VC->idExpr("_DUMP_PROOF")));
                        }
    break;

  case 55:
#line 576 "PL.y"
    { 
                          (yyval.node) = new CVC3::Expr(VC->listExpr(VC->idExpr("_DUMP_ASSUMPTIONS")));
                        }
    break;

  case 56:
#line 579 "PL.y"
    { 
                          (yyval.node) = new CVC3::Expr(VC->listExpr(VC->idExpr("_DUMP_SIG")));
                        }
    break;

  case 57:
#line 582 "PL.y"
    { 
                          (yyval.node) = new CVC3::Expr(VC->listExpr(VC->idExpr("_DUMP_TCC")));
                        }
    break;

  case 58:
#line 585 "PL.y"
    { 
                          (yyval.node) = new CVC3::Expr(VC->listExpr(VC->idExpr("_DUMP_TCC_ASSUMPTIONS")));
                        }
    break;

  case 59:
#line 588 "PL.y"
    { 
                          (yyval.node) = new CVC3::Expr(VC->listExpr(VC->idExpr("_DUMP_TCC_PROOF")));
                        }
    break;

  case 60:
#line 591 "PL.y"
    { 
                          (yyval.node) = new CVC3::Expr(VC->listExpr(VC->idExpr("_DUMP_CLOSURE")));
                        }
    break;

  case 61:
#line 594 "PL.y"
    { 
                          (yyval.node) = new CVC3::Expr(VC->listExpr(VC->idExpr("_DUMP_CLOSURE_PROOF")));
                        }
    break;

  case 62:
#line 599 "PL.y"
    {
                          (yyval.node) = new CVC3::Expr(VC->listExpr(VC->idExpr("_WHERE")));
               		}
    break;

  case 63:
#line 602 "PL.y"
    {
                          (yyval.node) = new CVC3::Expr(VC->listExpr(VC->idExpr("_ASSERTIONS")));
               		}
    break;

  case 64:
#line 605 "PL.y"
    {
                          (yyval.node) = new CVC3::Expr(VC->listExpr(VC->idExpr("_ASSUMPTIONS")));
               		}
    break;

  case 65:
#line 608 "PL.y"
    {
                          (yyval.node) = new CVC3::Expr(VC->listExpr(VC->idExpr("_COUNTEREXAMPLE")));
               		}
    break;

  case 66:
#line 611 "PL.y"
    {
                          (yyval.node) = new CVC3::Expr(VC->listExpr(VC->idExpr("_COUNTERMODEL")));
               		}
    break;

  case 67:
#line 615 "PL.y"
    { 
                          (yyval.node) = new CVC3::Expr(VC->listExpr("_PUSH", *(yyvsp[(2) - (2)].node)));
			  delete (yyvsp[(2) - (2)].node);
                        }
    break;

  case 68:
#line 619 "PL.y"
    {
                          (yyval.node) = new CVC3::Expr(VC->listExpr(VC->idExpr("_PUSH")));
		        }
    break;

  case 69:
#line 622 "PL.y"
    { 
                          (yyval.node) = new CVC3::Expr(VC->listExpr("_PUSH_SCOPE", *(yyvsp[(2) - (2)].node)));
			  delete (yyvsp[(2) - (2)].node);
                        }
    break;

  case 70:
#line 626 "PL.y"
    {
                          (yyval.node) = new CVC3::Expr(VC->listExpr(VC->idExpr("_PUSH_SCOPE")));
		        }
    break;

  case 71:
#line 630 "PL.y"
    { 
                          (yyval.node) = new CVC3::Expr(VC->listExpr("_POP", *(yyvsp[(2) - (2)].node)));
			  delete (yyvsp[(2) - (2)].node);
                        }
    break;

  case 72:
#line 634 "PL.y"
    {
                          (yyval.node) = new CVC3::Expr(VC->listExpr(VC->idExpr("_POP")));
		        }
    break;

  case 73:
#line 637 "PL.y"
    { 
                          (yyval.node) = new CVC3::Expr(VC->listExpr("_POP_SCOPE", *(yyvsp[(2) - (2)].node)));
			  delete (yyvsp[(2) - (2)].node);
                        }
    break;

  case 74:
#line 641 "PL.y"
    {
                          (yyval.node) = new CVC3::Expr(VC->listExpr(VC->idExpr("_POP_SCOPE")));
		        }
    break;

  case 75:
#line 645 "PL.y"
    { 
                          (yyval.node) = new CVC3::Expr(VC->listExpr("_POPTO", *(yyvsp[(2) - (2)].node)));
			  delete (yyvsp[(2) - (2)].node);
                        }
    break;

  case 76:
#line 649 "PL.y"
    {
                          (yyval.node) = new CVC3::Expr(VC->listExpr(VC->idExpr("_POPTO")));
		        }
    break;

  case 77:
#line 652 "PL.y"
    {
                          (yyval.node) = new CVC3::Expr(VC->listExpr("_POPTO_SCOPE", *(yyvsp[(2) - (2)].node)));
			  delete (yyvsp[(2) - (2)].node);
                        }
    break;

  case 78:
#line 656 "PL.y"
    {
                          (yyval.node) = new CVC3::Expr(VC->listExpr(VC->idExpr("_POPTO_SCOPE")));
		        }
    break;

  case 79:
#line 659 "PL.y"
    {
                          (yyval.node) = new CVC3::Expr(VC->listExpr(VC->idExpr("_RESET")));
		        }
    break;

  case 80:
#line 663 "PL.y"
    { 
                          (yyval.node) = new CVC3::Expr(VC->listExpr("_CONTEXT",  *(yyvsp[(2) - (2)].node)));
			  delete (yyvsp[(2) - (2)].node);
                        }
    break;

  case 81:
#line 667 "PL.y"
    {
                          (yyval.node) = new CVC3::Expr(VC->listExpr(VC->idExpr("_CONTEXT")));
		        }
    break;

  case 82:
#line 671 "PL.y"
    { 
                          (yyval.node) = new CVC3::Expr(VC->listExpr("_FORGET", *(yyvsp[(2) - (2)].node)));
			  delete (yyvsp[(2) - (2)].node);
                        }
    break;

  case 83:
#line 676 "PL.y"
    { 
                          (yyval.node) = new CVC3::Expr(VC->listExpr("_GET_TYPE", *(yyvsp[(2) - (2)].node)));
			  delete (yyvsp[(2) - (2)].node);
                        }
    break;

  case 84:
#line 681 "PL.y"
    { 
                          (yyval.node) = new CVC3::Expr(VC->listExpr("_CHECK_TYPE",*(yyvsp[(2) - (4)].node), *(yyvsp[(4) - (4)].node)));
			  delete (yyvsp[(2) - (4)].node);
			  delete (yyvsp[(4) - (4)].node);
                        }
    break;

  case 85:
#line 687 "PL.y"
    { 
                          (yyval.node) = new CVC3::Expr(VC->listExpr("_GET_CHILD", *(yyvsp[(2) - (3)].node), *(yyvsp[(3) - (3)].node)));
			  delete (yyvsp[(2) - (3)].node);
			  delete (yyvsp[(3) - (3)].node);
                        }
    break;

  case 86:
#line 693 "PL.y"
    { 
                          (yyval.node) = new CVC3::Expr(VC->listExpr("_GET_CHILD", *(yyvsp[(2) - (2)].node)));
			  delete (yyvsp[(2) - (2)].node);
                        }
    break;

  case 87:
#line 698 "PL.y"
    { 
                          std::vector<CVC3::Expr> tmp;
			  tmp.push_back(*(yyvsp[(2) - (11)].node));
			  tmp.push_back(*(yyvsp[(4) - (11)].node));
			  tmp.push_back(*(yyvsp[(6) - (11)].node));
			  tmp.push_back(*(yyvsp[(8) - (11)].node));
			  tmp.push_back(*(yyvsp[(10) - (11)].node));
                          (yyval.node) = new CVC3::Expr(VC->listExpr("_SUBSTITUTE", tmp));
			  delete (yyvsp[(2) - (11)].node);
			  delete (yyvsp[(4) - (11)].node);
			  delete (yyvsp[(6) - (11)].node);
			  delete (yyvsp[(8) - (11)].node);
			  delete (yyvsp[(10) - (11)].node);
                        }
    break;

  case 88:
#line 714 "PL.y"
    {
			  (yyval.node) = new CVC3::Expr(VC->idExpr(*(yyvsp[(1) - (1)].str)));
			  delete (yyvsp[(1) - (1)].str);
			}
    break;

  case 89:
#line 720 "PL.y"
    {
			  (yyval.node) = new CVC3::Expr(VC->stringExpr(*(yyvsp[(1) - (1)].str)));
			  delete (yyvsp[(1) - (1)].str);
			}
    break;

  case 90:
#line 726 "PL.y"
    {
  			  (yyval.node) = new CVC3::Expr(VC->ratExpr((*(yyvsp[(1) - (1)].str))));
  			  delete (yyvsp[(1) - (1)].str);
			}
    break;

  case 91:
#line 733 "PL.y"
    {
			  (yyval.node) = new CVC3::Expr
			    (VC->listExpr("_BVCONST", VC->stringExpr(*(yyvsp[(1) - (1)].str))));
			  delete (yyvsp[(1) - (1)].str);
                        }
    break;

  case 92:
#line 742 "PL.y"
    {
			  (yyval.node) = new CVC3::Expr
			    (VC->listExpr("_BVCONST", VC->stringExpr(*(yyvsp[(1) - (1)].str)), VC->ratExpr(16)));
			  delete (yyvsp[(1) - (1)].str);
                        }
    break;

  case 93:
#line 752 "PL.y"
    { (yyval.node) = (yyvsp[(1) - (1)].node); }
    break;

  case 94:
#line 753 "PL.y"
    { (yyval.node) = (yyvsp[(1) - (1)].node); }
    break;

  case 95:
#line 756 "PL.y"
    { (yyval.node) = (yyvsp[(1) - (1)].node); }
    break;

  case 96:
#line 757 "PL.y"
    { (yyval.node) = (yyvsp[(1) - (1)].node); }
    break;

  case 97:
#line 758 "PL.y"
    { (yyval.node) = (yyvsp[(1) - (1)].node); }
    break;

  case 98:
#line 759 "PL.y"
    { (yyval.node) = (yyvsp[(1) - (1)].node); }
    break;

  case 99:
#line 760 "PL.y"
    { (yyval.node) = (yyvsp[(1) - (1)].node); }
    break;

  case 100:
#line 761 "PL.y"
    { (yyval.node) = (yyvsp[(1) - (1)].node); }
    break;

  case 101:
#line 762 "PL.y"
    { (yyval.node) = (yyvsp[(1) - (1)].node); }
    break;

  case 102:
#line 763 "PL.y"
    {(yyval.node) = (yyvsp[(1) - (1)].node);}
    break;

  case 103:
#line 764 "PL.y"
    { (yyval.node) = (yyvsp[(1) - (1)].node); }
    break;

  case 104:
#line 765 "PL.y"
    { (yyval.node) = (yyvsp[(2) - (3)].node); }
    break;

  case 105:
#line 768 "PL.y"
    { (yyval.node) = (yyvsp[(1) - (1)].node); }
    break;

  case 106:
#line 769 "PL.y"
    { (yyval.node) = (yyvsp[(1) - (1)].node); }
    break;

  case 107:
#line 773 "PL.y"
    {
			  (yyval.node) = new CVC3::Expr(
                            VC->listExpr("_TYPEDEF",
                                         VC->listExpr("_DATATYPE", *(yyvsp[(2) - (3)].vec))));
			  delete (yyvsp[(2) - (3)].vec);
			}
    break;

  case 108:
#line 782 "PL.y"
    {
			  (yyval.vec) = new std::vector<CVC3::Expr>;
			  (yyval.vec)->push_back(*(yyvsp[(1) - (1)].node));
			  delete (yyvsp[(1) - (1)].node);
			}
    break;

  case 109:
#line 788 "PL.y"
    { 
			  (yyvsp[(1) - (3)].vec)->push_back(*(yyvsp[(3) - (3)].node)); 
                          (yyval.vec) = (yyvsp[(1) - (3)].vec);
		          delete (yyvsp[(3) - (3)].node);
			}
    break;

  case 110:
#line 796 "PL.y"
    {
			  (yyval.node) = new CVC3::Expr(VC->listExpr(*(yyvsp[(1) - (3)].node), VC->listExpr(*(yyvsp[(3) - (3)].vec))));
			  delete (yyvsp[(1) - (3)].node);
			  delete (yyvsp[(3) - (3)].vec);
                        }
    break;

  case 111:
#line 804 "PL.y"
    {
			  (yyval.vec) = new std::vector<CVC3::Expr>;
			  (yyval.vec)->push_back(*(yyvsp[(1) - (1)].node));
			  delete (yyvsp[(1) - (1)].node); 
			}
    break;

  case 112:
#line 810 "PL.y"
    { 
			  (yyvsp[(1) - (3)].vec)->push_back(*(yyvsp[(3) - (3)].node)); 
                          (yyval.vec) = (yyvsp[(1) - (3)].vec); 
		          delete (yyvsp[(3) - (3)].node); 
			}
    break;

  case 113:
#line 818 "PL.y"
    {
                          (yyval.node) = new CVC3::Expr(VC->listExpr(*(yyvsp[(1) - (1)].node)));
			  delete (yyvsp[(1) - (1)].node); 
			}
    break;

  case 114:
#line 823 "PL.y"
    {
                          CVC3::Expr tmp = VC->listExpr(*(yyvsp[(3) - (4)].vec));
			  (yyval.node) = new CVC3::Expr(VC->listExpr(*(yyvsp[(1) - (4)].node), tmp));
			  delete (yyvsp[(1) - (4)].node); delete (yyvsp[(3) - (4)].vec);
			}
    break;

  case 115:
#line 831 "PL.y"
    {
			  (yyval.vec) = new std::vector<CVC3::Expr>;
			  (yyval.vec)->push_back(*(yyvsp[(1) - (1)].node));
			  delete (yyvsp[(1) - (1)].node);
			}
    break;

  case 116:
#line 837 "PL.y"
    {
			  (yyvsp[(1) - (3)].vec)->push_back(*(yyvsp[(3) - (3)].node));
			  (yyval.vec) = (yyvsp[(1) - (3)].vec); 
			  delete (yyvsp[(3) - (3)].node);
			}
    break;

  case 117:
#line 845 "PL.y"
    { 
			  (yyval.node) = new CVC3::Expr(VC->listExpr(*(yyvsp[(1) - (3)].node), *(yyvsp[(3) - (3)].node)));
			  delete (yyvsp[(1) - (3)].node);
			  delete (yyvsp[(3) - (3)].node);
			}
    break;

  case 118:
#line 853 "PL.y"
    {
                          // Old style functions
                          (yyval.node) = new CVC3::Expr(VC->listExpr("_OLD_ARROW", *(yyvsp[(2) - (5)].node), *(yyvsp[(4) - (5)].node)));
                          delete (yyvsp[(2) - (5)].node); delete (yyvsp[(4) - (5)].node);
			}
    break;

  case 119:
#line 859 "PL.y"
    {
			  std::vector<CVC3::Expr> temp;
			  temp.push_back(*(yyvsp[(1) - (3)].node));
			  temp.push_back(*(yyvsp[(3) - (3)].node));

			  (yyval.node) = new CVC3::Expr(VC->listExpr("_ARROW", temp));
			  delete (yyvsp[(1) - (3)].node); delete (yyvsp[(3) - (3)].node); 
			}
    break;

  case 120:
#line 868 "PL.y"
    {
			  (yyvsp[(2) - (5)].vec)->push_back(*(yyvsp[(5) - (5)].node));
			  (yyval.node) = new CVC3::Expr(VC->listExpr("_ARROW", *(yyvsp[(2) - (5)].vec)));
			  delete (yyvsp[(2) - (5)].vec); delete (yyvsp[(5) - (5)].node); 
			}
    break;

  case 121:
#line 876 "PL.y"
    {
			  (yyval.node) = new CVC3::Expr(VC->listExpr(*(yyvsp[(2) - (3)].vec)));
			  delete (yyvsp[(2) - (3)].vec);
			}
    break;

  case 122:
#line 883 "PL.y"
    { 
			  (yyval.vec) = new std::vector<CVC3::Expr>;
			  (yyval.vec)->push_back(VC->idExpr("_RECORD_TYPE"));
			  (yyval.vec)->push_back(*(yyvsp[(1) - (1)].node)); 
			  delete (yyvsp[(1) - (1)].node); 
                        }
    break;

  case 123:
#line 890 "PL.y"
    { 
			  (yyvsp[(1) - (3)].vec)->push_back(*(yyvsp[(3) - (3)].node)); 
			  (yyval.vec) = (yyvsp[(1) - (3)].vec); 
			  delete (yyvsp[(3) - (3)].node);
			}
    break;

  case 124:
#line 898 "PL.y"
    {
			  (yyval.node) = new CVC3::Expr(VC->listExpr(*(yyvsp[(1) - (3)].node), *(yyvsp[(3) - (3)].node)));
			  delete (yyvsp[(1) - (3)].node);
			  delete (yyvsp[(3) - (3)].node);
			}
    break;

  case 125:
#line 906 "PL.y"
    {
			   (yyval.node) = new CVC3::Expr(VC->listExpr("_TUPLE_TYPE", *(yyvsp[(2) - (3)].vec)));
			   delete (yyvsp[(2) - (3)].vec);
			 }
    break;

  case 126:
#line 913 "PL.y"
    {
			  (yyval.vec) = new std::vector<CVC3::Expr>;
			  (yyval.vec)->push_back(*(yyvsp[(1) - (3)].node));
                          (yyval.vec)->push_back(*(yyvsp[(3) - (3)].node));
			  delete (yyvsp[(1) - (3)].node);
                          delete (yyvsp[(3) - (3)].node);
			}
    break;

  case 127:
#line 921 "PL.y"
    {
			  (yyvsp[(1) - (3)].vec)->push_back(*(yyvsp[(3) - (3)].node));
			  (yyval.vec) = (yyvsp[(1) - (3)].vec); 
			  delete (yyvsp[(3) - (3)].node);
			}
    break;

  case 128:
#line 937 "PL.y"
    {
			  (yyval.node) = new CVC3::Expr(VC->listExpr("_ARRAY", *(yyvsp[(2) - (4)].node), *(yyvsp[(4) - (4)].node)));
			  delete (yyvsp[(2) - (4)].node);
			  delete (yyvsp[(4) - (4)].node);
			}
    break;

  case 129:
#line 945 "PL.y"
    {
			   std::vector<CVC3::Expr>::iterator theIter = (yyvsp[(2) - (3)].vec)->begin();
			   (yyvsp[(2) - (3)].vec)->insert(theIter, VC->idExpr("_SCALARTYPE"));
			   (yyval.node) = new CVC3::Expr(VC->listExpr(*(yyvsp[(2) - (3)].vec)));
			   delete (yyvsp[(2) - (3)].vec);
			 }
    break;

  case 130:
#line 954 "PL.y"
    {
			  (yyval.node) = new CVC3::Expr(VC->listExpr("_SUBTYPE", *(yyvsp[(3) - (4)].node)));
			  delete (yyvsp[(3) - (4)].node);
			}
    break;

  case 131:
#line 959 "PL.y"
    {
                          (yyval.node) = new CVC3::Expr(VC->listExpr("_SUBTYPE", *(yyvsp[(3) - (6)].node), *(yyvsp[(5) - (6)].node)));
                          delete (yyvsp[(3) - (6)].node);
                          delete (yyvsp[(5) - (6)].node);
                        }
    break;

  case 132:
#line 967 "PL.y"
    {
			  (yyval.node) = new CVC3::Expr(VC->idExpr("_BOOLEAN"));
			}
    break;

  case 135:
#line 975 "PL.y"
    {
			  (yyval.node) = new CVC3::Expr(VC->listExpr("_BITVECTOR", *(yyvsp[(3) - (4)].node)));
			  delete (yyvsp[(3) - (4)].node);
			}
    break;

  case 136:
#line 982 "PL.y"
    {
			  (yyval.node) = new CVC3::Expr(VC->idExpr("_REAL"));
			}
    break;

  case 137:
#line 988 "PL.y"
    {
			  (yyval.node) = new CVC3::Expr(VC->idExpr("_INT"));
                        }
    break;

  case 138:
#line 993 "PL.y"
    {
			  (yyval.node) = new CVC3::Expr(VC->listExpr("_SUBRANGE", *(yyvsp[(2) - (5)].node), *(yyvsp[(4) - (5)].node)));
			  delete (yyvsp[(2) - (5)].node);
			  delete (yyvsp[(4) - (5)].node);
			}
    break;

  case 139:
#line 1001 "PL.y"
    {
			  (yyval.node) = new CVC3::Expr(VC->listExpr(VC->idExpr("_NEGINF")));
			}
    break;

  case 140:
#line 1004 "PL.y"
    { (yyval.node) = (yyvsp[(1) - (1)].node); }
    break;

  case 141:
#line 1005 "PL.y"
    {
                          CVC3::Rational value= -(yyvsp[(2) - (2)].node)->getRational();
			  (yyval.node) = new CVC3::Expr(VC->ratExpr(value.toString()));
			  delete (yyvsp[(2) - (2)].node);
                        }
    break;

  case 142:
#line 1013 "PL.y"
    {
			  (yyval.node) = new CVC3::Expr(VC->listExpr(VC->idExpr("_POSINF")));
			}
    break;

  case 143:
#line 1016 "PL.y"
    { (yyval.node) = (yyvsp[(1) - (1)].node); }
    break;

  case 144:
#line 1017 "PL.y"
    {
                          CVC3::Rational value= -(yyvsp[(2) - (2)].node)->getRational();
			  (yyval.node) = new CVC3::Expr(VC->ratExpr(value.toString()));
			  delete (yyvsp[(2) - (2)].node);
                        }
    break;

  case 145:
#line 1026 "PL.y"
    { 
			  (yyval.vec) = new std::vector<CVC3::Expr>;
			  (yyval.vec)->push_back(*(yyvsp[(1) - (1)].node));
			  delete (yyvsp[(1) - (1)].node);
			}
    break;

  case 146:
#line 1032 "PL.y"
    {
			  (yyvsp[(3) - (3)].vec)->push_back(*(yyvsp[(1) - (3)].node));
			  (yyval.vec) = (yyvsp[(3) - (3)].vec); 
			  delete (yyvsp[(1) - (3)].node);
			}
    break;

  case 147:
#line 1040 "PL.y"
    {
			  (yyval.vec) = new std::vector<CVC3::Expr>((yyvsp[(1) - (1)].vec)->rbegin(),
							   (yyvsp[(1) - (1)].vec)->rend());
			  delete (yyvsp[(1) - (1)].vec);
			}
    break;

  case 148:
#line 1049 "PL.y"
    { (yyval.node) = (yyvsp[(1) - (1)].node); }
    break;

  case 149:
#line 1050 "PL.y"
    { (yyval.node) = (yyvsp[(1) - (1)].node); }
    break;

  case 150:
#line 1051 "PL.y"
    { (yyval.node) = (yyvsp[(1) - (1)].node); }
    break;

  case 151:
#line 1052 "PL.y"
    { (yyval.node) = (yyvsp[(1) - (1)].node); }
    break;

  case 152:
#line 1054 "PL.y"
    {
			  std::vector<CVC3::Expr> tmp;
			  tmp.push_back(*(yyvsp[(1) - (4)].node));
			  tmp.insert(tmp.end(), (yyvsp[(3) - (4)].vec)->begin(), (yyvsp[(3) - (4)].vec)->end());
			  (yyval.node) = new CVC3::Expr(VC->listExpr(tmp));
			  delete (yyvsp[(1) - (4)].node);
			  delete (yyvsp[(3) - (4)].vec);
			}
    break;

  case 153:
#line 1063 "PL.y"
    {
			  (yyval.node) = new CVC3::Expr(VC->listExpr("_SIMULATE", *(yyvsp[(3) - (4)].vec)));
			  delete (yyvsp[(3) - (4)].vec);
			}
    break;

  case 154:
#line 1068 "PL.y"
    {
			  (yyval.node) = new CVC3::Expr(VC->listExpr("_READ", *(yyvsp[(1) - (4)].node), *(yyvsp[(3) - (4)].node)));
			  delete (yyvsp[(1) - (4)].node);
			  delete (yyvsp[(3) - (4)].node);
			}
    break;

  case 155:
#line 1074 "PL.y"
    {
			  (yyval.node) = new CVC3::Expr(VC->listExpr("_RECORD_SELECT", *(yyvsp[(1) - (3)].node), *(yyvsp[(3) - (3)].node)));
			  delete (yyvsp[(1) - (3)].node);
			  delete (yyvsp[(3) - (3)].node);
			}
    break;

  case 156:
#line 1080 "PL.y"
    {
			  (yyval.node) = new CVC3::Expr(VC->listExpr("_TUPLE_SELECT", *(yyvsp[(1) - (3)].node), *(yyvsp[(3) - (3)].node)));
			  delete (yyvsp[(1) - (3)].node);
			  delete (yyvsp[(3) - (3)].node);
			}
    break;

  case 157:
#line 1086 "PL.y"
    {
			  (yyval.node) = new CVC3::Expr(CVC3::PLprocessUpdates(*(yyvsp[(1) - (3)].node), *(yyvsp[(3) - (3)].vec)));
			  delete (yyvsp[(1) - (3)].node);
			  delete (yyvsp[(3) - (3)].vec);
			}
    break;

  case 158:
#line 1091 "PL.y"
    { (yyval.node) = (yyvsp[(1) - (1)].node); }
    break;

  case 159:
#line 1092 "PL.y"
    { (yyval.node) = (yyvsp[(1) - (1)].node); }
    break;

  case 160:
#line 1093 "PL.y"
    { (yyval.node) = (yyvsp[(1) - (1)].node); }
    break;

  case 161:
#line 1095 "PL.y"
    { (yyval.node) = (yyvsp[(1) - (1)].node); }
    break;

  case 162:
#line 1097 "PL.y"
    { (yyval.node) = (yyvsp[(1) - (1)].node); }
    break;

  case 163:
#line 1098 "PL.y"
    { (yyval.node) = (yyvsp[(1) - (1)].node); }
    break;

  case 164:
#line 1099 "PL.y"
    { (yyval.node) = (yyvsp[(1) - (1)].node); }
    break;

  case 165:
#line 1102 "PL.y"
    {
			  (yyval.node) = new CVC3::Expr(VC->idExpr("_TRUE_EXPR"));
			}
    break;

  case 166:
#line 1106 "PL.y"
    {
			  (yyval.node) = new CVC3::Expr(VC->idExpr("_FALSE_EXPR"));
			}
    break;

  case 167:
#line 1111 "PL.y"
    {
			  if ((yyvsp[(2) - (2)].node)->isRational())
			  {
			    CVC3::Rational value= -(yyvsp[(2) - (2)].node)->getRational();
			    (yyval.node)= new CVC3::Expr(VC->ratExpr(value.toString()));
			  }
			  else
			    (yyval.node) = new CVC3::Expr(VC->listExpr("_UMINUS", *(yyvsp[(2) - (2)].node)));
			  delete (yyvsp[(2) - (2)].node);
			}
    break;

  case 168:
#line 1122 "PL.y"
    {
			  (yyval.node) = new CVC3::Expr(VC->listExpr("_NOT", *(yyvsp[(2) - (2)].node)));
			  delete (yyvsp[(2) - (2)].node);
			}
    break;

  case 169:
#line 1127 "PL.y"
    {
			  (yyval.node) = new CVC3::Expr(VC->listExpr("_IS_INTEGER", *(yyvsp[(2) - (2)].node)));
			  delete (yyvsp[(2) - (2)].node);
			}
    break;

  case 170:
#line 1132 "PL.y"
    {
			  (yyval.node) = new CVC3::Expr(VC->listExpr("_TCC", *(yyvsp[(3) - (4)].node)));
			  delete (yyvsp[(3) - (4)].node);
			}
    break;

  case 171:
#line 1137 "PL.y"
    {
			  (yyval.node) = new CVC3::Expr(VC->listExpr("_EQ", *(yyvsp[(1) - (3)].node), *(yyvsp[(3) - (3)].node)));
			  delete (yyvsp[(1) - (3)].node);
			  delete (yyvsp[(3) - (3)].node);
			}
    break;

  case 172:
#line 1143 "PL.y"
    {
			  (yyval.node) = new CVC3::Expr(VC->listExpr("_NEQ", *(yyvsp[(1) - (3)].node), *(yyvsp[(3) - (3)].node)));
			  delete (yyvsp[(1) - (3)].node);
			  delete (yyvsp[(3) - (3)].node);
			}
    break;

  case 173:
#line 1149 "PL.y"
    {
			  (yyval.node) = new CVC3::Expr(VC->listExpr("_XOR", *(yyvsp[(1) - (3)].node), *(yyvsp[(3) - (3)].node)));
			  delete (yyvsp[(1) - (3)].node);
			  delete (yyvsp[(3) - (3)].node);
			}
    break;

  case 174:
#line 1155 "PL.y"
    {
			  (yyval.node) = new CVC3::Expr(VC->listExpr("_OR", *(yyvsp[(1) - (1)].vec)));
			  delete (yyvsp[(1) - (1)].vec);
			}
    break;

  case 175:
#line 1160 "PL.y"
    {
			  (yyval.node) = new CVC3::Expr(VC->listExpr("_AND", *(yyvsp[(1) - (1)].vec)));
			  delete (yyvsp[(1) - (1)].vec);
			}
    break;

  case 176:
#line 1165 "PL.y"
    {
			  (yyval.node) = new CVC3::Expr(VC->listExpr("_IMPLIES", *(yyvsp[(1) - (3)].node), *(yyvsp[(3) - (3)].node)));
			  delete (yyvsp[(1) - (3)].node);
			  delete (yyvsp[(3) - (3)].node);
			}
    break;

  case 177:
#line 1171 "PL.y"
    {
			  (yyval.node) = new CVC3::Expr(VC->listExpr("_IFF", *(yyvsp[(1) - (3)].node), *(yyvsp[(3) - (3)].node)));
			  delete (yyvsp[(1) - (3)].node);
			  delete (yyvsp[(3) - (3)].node);
			}
    break;

  case 178:
#line 1177 "PL.y"
    {
			  (yyval.node) = new CVC3::Expr(VC->listExpr("_PLUS", *(yyvsp[(1) - (3)].node), *(yyvsp[(3) - (3)].node)));
			  delete (yyvsp[(1) - (3)].node);
			  delete (yyvsp[(3) - (3)].node);
			}
    break;

  case 179:
#line 1183 "PL.y"
    {
			  (yyval.node) = new CVC3::Expr(VC->listExpr("_MINUS", *(yyvsp[(1) - (3)].node), *(yyvsp[(3) - (3)].node)));
			  delete (yyvsp[(1) - (3)].node);
			  delete (yyvsp[(3) - (3)].node);
			}
    break;

  case 180:
#line 1189 "PL.y"
    {
                          (yyval.node) = new CVC3::Expr(VC->listExpr("_TRANS_CLOSURE",
							   *(yyvsp[(1) - (7)].node), *(yyvsp[(4) - (7)].node), *(yyvsp[(6) - (7)].node)));
			  delete (yyvsp[(1) - (7)].node);
			  delete (yyvsp[(4) - (7)].node);
			  delete (yyvsp[(6) - (7)].node);
			}
    break;

  case 181:
#line 1197 "PL.y"
    {
			  (yyval.node) = new CVC3::Expr(VC->listExpr("_MULT", *(yyvsp[(1) - (3)].node), *(yyvsp[(3) - (3)].node)));
			  delete (yyvsp[(1) - (3)].node);
			  delete (yyvsp[(3) - (3)].node);
			}
    break;

  case 182:
#line 1203 "PL.y"
    {
			  (yyval.node) = new CVC3::Expr(VC->listExpr("_POW", *(yyvsp[(3) - (3)].node), *(yyvsp[(1) - (3)].node)));
			  delete (yyvsp[(1) - (3)].node);
			  delete (yyvsp[(3) - (3)].node);
			}
    break;

  case 183:
#line 1209 "PL.y"
    {
			  (yyval.node) = new CVC3::Expr(VC->listExpr("_DIVIDE", *(yyvsp[(1) - (3)].node), *(yyvsp[(3) - (3)].node)));
			  delete (yyvsp[(1) - (3)].node);
			  delete (yyvsp[(3) - (3)].node);
			}
    break;

  case 184:
#line 1227 "PL.y"
    {
			  (yyval.node) = new CVC3::Expr(VC->listExpr("_GT", *(yyvsp[(1) - (3)].node), *(yyvsp[(3) - (3)].node)));
			  delete (yyvsp[(1) - (3)].node);
			  delete (yyvsp[(3) - (3)].node);
			}
    break;

  case 185:
#line 1233 "PL.y"
    {
			  (yyval.node) = new CVC3::Expr(VC->listExpr("_GE", *(yyvsp[(1) - (3)].node), *(yyvsp[(3) - (3)].node)));
			  delete (yyvsp[(1) - (3)].node);
			  delete (yyvsp[(3) - (3)].node);
			}
    break;

  case 186:
#line 1239 "PL.y"
    {
			  (yyval.node) = new CVC3::Expr(VC->listExpr("_FLOOR", *(yyvsp[(3) - (4)].node)));
			  delete (yyvsp[(3) - (4)].node);
			}
    break;

  case 187:
#line 1244 "PL.y"
    {
			  (yyval.node) = new CVC3::Expr(VC->listExpr("_LT", *(yyvsp[(1) - (3)].node), *(yyvsp[(3) - (3)].node)));
			  delete (yyvsp[(1) - (3)].node);
			  delete (yyvsp[(3) - (3)].node);
			}
    break;

  case 188:
#line 1250 "PL.y"
    {
			  (yyval.node) = new CVC3::Expr(VC->listExpr("_LE", *(yyvsp[(1) - (3)].node), *(yyvsp[(3) - (3)].node)));
			  delete (yyvsp[(1) - (3)].node);
			  delete (yyvsp[(3) - (3)].node);
			}
    break;

  case 189:
#line 1256 "PL.y"
    {
			   (yyval.node) = (yyvsp[(2) - (3)].node);
			 }
    break;

  case 190:
#line 1260 "PL.y"
    {
			  (yyval.node) = new CVC3::Expr(VC->listExpr("_BVNEG", *(yyvsp[(2) - (2)].node)));
			  delete (yyvsp[(2) - (2)].node);
			}
    break;

  case 191:
#line 1265 "PL.y"
    {
			  (yyval.node) = new CVC3::Expr
			    (VC->listExpr("_EXTRACT", VC->ratExpr(*(yyvsp[(3) - (6)].str)),
                                          VC->ratExpr(*(yyvsp[(5) - (6)].str)), *(yyvsp[(1) - (6)].node)));
			  delete (yyvsp[(1) - (6)].node);
			  delete (yyvsp[(3) - (6)].str);
  			  delete (yyvsp[(5) - (6)].str);
			}
    break;

  case 192:
#line 1274 "PL.y"
    {
			  (yyval.node) = new CVC3::Expr(VC->listExpr("_BVAND", *(yyvsp[(1) - (3)].node), *(yyvsp[(3) - (3)].node)));
			  delete (yyvsp[(1) - (3)].node);
			  delete (yyvsp[(3) - (3)].node);
			}
    break;

  case 193:
#line 1280 "PL.y"
    {
			  (yyval.node) = new CVC3::Expr(VC->listExpr("_BVOR", *(yyvsp[(1) - (3)].node), *(yyvsp[(3) - (3)].node))); 
			  delete (yyvsp[(1) - (3)].node);
			  delete (yyvsp[(3) - (3)].node);
			}
    break;

  case 194:
#line 1286 "PL.y"
    {
			  (yyval.node) = new CVC3::Expr
			    (VC->listExpr("_LEFTSHIFT", *(yyvsp[(1) - (3)].node), VC->ratExpr(*(yyvsp[(3) - (3)].str))));
			  delete (yyvsp[(1) - (3)].node);
			  delete (yyvsp[(3) - (3)].str);
                        }
    break;

  case 195:
#line 1293 "PL.y"
    {
			  (yyval.node) = new CVC3::Expr
			    (VC->listExpr("_RIGHTSHIFT", *(yyvsp[(1) - (3)].node), VC->ratExpr(*(yyvsp[(3) - (3)].str))));
			  delete (yyvsp[(1) - (3)].node);
			  delete (yyvsp[(3) - (3)].str);
                        }
    break;

  case 196:
#line 1300 "PL.y"
    {
			  (yyval.node) = new CVC3::Expr(VC->listExpr("_BVXOR", *(yyvsp[(3) - (6)].node), *(yyvsp[(5) - (6)].node)));
			  delete (yyvsp[(3) - (6)].node);
			  delete (yyvsp[(5) - (6)].node);
			}
    break;

  case 197:
#line 1306 "PL.y"
    {
			  (yyval.node) = new CVC3::Expr(VC->listExpr("_BVNAND", *(yyvsp[(3) - (6)].node), *(yyvsp[(5) - (6)].node)));
			  delete (yyvsp[(3) - (6)].node);
			  delete (yyvsp[(5) - (6)].node);
			}
    break;

  case 198:
#line 1312 "PL.y"
    {
			  (yyval.node) = new CVC3::Expr(VC->listExpr("_BVNOR", *(yyvsp[(3) - (6)].node), *(yyvsp[(5) - (6)].node)));
			  delete (yyvsp[(3) - (6)].node);
			  delete (yyvsp[(5) - (6)].node);
			}
    break;

  case 199:
#line 1318 "PL.y"
    {
			  (yyval.node) = new CVC3::Expr(VC->listExpr("_BVCOMP", *(yyvsp[(3) - (6)].node), *(yyvsp[(5) - (6)].node)));
			  delete (yyvsp[(3) - (6)].node);
			  delete (yyvsp[(5) - (6)].node);
			}
    break;

  case 200:
#line 1324 "PL.y"
    {
			  (yyval.node) = new CVC3::Expr(VC->listExpr("_BVXNOR", *(yyvsp[(3) - (6)].node), *(yyvsp[(5) - (6)].node)));
			  delete (yyvsp[(3) - (6)].node);
			  delete (yyvsp[(5) - (6)].node);
			}
    break;

  case 201:
#line 1330 "PL.y"
    {
			  (yyval.node) = new CVC3::Expr(VC->listExpr("_SX",*(yyvsp[(3) - (6)].node),VC->ratExpr(*(yyvsp[(5) - (6)].str))));
			  delete (yyvsp[(3) - (6)].node);
  			  delete (yyvsp[(5) - (6)].str);
		        }
    break;

  case 202:
#line 1336 "PL.y"
    {
                          (yyval.node) = new CVC3::Expr(VC->listExpr("_BVZEROEXTEND",VC->ratExpr(*(yyvsp[(5) - (6)].str)),*(yyvsp[(3) - (6)].node)));
			  delete (yyvsp[(3) - (6)].node);
  			  delete (yyvsp[(5) - (6)].str);
                        }
    break;

  case 203:
#line 1342 "PL.y"
    {
                          (yyval.node) = new CVC3::Expr(VC->listExpr("_BVREPEAT",VC->ratExpr(*(yyvsp[(5) - (6)].str)),*(yyvsp[(3) - (6)].node)));
			  delete (yyvsp[(3) - (6)].node);
  			  delete (yyvsp[(5) - (6)].str);
                        }
    break;

  case 204:
#line 1348 "PL.y"
    {
                          (yyval.node) = new CVC3::Expr(VC->listExpr("_BVROTL",VC->ratExpr(*(yyvsp[(5) - (6)].str)),*(yyvsp[(3) - (6)].node)));
			  delete (yyvsp[(3) - (6)].node);
  			  delete (yyvsp[(5) - (6)].str);
                        }
    break;

  case 205:
#line 1354 "PL.y"
    {
                          (yyval.node) = new CVC3::Expr(VC->listExpr("_BVROTR",VC->ratExpr(*(yyvsp[(5) - (6)].str)),*(yyvsp[(3) - (6)].node)));
			  delete (yyvsp[(3) - (6)].node);
  			  delete (yyvsp[(5) - (6)].str);
                        }
    break;

  case 206:
#line 1360 "PL.y"
    {
			  (yyval.node) = new CVC3::Expr(VC->listExpr("_BVLT", *(yyvsp[(3) - (6)].node), *(yyvsp[(5) - (6)].node)));
			  delete (yyvsp[(3) - (6)].node);
			  delete (yyvsp[(5) - (6)].node);
			}
    break;

  case 207:
#line 1366 "PL.y"
    {
			  (yyval.node) = new CVC3::Expr(VC->listExpr("_BVGT", *(yyvsp[(3) - (6)].node), *(yyvsp[(5) - (6)].node)));
			  delete (yyvsp[(3) - (6)].node);
			  delete (yyvsp[(5) - (6)].node);
			}
    break;

  case 208:
#line 1372 "PL.y"
    {
			  (yyval.node) = new CVC3::Expr(VC->listExpr("_BVLE", *(yyvsp[(3) - (6)].node), *(yyvsp[(5) - (6)].node)));
			  delete (yyvsp[(3) - (6)].node);
			  delete (yyvsp[(5) - (6)].node);
			}
    break;

  case 209:
#line 1378 "PL.y"
    {
			  (yyval.node) = new CVC3::Expr(VC->listExpr("_BVGE", *(yyvsp[(3) - (6)].node), *(yyvsp[(5) - (6)].node)));
			  delete (yyvsp[(3) - (6)].node);
			  delete (yyvsp[(5) - (6)].node);
			}
    break;

  case 210:
#line 1385 "PL.y"
    {
			  (yyval.node) = new CVC3::Expr(VC->listExpr("_BVSLT", *(yyvsp[(3) - (6)].node), *(yyvsp[(5) - (6)].node)));
			  delete (yyvsp[(3) - (6)].node);
			  delete (yyvsp[(5) - (6)].node);
			}
    break;

  case 211:
#line 1391 "PL.y"
    {
			  (yyval.node) = new CVC3::Expr(VC->listExpr("_BVSGT", *(yyvsp[(3) - (6)].node), *(yyvsp[(5) - (6)].node)));
			  delete (yyvsp[(3) - (6)].node);
			  delete (yyvsp[(5) - (6)].node);
			}
    break;

  case 212:
#line 1397 "PL.y"
    {
			  (yyval.node) = new CVC3::Expr(VC->listExpr("_BVSLE", *(yyvsp[(3) - (6)].node), *(yyvsp[(5) - (6)].node)));
			  delete (yyvsp[(3) - (6)].node);
			  delete (yyvsp[(5) - (6)].node);
			}
    break;

  case 213:
#line 1403 "PL.y"
    {
			  (yyval.node) = new CVC3::Expr(VC->listExpr("_BVSGE", *(yyvsp[(3) - (6)].node), *(yyvsp[(5) - (6)].node)));
			  delete (yyvsp[(3) - (6)].node);
			  delete (yyvsp[(5) - (6)].node);
			}
    break;

  case 214:
#line 1409 "PL.y"
    {
			  (yyval.node) = new CVC3::Expr(VC->listExpr("_CONCAT", *(yyvsp[(1) - (3)].node), *(yyvsp[(3) - (3)].node)));
			  delete (yyvsp[(1) - (3)].node);
			  delete (yyvsp[(3) - (3)].node);
			}
    break;

  case 215:
#line 1415 "PL.y"
    {
			  (yyval.node) = new CVC3::Expr
			    (VC->listExpr("_INTTOBV", *(yyvsp[(3) - (8)].node), VC->ratExpr(*(yyvsp[(5) - (8)].str)),
					  VC->ratExpr(*(yyvsp[(7) - (8)].str))));
			  delete (yyvsp[(3) - (8)].node);
			  delete (yyvsp[(5) - (8)].str);
			  delete (yyvsp[(7) - (8)].str);
			}
    break;

  case 216:
#line 1424 "PL.y"
    {
			  (yyval.node) = new CVC3::Expr(VC->listExpr("_BVTOINT", *(yyvsp[(3) - (4)].node)));
			  delete (yyvsp[(3) - (4)].node);
                        }
    break;

  case 217:
#line 1429 "PL.y"
    {
			  //FIXME: this function is not to be exposed
			  //to the user counterexamples containing
			  //this function can be translated into
			  //BV-EXTRACT and comparison with 0 or 1
			  (yyval.node) = new CVC3::Expr(VC->listExpr("_BOOLEXTRACT", *(yyvsp[(3) - (6)].node),
                                              VC->ratExpr(*(yyvsp[(5) - (6)].str))));
			  delete (yyvsp[(3) - (6)].node);
  			  delete (yyvsp[(5) - (6)].str);
                        }
    break;

  case 218:
#line 1440 "PL.y"
    {
			  std::vector<CVC3::Expr> k;
			  k.push_back(VC->ratExpr(*(yyvsp[(3) - (6)].str)));
			  k.insert(k.end(), (yyvsp[(5) - (6)].vec)->begin(), (yyvsp[(5) - (6)].vec)->end()); 
			  (yyval.node) = new CVC3::Expr(VC->listExpr("_BVPLUS", k));
			  delete (yyvsp[(3) - (6)].str);
			  delete (yyvsp[(5) - (6)].vec);
                        }
    break;

  case 219:
#line 1449 "PL.y"
    {
			  (yyval.node) =  new CVC3::Expr
                           (VC->listExpr("_BVSUB", VC->ratExpr(*(yyvsp[(3) - (8)].str)), *(yyvsp[(5) - (8)].node), *(yyvsp[(7) - (8)].node)));
			  delete (yyvsp[(3) - (8)].str);
			  delete (yyvsp[(5) - (8)].node);
			  delete (yyvsp[(7) - (8)].node);
                        }
    break;

  case 220:
#line 1457 "PL.y"
    {
			  (yyval.node) =  new CVC3::Expr
                           (VC->listExpr("_BVUDIV", *(yyvsp[(3) - (6)].node), *(yyvsp[(5) - (6)].node)));
			  delete (yyvsp[(3) - (6)].node);
			  delete (yyvsp[(5) - (6)].node);
                        }
    break;

  case 221:
#line 1464 "PL.y"
    {
			  (yyval.node) =  new CVC3::Expr
                           (VC->listExpr("_BVSDIV", *(yyvsp[(3) - (6)].node), *(yyvsp[(5) - (6)].node)));
			  delete (yyvsp[(3) - (6)].node);
			  delete (yyvsp[(5) - (6)].node);
                        }
    break;

  case 222:
#line 1471 "PL.y"
    {
			  (yyval.node) =  new CVC3::Expr
                           (VC->listExpr("_BVUREM", *(yyvsp[(3) - (6)].node), *(yyvsp[(5) - (6)].node)));
			  delete (yyvsp[(3) - (6)].node);
			  delete (yyvsp[(5) - (6)].node);
                        }
    break;

  case 223:
#line 1478 "PL.y"
    {
			  (yyval.node) =  new CVC3::Expr
                           (VC->listExpr("_BVSREM", *(yyvsp[(3) - (6)].node), *(yyvsp[(5) - (6)].node)));
			  delete (yyvsp[(3) - (6)].node);
			  delete (yyvsp[(5) - (6)].node);
                        }
    break;

  case 224:
#line 1485 "PL.y"
    {
			  (yyval.node) =  new CVC3::Expr
                           (VC->listExpr("_BVSMOD", *(yyvsp[(3) - (6)].node), *(yyvsp[(5) - (6)].node)));
			  delete (yyvsp[(3) - (6)].node);
			  delete (yyvsp[(5) - (6)].node);
                        }
    break;

  case 225:
#line 1492 "PL.y"
    {
			  (yyval.node) =  new CVC3::Expr
                           (VC->listExpr("_BVSHL", *(yyvsp[(3) - (6)].node), *(yyvsp[(5) - (6)].node)));
			  delete (yyvsp[(3) - (6)].node);
			  delete (yyvsp[(5) - (6)].node);
                        }
    break;

  case 226:
#line 1499 "PL.y"
    {
			  (yyval.node) =  new CVC3::Expr
                           (VC->listExpr("_BVASHR", *(yyvsp[(3) - (6)].node), *(yyvsp[(5) - (6)].node)));
			  delete (yyvsp[(3) - (6)].node);
			  delete (yyvsp[(5) - (6)].node);
                        }
    break;

  case 227:
#line 1506 "PL.y"
    {
			  (yyval.node) =  new CVC3::Expr
                           (VC->listExpr("_BVLSHR", *(yyvsp[(3) - (6)].node), *(yyvsp[(5) - (6)].node)));
			  delete (yyvsp[(3) - (6)].node);
			  delete (yyvsp[(5) - (6)].node);
                        }
    break;

  case 228:
#line 1513 "PL.y"
    {
			  (yyval.node) =  new CVC3::Expr(VC->listExpr("_BVUMINUS", *(yyvsp[(3) - (4)].node)));
			  delete (yyvsp[(3) - (4)].node);
                        }
    break;

  case 229:
#line 1518 "PL.y"
    {
			  (yyval.node) = new CVC3::Expr
			    (VC->listExpr("_BVMULT", VC->ratExpr(*(yyvsp[(3) - (8)].str)), *(yyvsp[(5) - (8)].node), *(yyvsp[(7) - (8)].node)));
			  delete (yyvsp[(3) - (8)].str);
			  delete (yyvsp[(5) - (8)].node);
			  delete (yyvsp[(7) - (8)].node);
                        }
    break;

  case 230:
#line 1526 "PL.y"
    {
                          (yyval.node) = new CVC3::Expr(VC->listExpr("_DISTINCT", *(yyvsp[(3) - (4)].vec)));
                          delete (yyvsp[(3) - (4)].vec);
                        }
    break;

  case 231:
#line 1532 "PL.y"
    {
			  (yyvsp[(1) - (3)].vec)->push_back(*(yyvsp[(3) - (3)].node));
                          (yyval.vec) = (yyvsp[(1) - (3)].vec);
			  delete (yyvsp[(3) - (3)].node);
			}
    break;

  case 232:
#line 1539 "PL.y"
    {
			  (yyval.vec) = new std::vector<CVC3::Expr>;
			  (yyval.vec)->push_back(*(yyvsp[(1) - (3)].node));
			  (yyval.vec)->push_back(*(yyvsp[(3) - (3)].node));
			  delete (yyvsp[(1) - (3)].node);
			  delete (yyvsp[(3) - (3)].node);
                        }
    break;

  case 233:
#line 1550 "PL.y"
    {
			  (yyvsp[(1) - (3)].vec)->push_back(*(yyvsp[(3) - (3)].node));
                          (yyval.vec) = (yyvsp[(1) - (3)].vec);
			  delete (yyvsp[(3) - (3)].node);
			}
    break;

  case 234:
#line 1557 "PL.y"
    {
			  (yyval.vec) = new std::vector<CVC3::Expr>;
			  (yyval.vec)->push_back(*(yyvsp[(1) - (3)].node));
			  (yyval.vec)->push_back(*(yyvsp[(3) - (3)].node));
			  delete (yyvsp[(1) - (3)].node);
			  delete (yyvsp[(3) - (3)].node);
                        }
    break;

  case 235:
#line 1566 "PL.y"
    {
			  (yyvsp[(5) - (5)].vec)->push_back(VC->listExpr(*(yyvsp[(2) - (5)].node), *(yyvsp[(4) - (5)].node)));
			  (yyvsp[(5) - (5)].vec)->push_back(VC->idExpr("_COND"));
			  /* at this point, the list for ElseRest is 
			     in reverse order from what it should be. */
			  std::vector<CVC3::Expr> tmp;
			  tmp.insert(tmp.end(), (yyvsp[(5) - (5)].vec)->rbegin(), (yyvsp[(5) - (5)].vec)->rend());
			  (yyval.node) = new CVC3::Expr(VC->listExpr(tmp));
			  delete (yyvsp[(2) - (5)].node);
			  delete (yyvsp[(4) - (5)].node);
			  delete (yyvsp[(5) - (5)].vec);
			}
    break;

  case 236:
#line 1581 "PL.y"
    {
			  (yyval.vec) = new std::vector<CVC3::Expr>;
	                  (yyval.vec)->push_back(VC->listExpr("_ELSE",*(yyvsp[(2) - (3)].node)));
			  delete (yyvsp[(2) - (3)].node);
			}
    break;

  case 237:
#line 1587 "PL.y"
    {
			  /* NOTE that we're getting the list built
			     up in the reverse order here.  We'll fix
			     things when we produce a Conditional. */
			  (yyvsp[(5) - (5)].vec)->push_back(VC->listExpr(*(yyvsp[(2) - (5)].node), *(yyvsp[(4) - (5)].node)));
			  (yyval.vec) = (yyvsp[(5) - (5)].vec);
			  delete (yyvsp[(2) - (5)].node);
			  delete (yyvsp[(4) - (5)].node);
			}
    break;

  case 238:
#line 1599 "PL.y"
    {
			  (yyval.vec) = new std::vector<CVC3::Expr>;
			  (yyval.vec)->push_back(*(yyvsp[(1) - (1)].node));
			  delete (yyvsp[(1) - (1)].node);
			}
    break;

  case 239:
#line 1605 "PL.y"
    {
			  (yyvsp[(1) - (3)].vec)->push_back(*(yyvsp[(3) - (3)].node));
			  (yyval.vec) = (yyvsp[(1) - (3)].vec); 
			  delete (yyvsp[(3) - (3)].node);
			}
    break;

  case 240:
#line 1614 "PL.y"
    {
			  (yyval.vec) = (yyvsp[(3) - (5)].vec);
			}
    break;

  case 241:
#line 1619 "PL.y"
    {
			  (yyval.vec) = new std::vector<CVC3::Expr>;
			  (yyval.vec)->push_back(VC->listExpr(*(yyvsp[(1) - (1)].vec)));
			  delete (yyvsp[(1) - (1)].vec);
			}
    break;

  case 242:
#line 1625 "PL.y"
    {
			  (yyvsp[(1) - (2)].vec)->push_back(VC->listExpr(*(yyvsp[(2) - (2)].vec)));
			  (yyval.vec) = (yyvsp[(1) - (2)].vec); 
			  delete (yyvsp[(2) - (2)].vec);
			}
    break;

  case 243:
#line 1633 "PL.y"
    {
			  (yyval.node) = new CVC3::Expr(VC->listExpr(*(yyvsp[(1) - (3)].node), *(yyvsp[(3) - (3)].node)));
			  delete (yyvsp[(1) - (3)].node);
			  delete (yyvsp[(3) - (3)].node);
			}
    break;

  case 244:
#line 1641 "PL.y"
    {
			  (yyval.vec) = new std::vector<CVC3::Expr>;
			  (yyval.vec)->push_back(*(yyvsp[(1) - (1)].node));
			  delete (yyvsp[(1) - (1)].node);
			}
    break;

  case 245:
#line 1647 "PL.y"
    {
			  (yyval.vec)->push_back(*(yyvsp[(3) - (3)].node));
			  delete (yyvsp[(3) - (3)].node);
			}
    break;

  case 246:
#line 1654 "PL.y"
    {
			  (yyval.node) = new CVC3::Expr(VC->listExpr(*(yyvsp[(1) - (1)].vec)));
			  delete (yyvsp[(1) - (1)].vec);
			}
    break;

  case 247:
#line 1661 "PL.y"
    {
			  (yyval.vec) = new std::vector<CVC3::Expr>;
			  (yyval.vec)->push_back(VC->listExpr("_READ", *(yyvsp[(2) - (3)].node)));
			  delete (yyvsp[(2) - (3)].node);
			}
    break;

  case 248:
#line 1667 "PL.y"
    {
			  (yyval.vec) = new std::vector<CVC3::Expr>;
			  (yyval.vec)->push_back(*(yyvsp[(1) - (1)].node));
			  delete (yyvsp[(1) - (1)].node);
			}
    break;

  case 249:
#line 1673 "PL.y"
    {
			  (yyval.vec) = new std::vector<CVC3::Expr>;
			  (yyval.vec)->push_back(VC->listExpr("_RECORD_SELECT", *(yyvsp[(2) - (2)].node)));
			  delete (yyvsp[(2) - (2)].node);
			}
    break;

  case 250:
#line 1679 "PL.y"
    {
			  (yyval.vec) = new std::vector<CVC3::Expr>;
			  (yyval.vec)->push_back(VC->listExpr("_TUPLE_SELECT", *(yyvsp[(2) - (2)].node)));
			  delete (yyvsp[(2) - (2)].node);
			}
    break;

  case 251:
#line 1685 "PL.y"
    {
			  (yyvsp[(1) - (4)].vec)->push_back(VC->listExpr("_READ", *(yyvsp[(3) - (4)].node)));
			  (yyval.vec) = (yyvsp[(1) - (4)].vec);
			  delete (yyvsp[(3) - (4)].node);
			}
    break;

  case 252:
#line 1691 "PL.y"
    {
			  (yyvsp[(1) - (2)].vec)->push_back(*(yyvsp[(2) - (2)].node));
			  (yyval.vec) = (yyvsp[(1) - (2)].vec);
			  delete (yyvsp[(2) - (2)].node);
			}
    break;

  case 253:
#line 1697 "PL.y"
    {
			  (yyvsp[(1) - (3)].vec)->push_back(VC->listExpr("_RECORD_SELECT",*(yyvsp[(3) - (3)].node)));
			  (yyval.vec) = (yyvsp[(1) - (3)].vec);
			  delete (yyvsp[(3) - (3)].node);
			}
    break;

  case 254:
#line 1703 "PL.y"
    {
			  (yyvsp[(1) - (3)].vec)->push_back(VC->listExpr("_TUPLE_SELECT", *(yyvsp[(3) - (3)].node)));
			  (yyval.vec) = (yyvsp[(1) - (3)].vec);
			  delete (yyvsp[(3) - (3)].node);
			}
    break;

  case 255:
#line 1712 "PL.y"
    {
			  (yyval.node) = new CVC3::Expr(VC->listExpr("_LAMBDA", 
			                                   VC->listExpr(*(yyvsp[(3) - (6)].vec)), (*(yyvsp[(6) - (6)].node))));
			  delete (yyvsp[(3) - (6)].vec);
			  delete (yyvsp[(6) - (6)].node);
			}
    break;

  case 256:
#line 1721 "PL.y"
    {
			  (yyval.node) = new CVC3::Expr(VC->listExpr("_FORALL", 
			                                   VC->listExpr(*(yyvsp[(3) - (6)].vec)), *(yyvsp[(6) - (6)].node)));
			  delete (yyvsp[(3) - (6)].vec);
			  delete (yyvsp[(6) - (6)].node);
			}
    break;

  case 257:
#line 1729 "PL.y"
    {
			  (yyval.node) = new CVC3::Expr(VC->listExpr("_FORALL", 
			                                   VC->listExpr(*(yyvsp[(3) - (7)].vec)), *(yyvsp[(7) - (7)].node),
							   VC->listExpr(*(yyvsp[(6) - (7)].vec))));
			  delete (yyvsp[(3) - (7)].vec);
			  delete (yyvsp[(6) - (7)].vec);
			  delete (yyvsp[(7) - (7)].node);
			}
    break;

  case 258:
#line 1739 "PL.y"
    {
			  (yyval.node) = new CVC3::Expr(VC->listExpr("_EXISTS", 
			                                   VC->listExpr(*(yyvsp[(3) - (6)].vec)), (*(yyvsp[(6) - (6)].node))));
			  delete (yyvsp[(3) - (6)].vec);
			  delete (yyvsp[(6) - (6)].node);
			}
    break;

  case 259:
#line 1748 "PL.y"
    {
			  (yyval.node) = new CVC3::Expr(VC->listExpr("_EXISTS", 
			                                   VC->listExpr(*(yyvsp[(3) - (7)].vec)), *(yyvsp[(7) - (7)].node),
							   VC->listExpr(*(yyvsp[(6) - (7)].vec))));
			  delete (yyvsp[(3) - (7)].vec);
			  delete (yyvsp[(6) - (7)].vec);
			  delete (yyvsp[(7) - (7)].node);
			}
    break;

  case 260:
#line 1759 "PL.y"
    {
			  (yyval.node) = new CVC3::Expr
			    (VC->listExpr("_ARRAY_LITERAL", *(yyvsp[(3) - (6)].node), *(yyvsp[(6) - (6)].node)));
			  delete (yyvsp[(3) - (6)].node);
			  delete (yyvsp[(6) - (6)].node);
			}
    break;

  case 261:
#line 1767 "PL.y"
    {
			  (yyvsp[(2) - (3)].vec)->insert((yyvsp[(2) - (3)].vec)->begin(), VC->idExpr("_RECORD"));
			  (yyval.node) = new CVC3::Expr(VC->listExpr(*(yyvsp[(2) - (3)].vec)));
			  delete (yyvsp[(2) - (3)].vec);
			}
    break;

  case 262:
#line 1775 "PL.y"
    { 
			  (yyval.vec) = new std::vector<CVC3::Expr>;
			  (yyval.vec)->push_back(*(yyvsp[(1) - (1)].node)); 
			  delete (yyvsp[(1) - (1)].node);
			}
    break;

  case 263:
#line 1781 "PL.y"
    { 
			  (yyvsp[(1) - (3)].vec)->push_back(*(yyvsp[(3) - (3)].node));
			  (yyval.vec) = (yyvsp[(1) - (3)].vec); 
			  delete (yyvsp[(3) - (3)].node);
			}
    break;

  case 264:
#line 1789 "PL.y"
    {
			  (yyval.node) = new CVC3::Expr(VC->listExpr(*(yyvsp[(1) - (3)].node), *(yyvsp[(3) - (3)].node)));
			  delete (yyvsp[(1) - (3)].node);
			  delete (yyvsp[(3) - (3)].node);
			}
    break;

  case 265:
#line 1797 "PL.y"
    {
			  (yyvsp[(2) - (5)].vec)->push_back(*(yyvsp[(4) - (5)].node));
			  (yyvsp[(2) - (5)].vec)->insert((yyvsp[(2) - (5)].vec)->begin(),VC->idExpr("_TUPLE"));
			  (yyval.node) = new CVC3::Expr(VC->listExpr(*(yyvsp[(2) - (5)].vec)));
			  delete (yyvsp[(2) - (5)].vec);
			  delete (yyvsp[(4) - (5)].node);
			}
    break;

  case 266:
#line 1807 "PL.y"
    { 
			  (yyval.node) = new CVC3::Expr(VC->listExpr(*(yyvsp[(1) - (1)].vec)));
			  delete (yyvsp[(1) - (1)].vec);
			}
    break;

  case 267:
#line 1812 "PL.y"
    { 
			  (yyval.vec) = new std::vector<CVC3::Expr>;
			  (yyval.vec)->push_back(*(yyvsp[(1) - (1)].node));
			  delete (yyvsp[(1) - (1)].node);
                        }
    break;

  case 268:
#line 1818 "PL.y"
    { 
			  (yyvsp[(1) - (3)].vec)->push_back(*(yyvsp[(3) - (3)].node));
			  (yyval.vec) = (yyvsp[(1) - (3)].vec); 
			  delete (yyvsp[(3) - (3)].node);
			}
    break;

  case 269:
#line 1826 "PL.y"
    { 
			  (yyval.node) = new CVC3::Expr(VC->listExpr(*(yyvsp[(1) - (3)].node),*(yyvsp[(3) - (3)].node)));
			  delete (yyvsp[(1) - (3)].node);
			  delete (yyvsp[(3) - (3)].node);
			}
    break;

  case 270:
#line 1832 "PL.y"
    { 
			  (yyval.node) = new CVC3::Expr(VC->listExpr(*(yyvsp[(1) - (5)].node),*(yyvsp[(5) - (5)].node)));
			  delete (yyvsp[(1) - (5)].node);
			  delete (yyvsp[(3) - (5)].node);
			  delete (yyvsp[(5) - (5)].node);
			}
    break;

  case 271:
#line 1841 "PL.y"
    {
			  (yyval.node) = new CVC3::Expr(VC->listExpr("_LET", *(yyvsp[(2) - (4)].node), *(yyvsp[(4) - (4)].node)));
			  delete (yyvsp[(2) - (4)].node);
			  delete (yyvsp[(4) - (4)].node);
			}
    break;

  case 272:
#line 1849 "PL.y"
    { 
			  (yyval.node) = new CVC3::Expr(VC->listExpr(*(yyvsp[(1) - (1)].vec)));
			  delete (yyvsp[(1) - (1)].vec);
			}
    break;

  case 273:
#line 1854 "PL.y"
    { 
			  (yyval.vec) = new std::vector<CVC3::Expr>;
			  (yyval.vec)->push_back(*(yyvsp[(1) - (1)].node));
			  delete (yyvsp[(1) - (1)].node);
                        }
    break;

  case 274:
#line 1860 "PL.y"
    { 
			  (yyvsp[(1) - (3)].vec)->push_back(*(yyvsp[(3) - (3)].node));
			  (yyval.vec) = (yyvsp[(1) - (3)].vec); 
			  delete (yyvsp[(3) - (3)].node);
			}
    break;

  case 275:
#line 1868 "PL.y"
    { 
			  (yyval.node) = new CVC3::Expr(VC->listExpr(*(yyvsp[(1) - (3)].node), *(yyvsp[(3) - (3)].node)));
			  delete (yyvsp[(1) - (3)].node);
			  delete (yyvsp[(3) - (3)].node);
			}
    break;

  case 276:
#line 1874 "PL.y"
    { 
			  (yyval.node) = new CVC3::Expr(VC->listExpr(*(yyvsp[(1) - (5)].node),*(yyvsp[(5) - (5)].node)));
			  delete (yyvsp[(1) - (5)].node);
			  delete (yyvsp[(5) - (5)].node);
			}
    break;

  case 277:
#line 1882 "PL.y"
    {
			  (yyval.node) = new CVC3::Expr(VC->listExpr("_LET", *(yyvsp[(2) - (4)].node), *(yyvsp[(4) - (4)].node)));
			  delete (yyvsp[(2) - (4)].node);
			  delete (yyvsp[(4) - (4)].node);
			}
    break;

  case 278:
#line 1890 "PL.y"
    {
			  (yyvsp[(1) - (3)].vec)->push_back(*(yyvsp[(3) - (3)].node));
			  delete (yyvsp[(3) - (3)].node);
			  (yyval.node) = new CVC3::Expr(VC->listExpr(*(yyvsp[(1) - (3)].vec)));
			  delete (yyvsp[(1) - (3)].vec);
			
			}
    break;

  case 279:
#line 1900 "PL.y"
    {
			  (yyval.vec) = new std::vector<CVC3::Expr>;
			  (yyval.vec)->push_back(*(yyvsp[(1) - (1)].node));
			  delete (yyvsp[(1) - (1)].node);
			}
    break;

  case 280:
#line 1906 "PL.y"
    {
			  (yyvsp[(1) - (3)].vec)->push_back(*(yyvsp[(3) - (3)].node));
			  (yyval.vec) = (yyvsp[(1) - (3)].vec); 
			  delete (yyvsp[(3) - (3)].node);
			}
    break;

  case 281:
#line 1914 "PL.y"
    { 
			  (yyval.node) = new CVC3::Expr(VC->listExpr(*(yyvsp[(1) - (1)].vec)));
			  delete (yyvsp[(1) - (1)].vec);
			}
    break;

  case 282:
#line 1921 "PL.y"
    {
			  (yyval.node) = new CVC3::Expr(VC->listExpr("_CONST",
							   *(yyvsp[(1) - (5)].node), *(yyvsp[(3) - (5)].node), *(yyvsp[(5) - (5)].node)));
			  delete (yyvsp[(1) - (5)].node);
			  delete (yyvsp[(3) - (5)].node);
			  delete (yyvsp[(5) - (5)].node);
			}
    break;

  case 283:
#line 1929 "PL.y"
    {
			  (yyval.node) =new CVC3::Expr
			    (VC->listExpr("_CONST", VC->listExpr(*(yyvsp[(1) - (3)].node)), *(yyvsp[(3) - (3)].node)));
			  delete (yyvsp[(1) - (3)].node);
			  delete (yyvsp[(3) - (3)].node);
			}
    break;

  case 284:
#line 1936 "PL.y"
    {
			  std::vector<CVC3::Expr> tmp;
			  tmp.push_back(VC->idExpr("_DEFUN"));
			  tmp.push_back(*(yyvsp[(1) - (8)].node));
			  tmp.push_back(*(yyvsp[(3) - (8)].node));
			  tmp.push_back(*(yyvsp[(6) - (8)].node));
			  tmp.push_back(*(yyvsp[(8) - (8)].node));
			  (yyval.node) = new CVC3::Expr(VC->listExpr(tmp));
			  delete (yyvsp[(1) - (8)].node);
			  delete (yyvsp[(3) - (8)].node);
			  delete (yyvsp[(6) - (8)].node);
			  delete (yyvsp[(8) - (8)].node);
			}
    break;

  case 285:
#line 1950 "PL.y"
    {
			  std::vector<CVC3::Expr> tmp;
			  tmp.push_back(VC->idExpr("_DEFUN"));
			  tmp.push_back(*(yyvsp[(1) - (6)].node));
			  tmp.push_back(*(yyvsp[(3) - (6)].node));
			  tmp.push_back(*(yyvsp[(6) - (6)].node));
			  (yyval.node) = new CVC3::Expr(VC->listExpr(tmp));
			  delete (yyvsp[(1) - (6)].node);
			  delete (yyvsp[(3) - (6)].node);
			  delete (yyvsp[(6) - (6)].node);
			}
    break;

  case 286:
#line 1962 "PL.y"
    {
			  (yyvsp[(3) - (5)].vec)->insert((yyvsp[(3) - (5)].vec)->begin(), *(yyvsp[(1) - (5)].node));
			  (yyval.node) = new CVC3::Expr(VC->listExpr("_CONST", VC->listExpr(*(yyvsp[(3) - (5)].vec)), *(yyvsp[(5) - (5)].node)));
			  delete (yyvsp[(1) - (5)].node);
			  delete (yyvsp[(3) - (5)].vec);
			  delete (yyvsp[(5) - (5)].node);
			}
    break;

  case 287:
#line 1971 "PL.y"
    { (yyval.node) = (yyvsp[(1) - (1)].node); }
    break;

  case 288:
#line 1973 "PL.y"
    {
			  (yyval.node) = new CVC3::Expr(VC->listExpr("_TYPEDEF", *(yyvsp[(1) - (5)].node), *(yyvsp[(5) - (5)].node)));
			  delete (yyvsp[(1) - (5)].node);
			  delete (yyvsp[(5) - (5)].node);
			}
    break;

  case 289:
#line 1979 "PL.y"
    {
			  (yyval.node) =new CVC3::Expr(VC->listExpr("_TYPE", *(yyvsp[(1) - (3)].node)));
			  delete (yyvsp[(1) - (3)].node);
			}
    break;

  case 290:
#line 1984 "PL.y"
    {
			  std::vector<CVC3::Expr> tmp;
			  tmp.push_back(*(yyvsp[(1) - (5)].node));
			  tmp.insert(tmp.end(), (yyvsp[(3) - (5)].vec)->begin(), (yyvsp[(3) - (5)].vec)->end());
			  (yyval.node) = new CVC3::Expr(VC->listExpr("_TYPE", tmp));
			  delete (yyvsp[(1) - (5)].node);
			  delete (yyvsp[(3) - (5)].vec);
			}
    break;


/* Line 1267 of yacc.c.  */
#line 5805 "parsePL.cpp"
      default: break;
    }
  YY_SYMBOL_PRINT ("-> $$ =", yyr1[yyn], &yyval, &yyloc);

  YYPOPSTACK (yylen);
  yylen = 0;
  YY_STACK_PRINT (yyss, yyssp);

  *++yyvsp = yyval;


  /* Now `shift' the result of the reduction.  Determine what state
     that goes to, based on the state we popped back to and the rule
     number reduced by.  */

  yyn = yyr1[yyn];

  yystate = yypgoto[yyn - YYNTOKENS] + *yyssp;
  if (0 <= yystate && yystate <= YYLAST && yycheck[yystate] == *yyssp)
    yystate = yytable[yystate];
  else
    yystate = yydefgoto[yyn - YYNTOKENS];

  goto yynewstate;


/*------------------------------------.
| yyerrlab -- here on detecting error |
`------------------------------------*/
yyerrlab:
  /* If not already recovering from an error, report this error.  */
  if (!yyerrstatus)
    {
      ++yynerrs;
#if ! YYERROR_VERBOSE
      yyerror (YY_("syntax error"));
#else
      {
	YYSIZE_T yysize = yysyntax_error (0, yystate, yychar);
	if (yymsg_alloc < yysize && yymsg_alloc < YYSTACK_ALLOC_MAXIMUM)
	  {
	    YYSIZE_T yyalloc = 2 * yysize;
	    if (! (yysize <= yyalloc && yyalloc <= YYSTACK_ALLOC_MAXIMUM))
	      yyalloc = YYSTACK_ALLOC_MAXIMUM;
	    if (yymsg != yymsgbuf)
	      YYSTACK_FREE (yymsg);
	    yymsg = (char *) YYSTACK_ALLOC (yyalloc);
	    if (yymsg)
	      yymsg_alloc = yyalloc;
	    else
	      {
		yymsg = yymsgbuf;
		yymsg_alloc = sizeof yymsgbuf;
	      }
	  }

	if (0 < yysize && yysize <= yymsg_alloc)
	  {
	    (void) yysyntax_error (yymsg, yystate, yychar);
	    yyerror (yymsg);
	  }
	else
	  {
	    yyerror (YY_("syntax error"));
	    if (yysize != 0)
	      goto yyexhaustedlab;
	  }
      }
#endif
    }



  if (yyerrstatus == 3)
    {
      /* If just tried and failed to reuse look-ahead token after an
	 error, discard it.  */

      if (yychar <= YYEOF)
	{
	  /* Return failure if at end of input.  */
	  if (yychar == YYEOF)
	    YYABORT;
	}
      else
	{
	  yydestruct ("Error: discarding",
		      yytoken, &yylval);
	  yychar = YYEMPTY;
	}
    }

  /* Else will try to reuse look-ahead token after shifting the error
     token.  */
  goto yyerrlab1;


/*---------------------------------------------------.
| yyerrorlab -- error raised explicitly by YYERROR.  |
`---------------------------------------------------*/
yyerrorlab:

  /* Pacify compilers like GCC when the user code never invokes
     YYERROR and the label yyerrorlab therefore never appears in user
     code.  */
  if (/*CONSTCOND*/ 0)
     goto yyerrorlab;

  /* Do not reclaim the symbols of the rule which action triggered
     this YYERROR.  */
  YYPOPSTACK (yylen);
  yylen = 0;
  YY_STACK_PRINT (yyss, yyssp);
  yystate = *yyssp;
  goto yyerrlab1;


/*-------------------------------------------------------------.
| yyerrlab1 -- common code for both syntax error and YYERROR.  |
`-------------------------------------------------------------*/
yyerrlab1:
  yyerrstatus = 3;	/* Each real token shifted decrements this.  */

  for (;;)
    {
      yyn = yypact[yystate];
      if (yyn != YYPACT_NINF)
	{
	  yyn += YYTERROR;
	  if (0 <= yyn && yyn <= YYLAST && yycheck[yyn] == YYTERROR)
	    {
	      yyn = yytable[yyn];
	      if (0 < yyn)
		break;
	    }
	}

      /* Pop the current state because it cannot handle the error token.  */
      if (yyssp == yyss)
	YYABORT;


      yydestruct ("Error: popping",
		  yystos[yystate], yyvsp);
      YYPOPSTACK (1);
      yystate = *yyssp;
      YY_STACK_PRINT (yyss, yyssp);
    }

  if (yyn == YYFINAL)
    YYACCEPT;

  *++yyvsp = yylval;


  /* Shift the error token.  */
  YY_SYMBOL_PRINT ("Shifting", yystos[yyn], yyvsp, yylsp);

  yystate = yyn;
  goto yynewstate;


/*-------------------------------------.
| yyacceptlab -- YYACCEPT comes here.  |
`-------------------------------------*/
yyacceptlab:
  yyresult = 0;
  goto yyreturn;

/*-----------------------------------.
| yyabortlab -- YYABORT comes here.  |
`-----------------------------------*/
yyabortlab:
  yyresult = 1;
  goto yyreturn;

#ifndef yyoverflow
/*-------------------------------------------------.
| yyexhaustedlab -- memory exhaustion comes here.  |
`-------------------------------------------------*/
yyexhaustedlab:
  yyerror (YY_("memory exhausted"));
  yyresult = 2;
  /* Fall through.  */
#endif

yyreturn:
  if (yychar != YYEOF && yychar != YYEMPTY)
     yydestruct ("Cleanup: discarding lookahead",
		 yytoken, &yylval);
  /* Do not reclaim the symbols of the rule which action triggered
     this YYABORT or YYACCEPT.  */
  YYPOPSTACK (yylen);
  YY_STACK_PRINT (yyss, yyssp);
  while (yyssp != yyss)
    {
      yydestruct ("Cleanup: popping",
		  yystos[*yyssp], yyvsp);
      YYPOPSTACK (1);
    }
#ifndef yyoverflow
  if (yyss != yyssa)
    YYSTACK_FREE (yyss);
#endif
#if YYERROR_VERBOSE
  if (yymsg != yymsgbuf)
    YYSTACK_FREE (yymsg);
#endif
  /* Make sure YYID is used.  */
  return YYID (yyresult);
}


#line 1993 "PL.y"


