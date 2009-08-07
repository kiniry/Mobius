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
#define yyparse smtlibparse
#define yylex   smtliblex
#define yyerror smtliberror
#define yylval  smtliblval
#define yychar  smtlibchar
#define yydebug smtlibdebug
#define yynerrs smtlibnerrs


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




/* Copy the first part of user declarations.  */
#line 1 "smtlib.y"

/*****************************************************************************/
/*!
 * \file smtlib.y
 * 
 * Author: Clark Barrett
 * 
 * Created: Apr 30 2005
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
/* 
   This file contains the bison code for the parser that reads in CVC
   commands in SMT-LIB language.
*/

#include "vc.h"
#include "parser_exception.h"
#include "parser_temp.h"

// Exported shared data
namespace CVC3 {
  extern ParserTemp* parserTemp;
}
// Define shortcuts for various things
#define TMP CVC3::parserTemp
#define EXPR CVC3::parserTemp->expr
#define VC (CVC3::parserTemp->vc)
#define ARRAYSENABLED (CVC3::parserTemp->arrFlag)
#define BVENABLED (CVC3::parserTemp->bvFlag)
#define BVSIZE (CVC3::parserTemp->bvSize)
#define RAT(args) CVC3::newRational args
#define QUERYPARSED CVC3::parserTemp->queryParsed

// Suppress the bogus warning suppression in bison (it generates
// compile error)
#undef __GNUC_MINOR__

/* stuff that lives in smtlib.lex */
extern int smtliblex(void);

int smtliberror(const char *s)
{
  std::ostringstream ss;
  ss << CVC3::parserTemp->fileName << ":" << CVC3::parserTemp->lineNum
     << ": " << s;
  return CVC3::parserTemp->error(ss.str());
}



#define YYLTYPE_IS_TRIVIAL 1
#define YYMAXDEPTH 10485760



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
#line 66 "smtlib.y"
{
  std::string *str;
  std::vector<std::string> *strvec;
  CVC3::Expr *node;
  std::vector<CVC3::Expr> *vec;
  std::pair<std::vector<CVC3::Expr>, std::vector<std::string> > *pat_ann;
}
/* Line 187 of yacc.c.  */
#line 269 "parsesmtlib.cpp"
	YYSTYPE;
# define yystype YYSTYPE /* obsolescent; will be withdrawn */
# define YYSTYPE_IS_DECLARED 1
# define YYSTYPE_IS_TRIVIAL 1
#endif



/* Copy the second part of user declarations.  */


/* Line 216 of yacc.c.  */
#line 282 "parsesmtlib.cpp"

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
#define YYFINAL  6
/* YYLAST -- Last index in YYTABLE.  */
#define YYLAST   345

/* YYNTOKENS -- Number of terminals.  */
#define YYNTOKENS  47
/* YYNNTS -- Number of nonterminals.  */
#define YYNNTS  40
/* YYNRULES -- Number of rules.  */
#define YYNRULES  120
/* YYNRULES -- Number of states.  */
#define YYNSTATES  246

/* YYTRANSLATE(YYLEX) -- Bison symbol number corresponding to YYLEX.  */
#define YYUNDEFTOK  2
#define YYMAXUTOK   301

#define YYTRANSLATE(YYX)						\
  ((unsigned int) (YYX) <= YYMAXUTOK ? yytranslate[YYX] : YYUNDEFTOK)

/* YYTRANSLATE[YYLEX] -- Bison symbol number corresponding to YYLEX.  */
static const yytype_uint8 yytranslate[] =
{
       0,     2,     2,     2,     2,     2,     2,     2,     2,     2,
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
      35,    36,    37,    38,    39,    40,    41,    42,    43,    44,
      45,    46
};

#if YYDEBUG
/* YYPRHS[YYN] -- Index of the first RHS symbol of rule number YYN in
   YYRHS.  */
static const yytype_uint16 yyprhs[] =
{
       0,     0,     3,     5,    11,    13,    15,    17,    20,    24,
      28,    32,    36,    42,    48,    54,    58,    62,    64,    69,
      71,    73,    75,    77,    79,    82,    84,    87,    92,    96,
      99,   101,   104,   109,   113,   116,   118,   120,   123,   125,
     131,   136,   143,   149,   159,   168,   178,   187,   189,   191,
     194,   197,   202,   204,   207,   212,   214,   216,   218,   220,
     222,   224,   226,   228,   230,   232,   237,   243,   248,   254,
     259,   261,   263,   265,   267,   269,   272,   274,   279,   285,
     290,   298,   305,   315,   324,   334,   343,   345,   347,   349,
     352,   354,   357,   359,   364,   371,   373,   375,   377,   382,
     389,   391,   393,   395,   398,   401,   404,   406,   409,   411,
     413,   419,   424,   434,   443,   453,   462,   467,   474,   476,
     478
};

/* YYRHS -- A `-1'-separated list of the rules' RHS.  */
static const yytype_int8 yyrhs[] =
{
      48,     0,    -1,    49,    -1,    30,    38,    50,    51,    31,
      -1,    45,    -1,     4,    -1,    52,    -1,    51,    52,    -1,
      25,    35,    63,    -1,    25,    36,    63,    -1,    25,    37,
      54,    -1,    25,    24,    53,    -1,    25,    39,    30,    55,
      31,    -1,    25,    40,    30,    56,    31,    -1,    25,    41,
      30,    59,    31,    -1,    25,    22,     5,    -1,    25,    23,
       5,    -1,    76,    -1,     4,    26,     3,    27,    -1,     4,
      -1,    32,    -1,    33,    -1,    34,    -1,    78,    -1,    55,
      78,    -1,    57,    -1,    56,    57,    -1,    30,    58,    75,
      31,    -1,    30,    58,    31,    -1,    80,    55,    -1,    60,
      -1,    59,    60,    -1,    30,    61,    75,    31,    -1,    30,
      61,    31,    -1,    79,    55,    -1,    79,    -1,    63,    -1,
      62,    63,    -1,    70,    -1,    30,    69,    62,    75,    31,
      -1,    30,    69,    62,    31,    -1,    30,    68,    66,    63,
      64,    31,    -1,    30,    68,    66,    63,    31,    -1,    30,
      20,    30,    82,    73,    31,    63,    75,    31,    -1,    30,
      20,    30,    82,    73,    31,    63,    31,    -1,    30,    21,
      30,    83,    63,    31,    63,    75,    31,    -1,    30,    21,
      30,    83,    63,    31,    63,    31,    -1,    65,    -1,    76,
      -1,    64,    65,    -1,    64,    76,    -1,    46,    28,    84,
      29,    -1,    67,    -1,    66,    67,    -1,    30,    82,    78,
      31,    -1,    18,    -1,    19,    -1,    11,    -1,    12,    -1,
      13,    -1,    14,    -1,    15,    -1,    16,    -1,    17,    -1,
      71,    -1,    30,    71,    75,    31,    -1,    30,    79,    72,
      75,    31,    -1,    30,    79,    72,    31,    -1,    30,    44,
      72,    75,    31,    -1,    30,    44,    72,    31,    -1,     8,
      -1,     9,    -1,    83,    -1,    79,    -1,    73,    -1,    72,
      73,    -1,    74,    -1,    30,    74,    75,    31,    -1,    30,
      80,    72,    75,    31,    -1,    30,    80,    72,    31,    -1,
      30,    10,    63,    73,    73,    75,    31,    -1,    30,    10,
      63,    73,    73,    31,    -1,    30,    20,    30,    82,    73,
      31,    73,    75,    31,    -1,    30,    20,    30,    82,    73,
      31,    73,    31,    -1,    30,    21,    30,    83,    63,    31,
      73,    75,    31,    -1,    30,    21,    30,    83,    63,    31,
      73,    31,    -1,    82,    -1,    80,    -1,    76,    -1,    75,
      76,    -1,    81,    -1,    81,    77,    -1,     7,    -1,     4,
      26,     3,    27,    -1,     4,    26,     3,    25,     3,    27,
      -1,     4,    -1,     4,    -1,     6,    -1,     4,    26,     3,
      27,    -1,     4,    26,     3,    25,     3,    27,    -1,     4,
      -1,     6,    -1,     3,    -1,    25,     4,    -1,    43,     4,
      -1,    42,     4,    -1,    85,    -1,    84,    85,    -1,    82,
      -1,    83,    -1,    30,    86,    72,    75,    31,    -1,    30,
      86,    72,    31,    -1,    30,    20,    30,    82,    73,    31,
      85,    75,    31,    -1,    30,    20,    30,    82,    73,    31,
      85,    31,    -1,    30,    21,    30,    83,    63,    31,    85,
      75,    31,    -1,    30,    21,    30,    83,    63,    31,    85,
      31,    -1,     4,    26,     3,    27,    -1,     4,    26,     3,
      25,     3,    27,    -1,     4,    -1,     6,    -1,     3,    -1
};

/* YYRLINE[YYN] -- source line where rule number YYN was defined.  */
static const yytype_uint16 yyrline[] =
{
       0,   139,   139,   148,   155,   163,   171,   179,   190,   195,
     201,   205,   274,   279,   284,   289,   294,   299,   307,   313,
     320,   321,   322,   326,   332,   341,   348,   357,   362,   369,
     384,   391,   400,   405,   412,   421,   430,   437,   446,   450,
     457,   463,   471,   478,   487,   495,   504,   515,   521,   527,
     533,   541,   548,   554,   563,   572,   576,   583,   587,   591,
     595,   599,   603,   607,   614,   618,   623,   640,   649,   667,
     682,   686,   690,   694,   701,   707,   716,   720,   725,   733,
     740,   748,   755,   764,   772,   781,   792,   796,   809,   815,
     825,   827,   832,   841,   852,   866,   880,   911,   934,   970,
     983,  1150,  1176,  1185,  1192,  1200,  1208,  1215,  1224,  1228,
    1232,  1240,  1247,  1256,  1264,  1273,  1284,  1320,  1333,  1526,
    1552
};
#endif

#if YYDEBUG || YYERROR_VERBOSE || YYTOKEN_TABLE
/* YYTNAME[SYMBOL-NUM] -- String name of the symbol SYMBOL-NUM.
   First, the terminals, then, starting at YYNTOKENS, nonterminals.  */
static const char *const yytname[] =
{
  "$end", "error", "$undefined", "NUMERAL_TOK", "SYM_TOK", "STRING_TOK",
  "AR_SYMB", "USER_VAL_TOK", "TRUE_TOK", "FALSE_TOK", "ITE_TOK", "NOT_TOK",
  "IMPLIES_TOK", "IF_THEN_ELSE_TOK", "AND_TOK", "OR_TOK", "XOR_TOK",
  "IFF_TOK", "EXISTS_TOK", "FORALL_TOK", "LET_TOK", "FLET_TOK",
  "NOTES_TOK", "CVC_COMMAND_TOK", "LOGIC_TOK", "COLON_TOK", "LBRACKET_TOK",
  "RBRACKET_TOK", "LCURBRACK_TOK", "RCURBRACK_TOK", "LPAREN_TOK",
  "RPAREN_TOK", "SAT_TOK", "UNSAT_TOK", "UNKNOWN_TOK", "ASSUMPTION_TOK",
  "FORMULA_TOK", "STATUS_TOK", "BENCHMARK_TOK", "EXTRASORTS_TOK",
  "EXTRAFUNS_TOK", "EXTRAPREDS_TOK", "DOLLAR_TOK", "QUESTION_TOK",
  "DISTINCT_TOK", "EOF_TOK", "PAT_TOK", "$accept", "cmd", "benchmark",
  "bench_name", "bench_attributes", "bench_attribute", "logic_name",
  "status", "sort_symbs", "fun_symb_decls", "fun_symb_decl", "fun_sig",
  "pred_symb_decls", "pred_symb_decl", "pred_sig", "an_formulas",
  "an_formula", "patterns_annotations", "pattern", "quant_vars",
  "quant_var", "quant_symb", "connective", "an_atom", "prop_atom",
  "an_terms", "an_term", "basic_term", "annotations", "annotation",
  "user_value", "sort_symb", "pred_symb", "fun_symb", "attribute", "var",
  "fvar", "an_exprs", "an_expr", "fun_pred_symb", 0
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
     285,   286,   287,   288,   289,   290,   291,   292,   293,   294,
     295,   296,   297,   298,   299,   300,   301
};
# endif

/* YYR1[YYN] -- Symbol number of symbol that rule YYN derives.  */
static const yytype_uint8 yyr1[] =
{
       0,    47,    48,    49,    49,    50,    51,    51,    52,    52,
      52,    52,    52,    52,    52,    52,    52,    52,    53,    53,
      54,    54,    54,    55,    55,    56,    56,    57,    57,    58,
      59,    59,    60,    60,    61,    61,    62,    62,    63,    63,
      63,    63,    63,    63,    63,    63,    63,    64,    64,    64,
      64,    65,    66,    66,    67,    68,    68,    69,    69,    69,
      69,    69,    69,    69,    70,    70,    70,    70,    70,    70,
      71,    71,    71,    71,    72,    72,    73,    73,    73,    73,
      73,    73,    73,    73,    73,    73,    74,    74,    75,    75,
      76,    76,    77,    78,    78,    78,    79,    79,    80,    80,
      80,    80,    80,    81,    82,    83,    84,    84,    85,    85,
      85,    85,    85,    85,    85,    85,    86,    86,    86,    86,
      86
};

/* YYR2[YYN] -- Number of symbols composing right hand side of rule YYN.  */
static const yytype_uint8 yyr2[] =
{
       0,     2,     1,     5,     1,     1,     1,     2,     3,     3,
       3,     3,     5,     5,     5,     3,     3,     1,     4,     1,
       1,     1,     1,     1,     2,     1,     2,     4,     3,     2,
       1,     2,     4,     3,     2,     1,     1,     2,     1,     5,
       4,     6,     5,     9,     8,     9,     8,     1,     1,     2,
       2,     4,     1,     2,     4,     1,     1,     1,     1,     1,
       1,     1,     1,     1,     1,     4,     5,     4,     5,     4,
       1,     1,     1,     1,     1,     2,     1,     4,     5,     4,
       7,     6,     9,     8,     9,     8,     1,     1,     1,     2,
       1,     2,     1,     4,     6,     1,     1,     1,     4,     6,
       1,     1,     1,     2,     2,     2,     1,     2,     1,     1,
       5,     4,     9,     8,     9,     8,     4,     6,     1,     1,
       1
};

/* YYDEFACT[STATE-NAME] -- Default rule to reduce with in state
   STATE-NUM when YYTABLE doesn't specify something else to do.  Zero
   means the default is an error.  */
static const yytype_uint8 yydefact[] =
{
       0,     0,     4,     0,     2,     0,     1,     5,     0,     0,
       0,     6,    17,    90,   103,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     3,     7,    92,    91,    15,    16,
      19,    11,    96,    97,    70,    71,     0,     0,     8,    38,
      64,    73,    72,     9,    20,    21,    22,    10,     0,     0,
       0,     0,    57,    58,    59,    60,    61,    62,    63,    55,
      56,     0,     0,     0,     0,     0,     0,    73,   105,    95,
       0,    23,     0,     0,    25,     0,     0,    30,     0,     0,
       0,   102,   100,   101,     0,     0,     0,    74,    76,    87,
      86,     0,     0,    52,     0,    36,     0,     0,    88,     0,
       0,    12,    24,     0,     0,    13,    26,     0,    35,    14,
      31,    18,     0,     0,     0,     0,     0,     0,     0,    87,
     104,    69,    75,     0,     0,     0,     0,    53,    40,    37,
       0,    65,    89,    67,     0,     0,    28,     0,    29,    33,
       0,    34,     0,     0,     0,     0,     0,     0,     0,     0,
      68,     0,    42,     0,     0,    47,    48,    39,    66,     0,
      93,    27,    32,     0,     0,     0,    98,     0,     0,     0,
      77,    79,     0,    54,     0,    41,    49,    50,     0,     0,
       0,     0,     0,     0,     0,    78,     0,   108,   109,     0,
     106,    94,    44,     0,    46,     0,    99,    81,     0,     0,
       0,   120,   118,   119,     0,     0,     0,    51,   107,    43,
      45,    80,     0,     0,     0,     0,     0,     0,    83,     0,
      85,     0,     0,     0,     0,   111,     0,    82,    84,     0,
     116,     0,     0,   110,     0,     0,     0,   117,     0,     0,
     113,     0,   115,     0,   112,   114
};

/* YYDEFGOTO[NTERM-NUM].  */
static const yytype_int16 yydefgoto[] =
{
      -1,     3,     4,     8,    10,    11,    31,    47,    70,    73,
      74,   103,    76,    77,   107,    94,    38,   154,   155,    92,
      93,    64,    65,    39,    40,    86,    87,    88,    97,    98,
      27,    71,    41,    89,    13,    90,    42,   189,   190,   206
};

/* YYPACT[STATE-NUM] -- Index in YYTABLE of the portion describing
   STATE-NUM.  */
#define YYPACT_NINF -181
static const yytype_int16 yypact[] =
{
     -22,    14,  -181,    59,  -181,    66,  -181,  -181,    55,   282,
     -15,  -181,  -181,    83,  -181,    90,    95,   101,   266,   266,
      12,   105,   109,   172,  -181,  -181,  -181,  -181,  -181,  -181,
     189,  -181,  -181,  -181,  -181,  -181,    18,   127,  -181,  -181,
    -181,  -181,  -181,  -181,  -181,  -181,  -181,  -181,   199,   210,
     215,   254,  -181,  -181,  -181,  -181,  -181,  -181,  -181,  -181,
    -181,   234,   243,   166,   246,   266,   263,   166,  -181,   271,
      11,  -181,   288,    97,  -181,   171,   130,  -181,   272,   255,
     265,  -181,   274,  -181,    63,   297,    82,  -181,  -181,  -181,
    -181,   255,   273,  -181,   238,  -181,   298,   -13,  -181,   148,
     306,  -181,  -181,   -11,   199,  -181,  -181,    -6,   199,  -181,
    -181,  -181,   166,   266,   307,   266,   281,   283,   263,   166,
    -181,  -181,  -181,    50,   199,   208,    46,  -181,  -181,  -181,
      92,  -181,  -181,  -181,    99,   159,  -181,   113,   199,  -181,
     124,   199,   285,   289,   260,   166,   255,   265,   125,   228,
    -181,   293,  -181,   284,    73,  -181,  -181,  -181,  -181,   311,
    -181,  -181,  -181,   266,   266,   322,  -181,   166,   166,   266,
    -181,  -181,   143,  -181,    78,  -181,  -181,  -181,   299,   151,
     163,   300,   164,   301,   302,  -181,   177,  -181,  -181,    21,
    -181,  -181,  -181,   174,  -181,   175,  -181,  -181,   176,   166,
     166,  -181,   303,  -181,   304,   305,   166,  -181,  -181,  -181,
    -181,  -181,   179,   205,   325,   255,   265,   235,  -181,   212,
    -181,   223,   268,   166,   266,  -181,   224,  -181,  -181,   327,
    -181,   308,   309,  -181,   310,    78,    78,  -181,   231,   236,
    -181,   258,  -181,   259,  -181,  -181
};

/* YYPGOTO[NTERM-NUM].  */
static const yytype_int16 yypgoto[] =
{
    -181,  -181,  -181,  -181,  -181,   321,  -181,  -181,   -87,  -181,
     269,  -181,  -181,   262,  -181,  -181,   -16,  -181,   182,  -181,
     249,  -181,  -181,  -181,   -31,   -61,   -58,   261,   -46,    -8,
    -181,   -59,   -32,    30,  -181,   -78,   -73,  -181,  -180,  -181
};

/* YYTABLE[YYPACT[STATE-NUM]].  What to do in state STATE-NUM.  If
   positive, shift that token.  If negative, reduce the rule which
   number is the opposite.  If zero, do what YYDEFACT says.
   If YYTABLE_NINF, syntax error.  */
#define YYTABLE_NINF -1
static const yytype_uint8 yytable[] =
{
      12,   112,    12,    43,    67,    66,    99,   113,     1,   208,
       9,   102,    96,   124,    96,    69,    24,   138,   131,    96,
     136,   141,    32,     2,    33,   139,    34,    35,   122,    52,
      53,    54,    55,    56,    57,    58,    59,    60,    61,    62,
     123,   122,   101,   108,    44,    45,    46,   124,   130,    95,
     207,   186,     5,   134,   142,   238,   239,   137,   149,     6,
      37,   140,    63,    37,    85,   151,    81,    82,   168,    83,
       7,    96,   148,   115,   169,    96,   126,   152,   129,   102,
       9,   150,   102,   116,   117,    81,    82,   167,    83,   132,
      26,   122,   153,    67,    66,    28,   187,   143,    96,   145,
      29,   188,   104,   172,   175,    30,    85,    96,   186,   182,
     183,   187,    84,   121,   119,   132,   188,    96,   156,   153,
      37,    85,   132,   157,    96,    85,   132,    72,   105,   132,
     158,    68,   132,   193,   195,    48,   198,   223,    96,    49,
     132,   212,   213,   224,   161,   217,   177,   179,   180,    96,
      96,    81,    82,   184,    83,   162,   170,   187,   187,   122,
      75,   109,   188,   188,   132,   231,   219,   221,    96,    81,
      82,   226,    83,    96,   185,    32,    96,    33,    84,   133,
     201,   202,   192,   203,   159,   132,   160,   132,    96,    96,
     132,    85,   241,   243,   194,   197,    84,   204,   205,    96,
      96,    96,    50,    69,    96,   209,   210,   211,   232,    85,
     218,   132,    32,   132,    33,    51,    34,    35,   132,    52,
      53,    54,    55,    56,    57,    58,    59,    60,    61,    62,
      96,    81,    82,   132,    83,   132,   220,    96,    81,    82,
      72,    83,    32,   227,    33,    75,    34,    35,    96,    96,
      37,    85,    63,    96,   228,   233,    96,    78,    84,   171,
      96,    96,   240,    96,    79,    84,   225,   242,    36,   128,
      32,    85,    33,    80,    34,    35,    91,    32,    85,    33,
      37,    34,    35,    96,    96,   165,    14,   166,    96,   244,
     245,    81,    82,   229,    83,   230,    36,   100,    85,   111,
     114,   120,    14,   125,    15,    16,    17,    37,    37,   135,
     144,   146,   174,   147,   178,    37,   163,    18,    19,    20,
     164,    21,    22,    23,   173,   181,   191,   196,   222,   214,
     234,    25,   199,   200,   215,   216,   176,   237,   110,   235,
     236,   127,   106,     0,     0,   118
};

static const yytype_int16 yycheck[] =
{
       8,    79,    10,    19,    36,    36,    67,    80,    30,   189,
      25,    70,    25,    91,    25,     4,    31,   104,    31,    25,
      31,   108,     4,    45,     6,    31,     8,     9,    86,    11,
      12,    13,    14,    15,    16,    17,    18,    19,    20,    21,
      86,    99,    31,    75,    32,    33,    34,   125,    94,    65,
      29,    30,    38,    99,   112,   235,   236,   103,   119,     0,
      42,   107,    44,    42,    43,   124,     3,     4,   146,     6,
       4,    25,   118,    10,   147,    25,    92,    31,    94,   138,
      25,    31,   141,    20,    21,     3,     4,   145,     6,    97,
       7,   149,    46,   125,   125,     5,   174,   113,    25,   115,
       5,   174,    72,   149,    31,     4,    43,    25,    30,   167,
     168,   189,    30,    31,    84,   123,   189,    25,   126,    46,
      42,    43,   130,    31,    25,    43,   134,    30,    31,   137,
      31,     4,   140,   179,   180,    30,   182,   215,    25,    30,
     148,   199,   200,   216,    31,   206,   154,   163,   164,    25,
      25,     3,     4,   169,     6,    31,    31,   235,   236,   217,
      30,    31,   235,   236,   172,   223,   212,   213,    25,     3,
       4,   217,     6,    25,    31,     4,    25,     6,    30,    31,
       3,     4,    31,     6,    25,   193,    27,   195,    25,    25,
     198,    43,   238,   239,    31,    31,    30,    20,    21,    25,
      25,    25,    30,     4,    25,    31,    31,    31,   224,    43,
      31,   219,     4,   221,     6,    26,     8,     9,   226,    11,
      12,    13,    14,    15,    16,    17,    18,    19,    20,    21,
      25,     3,     4,   241,     6,   243,    31,    25,     3,     4,
      30,     6,     4,    31,     6,    30,     8,     9,    25,    25,
      42,    43,    44,    25,    31,    31,    25,     3,    30,    31,
      25,    25,    31,    25,    30,    30,    31,    31,    30,    31,
       4,    43,     6,    30,     8,     9,    30,     4,    43,     6,
      42,     8,     9,    25,    25,    25,     4,    27,    25,    31,
      31,     3,     4,    25,     6,    27,    30,    26,    43,    27,
      26,     4,     4,    30,    22,    23,    24,    42,    42,     3,
       3,    30,    28,    30,     3,    42,    31,    35,    36,    37,
      31,    39,    40,    41,    31,     3,    27,    27,     3,    26,
       3,    10,    31,    31,    30,    30,   154,    27,    76,    31,
      31,    92,    73,    -1,    -1,    84
};

/* YYSTOS[STATE-NUM] -- The (internal number of the) accessing
   symbol of state STATE-NUM.  */
static const yytype_uint8 yystos[] =
{
       0,    30,    45,    48,    49,    38,     0,     4,    50,    25,
      51,    52,    76,    81,     4,    22,    23,    24,    35,    36,
      37,    39,    40,    41,    31,    52,     7,    77,     5,     5,
       4,    53,     4,     6,     8,     9,    30,    42,    63,    70,
      71,    79,    83,    63,    32,    33,    34,    54,    30,    30,
      30,    26,    11,    12,    13,    14,    15,    16,    17,    18,
      19,    20,    21,    44,    68,    69,    71,    79,     4,     4,
      55,    78,    30,    56,    57,    30,    59,    60,     3,    30,
      30,     3,     4,     6,    30,    43,    72,    73,    74,    80,
      82,    30,    66,    67,    62,    63,    25,    75,    76,    72,
      26,    31,    78,    58,    80,    31,    57,    61,    79,    31,
      60,    27,    82,    83,    26,    10,    20,    21,    74,    80,
       4,    31,    73,    75,    82,    30,    63,    67,    31,    63,
      75,    31,    76,    31,    75,     3,    31,    75,    55,    31,
      75,    55,    73,    63,     3,    63,    30,    30,    75,    72,
      31,    78,    31,    46,    64,    65,    76,    31,    31,    25,
      27,    31,    31,    31,    31,    25,    27,    73,    82,    83,
      31,    31,    75,    31,    28,    31,    65,    76,     3,    63,
      63,     3,    73,    73,    63,    31,    30,    82,    83,    84,
      85,    27,    31,    75,    31,    75,    27,    31,    75,    31,
      31,     3,     4,     6,    20,    21,    86,    29,    85,    31,
      31,    31,    73,    73,    26,    30,    30,    72,    31,    75,
      31,    75,     3,    82,    83,    31,    75,    31,    31,    25,
      27,    73,    63,    31,     3,    31,    31,    27,    85,    85,
      31,    75,    31,    75,    31,    31
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
#line 140 "smtlib.y"
    {
      EXPR = *(yyvsp[(1) - (1)].node);
      delete (yyvsp[(1) - (1)].node);
      YYACCEPT;
    }
    break;

  case 3:
#line 149 "smtlib.y"
    {
      if (!QUERYPARSED)
        (yyvsp[(4) - (5)].vec)->push_back(CVC3::Expr(VC->listExpr("_CHECKSAT", CVC3::Expr(VC->idExpr("_TRUE_EXPR")))));
      (yyval.node) = new CVC3::Expr(VC->listExpr("_SEQ",*(yyvsp[(4) - (5)].vec)));
      delete (yyvsp[(4) - (5)].vec);
    }
    break;

  case 4:
#line 156 "smtlib.y"
    { 
      TMP->done = true;
      (yyval.node) = new CVC3::Expr();
    }
    break;

  case 5:
#line 164 "smtlib.y"
    {
      (yyval.node) = NULL;
      delete (yyvsp[(1) - (1)].str);
    }
    break;

  case 6:
#line 172 "smtlib.y"
    {
      (yyval.vec) = new std::vector<CVC3::Expr>;
      if ((yyvsp[(1) - (1)].node)) {
	(yyval.vec)->push_back(*(yyvsp[(1) - (1)].node));
	delete (yyvsp[(1) - (1)].node);
      }
    }
    break;

  case 7:
#line 180 "smtlib.y"
    {
      (yyval.vec) = (yyvsp[(1) - (2)].vec);
      if ((yyvsp[(2) - (2)].node)) {
	(yyval.vec)->push_back(*(yyvsp[(2) - (2)].node));
	delete (yyvsp[(2) - (2)].node);
      }
    }
    break;

  case 8:
#line 191 "smtlib.y"
    {
      (yyval.node) = new CVC3::Expr(VC->listExpr("_ASSERT", *(yyvsp[(3) - (3)].node)));
      delete (yyvsp[(3) - (3)].node);
    }
    break;

  case 9:
#line 196 "smtlib.y"
    {
      (yyval.node) = new CVC3::Expr(VC->listExpr("_CHECKSAT", *(yyvsp[(3) - (3)].node)));
      QUERYPARSED = true;
      delete (yyvsp[(3) - (3)].node);
    }
    break;

  case 10:
#line 202 "smtlib.y"
    {
      (yyval.node) = NULL;
    }
    break;

  case 11:
#line 206 "smtlib.y"
    {
      ARRAYSENABLED = false;
      BVENABLED = false;
      if (*(yyvsp[(3) - (3)].str) == "QF_UF") {
        (yyval.node) = new CVC3::Expr(VC->listExpr("_TYPE", VC->idExpr("U")));
      }
      else if (*(yyvsp[(3) - (3)].str) == "QF_A" ||
               *(yyvsp[(3) - (3)].str) == "QF_AX") {
        ARRAYSENABLED = true;
        std::vector<CVC3::Expr> tmp;
        tmp.push_back(VC->listExpr("_TYPE", VC->idExpr("Index")));
        tmp.push_back(VC->listExpr("_TYPE", VC->idExpr("Element")));
        tmp.push_back(VC->listExpr("_TYPEDEF", VC->idExpr("Array"),
                                   VC->listExpr("_ARRAY",
                                                VC->idExpr("Index"),
                                                VC->idExpr("Element"))));
        (yyval.node) = new CVC3::Expr(VC->listExpr("_SEQ", tmp));
      }
      else if (*(yyvsp[(3) - (3)].str) == "QF_AUFLIA" ||
               *(yyvsp[(3) - (3)].str) == "AUFLIA") {
        ARRAYSENABLED = true;
        std::vector<CVC3::Expr> tmp;
        tmp.push_back(VC->listExpr("_TYPEDEF", VC->idExpr("Array"),
                                   VC->listExpr("_ARRAY",
                                                VC->idExpr("_INT"),
                                                VC->idExpr("_INT"))));
        (yyval.node) = new CVC3::Expr(VC->listExpr("_SEQ", tmp));
      }
      else if (*(yyvsp[(3) - (3)].str) == "QF_AUFLIRA" ||
               *(yyvsp[(3) - (3)].str) == "AUFLIRA" ||
               *(yyvsp[(3) - (3)].str) == "QF_AUFNIRA" ||
               *(yyvsp[(3) - (3)].str) == "AUFNIRA") {
        ARRAYSENABLED = true;
        std::vector<CVC3::Expr> tmp;
        tmp.push_back(VC->listExpr("_TYPEDEF", VC->idExpr("Array1"),
                                   VC->listExpr("_ARRAY",
                                                VC->idExpr("_INT"),
                                                VC->idExpr("_REAL"))));
        tmp.push_back(VC->listExpr("_TYPEDEF", VC->idExpr("Array2"),
                                   VC->listExpr("_ARRAY",
                                                VC->idExpr("_INT"),
                                                VC->idExpr("Array1"))));
        (yyval.node) = new CVC3::Expr(VC->listExpr("_SEQ", tmp));
      }
      else if (*(yyvsp[(3) - (3)].str) == "QF_AUFBV" ||
               *(yyvsp[(3) - (3)].str) == "QF_ABV") {
        ARRAYSENABLED = true;
        BVENABLED = true;
        (yyval.node) = NULL;
//         $$ = new CVC3::Expr(VC->listExpr("_TYPEDEF", VC->idExpr("Array"),
//                                          VC->listExpr("_ARRAY",
//                                                       VC->listExpr("_BITVECTOR", VC->ratExpr(32)),
//                                                       VC->listExpr("_BITVECTOR", VC->ratExpr(8)))));
      }
      else if (*(yyvsp[(3) - (3)].str) == "QF_BV" ||
               *(yyvsp[(3) - (3)].str) == "QF_UFBV") {
        BVENABLED = true;
        (yyval.node) = NULL;
      }
    // This enables the new arith for QF_LRA, but this results in assertion failures in DEBUG mode
      else if (*(yyvsp[(3) - (3)].str) == "QF_LRA") {
         (yyval.node) = new CVC3::Expr(VC->listExpr("_OPTION", VC->stringExpr("arith-new"), VC->ratExpr(1)));
       }
      else {
        (yyval.node) = NULL;
      }
      delete (yyvsp[(3) - (3)].str);
    }
    break;

  case 12:
#line 275 "smtlib.y"
    {
      (yyval.node) = new CVC3::Expr(VC->listExpr("_TYPE", *(yyvsp[(4) - (5)].vec)));
      delete (yyvsp[(4) - (5)].vec);
    }
    break;

  case 13:
#line 280 "smtlib.y"
    {
      (yyval.node) = new CVC3::Expr(VC->listExpr("_SEQ", *(yyvsp[(4) - (5)].vec)));
      delete (yyvsp[(4) - (5)].vec);
    }
    break;

  case 14:
#line 285 "smtlib.y"
    {
      (yyval.node) = new CVC3::Expr(VC->listExpr("_SEQ", *(yyvsp[(4) - (5)].vec)));
      delete (yyvsp[(4) - (5)].vec);
    }
    break;

  case 15:
#line 290 "smtlib.y"
    {
      (yyval.node) = NULL;
      delete (yyvsp[(3) - (3)].str);
    }
    break;

  case 16:
#line 295 "smtlib.y"
    {
      (yyval.node) = new CVC3::Expr(VC->listExpr(VC->idExpr("_"+*(yyvsp[(3) - (3)].str))));
      delete (yyvsp[(3) - (3)].str);
    }
    break;

  case 17:
#line 300 "smtlib.y"
    {
      (yyval.node) = NULL;
      delete (yyvsp[(1) - (1)].str);
    }
    break;

  case 18:
#line 308 "smtlib.y"
    {
      BVSIZE = atoi((yyvsp[(3) - (4)].str)->c_str());
      delete (yyvsp[(3) - (4)].str);
      (yyval.str) = (yyvsp[(1) - (4)].str);
    }
    break;

  case 19:
#line 314 "smtlib.y"
    {
      (yyval.str) = (yyvsp[(1) - (1)].str);
    }
    break;

  case 20:
#line 320 "smtlib.y"
    { (yyval.node) = NULL; }
    break;

  case 21:
#line 321 "smtlib.y"
    { (yyval.node) = NULL; }
    break;

  case 22:
#line 322 "smtlib.y"
    { (yyval.node) = NULL; }
    break;

  case 23:
#line 327 "smtlib.y"
    {
      (yyval.vec) = new std::vector<CVC3::Expr>;
      (yyval.vec)->push_back(*(yyvsp[(1) - (1)].node));
      delete (yyvsp[(1) - (1)].node);
    }
    break;

  case 24:
#line 333 "smtlib.y"
    { 
      (yyvsp[(1) - (2)].vec)->push_back(*(yyvsp[(2) - (2)].node));
      (yyval.vec) = (yyvsp[(1) - (2)].vec);
      delete (yyvsp[(2) - (2)].node);
    }
    break;

  case 25:
#line 342 "smtlib.y"
    {
      (yyval.vec) = new std::vector<CVC3::Expr>;
      (yyval.vec)->push_back(*(yyvsp[(1) - (1)].node));
      delete (yyvsp[(1) - (1)].node);
    }
    break;

  case 26:
#line 349 "smtlib.y"
    {
      (yyvsp[(1) - (2)].vec)->push_back(*(yyvsp[(2) - (2)].node));
      (yyval.vec) = (yyvsp[(1) - (2)].vec);
      delete (yyvsp[(2) - (2)].node);
    }
    break;

  case 27:
#line 358 "smtlib.y"
    {
      (yyval.node) = (yyvsp[(2) - (4)].node);
      delete (yyvsp[(3) - (4)].strvec);
    }
    break;

  case 28:
#line 363 "smtlib.y"
    {
      (yyval.node) = (yyvsp[(2) - (3)].node);
    }
    break;

  case 29:
#line 370 "smtlib.y"
    {
      if ((yyvsp[(2) - (2)].vec)->size() == 1) {
        (yyval.node) = new CVC3::Expr(VC->listExpr("_CONST", VC->listExpr(*(yyvsp[(1) - (2)].vec)), (*(yyvsp[(2) - (2)].vec))[0]));
      }
      else {
        CVC3::Expr tmp(VC->listExpr("_ARROW", *(yyvsp[(2) - (2)].vec)));
        (yyval.node) = new CVC3::Expr(VC->listExpr("_CONST", VC->listExpr(*(yyvsp[(1) - (2)].vec)), tmp));
      }
      delete (yyvsp[(1) - (2)].vec);
      delete (yyvsp[(2) - (2)].vec);
    }
    break;

  case 30:
#line 385 "smtlib.y"
    {
      (yyval.vec) = new std::vector<CVC3::Expr>;
      (yyval.vec)->push_back(*(yyvsp[(1) - (1)].node));
      delete (yyvsp[(1) - (1)].node);
    }
    break;

  case 31:
#line 392 "smtlib.y"
    {
      (yyvsp[(1) - (2)].vec)->push_back(*(yyvsp[(2) - (2)].node));
      (yyval.vec) = (yyvsp[(1) - (2)].vec);
      delete (yyvsp[(2) - (2)].node);
    }
    break;

  case 32:
#line 401 "smtlib.y"
    {
      (yyval.node) = (yyvsp[(2) - (4)].node);
      delete (yyvsp[(3) - (4)].strvec);
    }
    break;

  case 33:
#line 406 "smtlib.y"
    {
      (yyval.node) = (yyvsp[(2) - (3)].node);
    }
    break;

  case 34:
#line 413 "smtlib.y"
    {
      std::vector<CVC3::Expr> tmp(*(yyvsp[(2) - (2)].vec));
      tmp.push_back(VC->idExpr("_BOOLEAN"));
      CVC3::Expr tmp2(VC->listExpr("_ARROW", tmp));
      (yyval.node) = new CVC3::Expr(VC->listExpr("_CONST", VC->listExpr(*(yyvsp[(1) - (2)].node)), tmp2));
      delete (yyvsp[(1) - (2)].node);
      delete (yyvsp[(2) - (2)].vec);
    }
    break;

  case 35:
#line 422 "smtlib.y"
    {
      (yyval.node) = new CVC3::Expr(VC->listExpr("_CONST", VC->listExpr(*(yyvsp[(1) - (1)].node)),
                                       VC->idExpr("_BOOLEAN")));
      delete (yyvsp[(1) - (1)].node);
    }
    break;

  case 36:
#line 431 "smtlib.y"
    {
      (yyval.vec) = new std::vector<CVC3::Expr>;
      (yyval.vec)->push_back(*(yyvsp[(1) - (1)].node));
      delete (yyvsp[(1) - (1)].node);
    }
    break;

  case 37:
#line 438 "smtlib.y"
    {
      (yyvsp[(1) - (2)].vec)->push_back(*(yyvsp[(2) - (2)].node));
      (yyval.vec) = (yyvsp[(1) - (2)].vec);
      delete (yyvsp[(2) - (2)].node);
    }
    break;

  case 38:
#line 447 "smtlib.y"
    {
      (yyval.node) = (yyvsp[(1) - (1)].node);
    }
    break;

  case 39:
#line 451 "smtlib.y"
    {
      (yyval.node) = new CVC3::Expr(VC->listExpr(*(yyvsp[(2) - (5)].str), *(yyvsp[(3) - (5)].vec)));
      delete (yyvsp[(2) - (5)].str);
      delete (yyvsp[(3) - (5)].vec);
      delete (yyvsp[(4) - (5)].strvec);
    }
    break;

  case 40:
#line 458 "smtlib.y"
    {
      (yyval.node) = new CVC3::Expr(VC->listExpr(*(yyvsp[(2) - (4)].str), *(yyvsp[(3) - (4)].vec)));
      delete (yyvsp[(2) - (4)].str);
      delete (yyvsp[(3) - (4)].vec);
    }
    break;

  case 41:
#line 464 "smtlib.y"
    {
      (yyval.node) = new CVC3::Expr(VC->listExpr(*(yyvsp[(2) - (6)].str), VC->listExpr(*(yyvsp[(3) - (6)].vec)), *(yyvsp[(4) - (6)].node), VC->listExpr((*(yyvsp[(5) - (6)].pat_ann)).first)));
      delete (yyvsp[(2) - (6)].str);
      delete (yyvsp[(3) - (6)].vec);
      delete (yyvsp[(4) - (6)].node);
      delete (yyvsp[(5) - (6)].pat_ann);
    }
    break;

  case 42:
#line 472 "smtlib.y"
    {
      (yyval.node) = new CVC3::Expr(VC->listExpr(*(yyvsp[(2) - (5)].str), VC->listExpr(*(yyvsp[(3) - (5)].vec)), *(yyvsp[(4) - (5)].node)));
      delete (yyvsp[(2) - (5)].str);
      delete (yyvsp[(3) - (5)].vec);
      delete (yyvsp[(4) - (5)].node);
    }
    break;

  case 43:
#line 479 "smtlib.y"
    {
      CVC3::Expr e(VC->listExpr(VC->listExpr(*(yyvsp[(4) - (9)].node), *(yyvsp[(5) - (9)].node))));
      (yyval.node) = new CVC3::Expr(VC->listExpr("_LET", e, *(yyvsp[(7) - (9)].node)));
      delete (yyvsp[(4) - (9)].node);
      delete (yyvsp[(5) - (9)].node);
      delete (yyvsp[(7) - (9)].node);
      delete (yyvsp[(8) - (9)].strvec);
    }
    break;

  case 44:
#line 488 "smtlib.y"
    {
      CVC3::Expr e(VC->listExpr(VC->listExpr(*(yyvsp[(4) - (8)].node), *(yyvsp[(5) - (8)].node))));
      (yyval.node) = new CVC3::Expr(VC->listExpr("_LET", e, *(yyvsp[(7) - (8)].node)));
      delete (yyvsp[(4) - (8)].node);
      delete (yyvsp[(5) - (8)].node);
      delete (yyvsp[(7) - (8)].node);
    }
    break;

  case 45:
#line 496 "smtlib.y"
    {
      CVC3::Expr e(VC->listExpr(VC->listExpr(*(yyvsp[(4) - (9)].node), *(yyvsp[(5) - (9)].node))));
      (yyval.node) = new CVC3::Expr(VC->listExpr("_LET", e, *(yyvsp[(7) - (9)].node)));
      delete (yyvsp[(4) - (9)].node);
      delete (yyvsp[(5) - (9)].node);
      delete (yyvsp[(7) - (9)].node);
      delete (yyvsp[(8) - (9)].strvec);
    }
    break;

  case 46:
#line 505 "smtlib.y"
    {
      CVC3::Expr e(VC->listExpr(VC->listExpr(*(yyvsp[(4) - (8)].node), *(yyvsp[(5) - (8)].node))));
      (yyval.node) = new CVC3::Expr(VC->listExpr("_LET", e, *(yyvsp[(7) - (8)].node)));
      delete (yyvsp[(4) - (8)].node);
      delete (yyvsp[(5) - (8)].node);
      delete (yyvsp[(7) - (8)].node);
    }
    break;

  case 47:
#line 516 "smtlib.y"
    {
       (yyval.pat_ann) = new std::pair<std::vector<CVC3::Expr>, std::vector<std::string> >;
       (yyval.pat_ann)->first.push_back(*(yyvsp[(1) - (1)].node));
       delete (yyvsp[(1) - (1)].node);
     }
    break;

  case 48:
#line 522 "smtlib.y"
    {
       (yyval.pat_ann) = new std::pair<std::vector<CVC3::Expr>, std::vector<std::string> >;
       (yyval.pat_ann)->second.push_back(*(yyvsp[(1) - (1)].str));
       delete (yyvsp[(1) - (1)].str);
     }
    break;

  case 49:
#line 528 "smtlib.y"
    {
       (yyvsp[(1) - (2)].pat_ann)->first.push_back(*(yyvsp[(2) - (2)].node));
       (yyval.pat_ann) = (yyvsp[(1) - (2)].pat_ann);
       delete (yyvsp[(2) - (2)].node);
     }
    break;

  case 50:
#line 534 "smtlib.y"
    {
       (yyvsp[(1) - (2)].pat_ann)->second.push_back(*(yyvsp[(2) - (2)].str));
       (yyval.pat_ann) = (yyvsp[(1) - (2)].pat_ann);
       delete (yyvsp[(2) - (2)].str);
     }
    break;

  case 51:
#line 542 "smtlib.y"
    {
       (yyval.node) = new CVC3::Expr(VC->listExpr(*(yyvsp[(3) - (4)].vec)));
       delete (yyvsp[(3) - (4)].vec);
     }
    break;

  case 52:
#line 549 "smtlib.y"
    {
      (yyval.vec) = new std::vector<CVC3::Expr>;
      (yyval.vec)->push_back(*(yyvsp[(1) - (1)].node));
      delete (yyvsp[(1) - (1)].node);
    }
    break;

  case 53:
#line 555 "smtlib.y"
    {
      (yyvsp[(1) - (2)].vec)->push_back(*(yyvsp[(2) - (2)].node));
      (yyval.vec) = (yyvsp[(1) - (2)].vec); 
      delete (yyvsp[(2) - (2)].node);
    }
    break;

  case 54:
#line 564 "smtlib.y"
    {
      (yyval.node) = new CVC3::Expr(VC->listExpr(*(yyvsp[(2) - (4)].node), *(yyvsp[(3) - (4)].node)));
      delete (yyvsp[(2) - (4)].node);
      delete (yyvsp[(3) - (4)].node);
    }
    break;

  case 55:
#line 573 "smtlib.y"
    {
      (yyval.str) = new std::string("_EXISTS");
    }
    break;

  case 56:
#line 577 "smtlib.y"
    {
      (yyval.str) = new std::string("_FORALL");
    }
    break;

  case 57:
#line 584 "smtlib.y"
    {
      (yyval.str) = new std::string("_NOT");
    }
    break;

  case 58:
#line 588 "smtlib.y"
    {
      (yyval.str) = new std::string("_IMPLIES");
    }
    break;

  case 59:
#line 592 "smtlib.y"
    {
      (yyval.str) = new std::string("_IF");
    }
    break;

  case 60:
#line 596 "smtlib.y"
    {
      (yyval.str) = new std::string("_AND");
    }
    break;

  case 61:
#line 600 "smtlib.y"
    {
      (yyval.str) = new std::string("_OR");
    }
    break;

  case 62:
#line 604 "smtlib.y"
    {
      (yyval.str) = new std::string("_XOR");
    }
    break;

  case 63:
#line 608 "smtlib.y"
    {
      (yyval.str) = new std::string("_IFF");
    }
    break;

  case 64:
#line 615 "smtlib.y"
    {
      (yyval.node) = (yyvsp[(1) - (1)].node);
    }
    break;

  case 65:
#line 619 "smtlib.y"
    {
      (yyval.node) = (yyvsp[(2) - (4)].node);
      delete (yyvsp[(3) - (4)].strvec);
    }
    break;

  case 66:
#line 624 "smtlib.y"
    {
      if ((yyvsp[(4) - (5)].strvec)->size() == 1 && (*(yyvsp[(4) - (5)].strvec))[0] == "transclose" &&
          (yyvsp[(3) - (5)].vec)->size() == 2) {
        (yyval.node) = new CVC3::Expr(VC->listExpr("_TRANS_CLOSURE",
                                        *(yyvsp[(2) - (5)].node), (*(yyvsp[(3) - (5)].vec))[0], (*(yyvsp[(3) - (5)].vec))[1]));
      }
      else {
        std::vector<CVC3::Expr> tmp;
        tmp.push_back(*(yyvsp[(2) - (5)].node));
        tmp.insert(tmp.end(), (yyvsp[(3) - (5)].vec)->begin(), (yyvsp[(3) - (5)].vec)->end());
        (yyval.node) = new CVC3::Expr(VC->listExpr(tmp));
      }
      delete (yyvsp[(2) - (5)].node);
      delete (yyvsp[(3) - (5)].vec);
      delete (yyvsp[(4) - (5)].strvec);
    }
    break;

  case 67:
#line 641 "smtlib.y"
    {
      std::vector<CVC3::Expr> tmp;
      tmp.push_back(*(yyvsp[(2) - (4)].node));
      tmp.insert(tmp.end(), (yyvsp[(3) - (4)].vec)->begin(), (yyvsp[(3) - (4)].vec)->end());
      (yyval.node) = new CVC3::Expr(VC->listExpr(tmp));
      delete (yyvsp[(2) - (4)].node);
      delete (yyvsp[(3) - (4)].vec);
    }
    break;

  case 68:
#line 650 "smtlib.y"
    {
      (yyval.node) = new CVC3::Expr(VC->listExpr("_DISTINCT", *(yyvsp[(3) - (5)].vec)));

//       std::vector<CVC3::Expr> tmp;
//       tmp.push_back(*$2);
//       tmp.insert(tmp.end(), $3->begin(), $3->end());
//       $$ = new CVC3::Expr(VC->listExpr(tmp));
//       for (unsigned i = 0; i < (*$3).size(); ++i) {
//         tmp.push_back(($3)[i])
// 	for (unsigned j = i+1; j < (*$3).size(); ++j) {
// 	  tmp.push_back(VC->listExpr("_NEQ", (*$3)[i], (*$3)[j]));
// 	}
//       }
//       $$ = new CVC3::Expr(VC->listExpr("_AND", tmp));
      delete (yyvsp[(3) - (5)].vec);
      delete (yyvsp[(4) - (5)].strvec);
    }
    break;

  case 69:
#line 668 "smtlib.y"
    {
      (yyval.node) = new CVC3::Expr(VC->listExpr("_DISTINCT", *(yyvsp[(3) - (4)].vec)));
//       std::vector<CVC3::Expr> tmp;
//       for (unsigned i = 0; i < (*$3).size(); ++i) {
// 	for (unsigned j = i+1; j < (*$3).size(); ++j) {
// 	  tmp.push_back(VC->listExpr("_NEQ", (*$3)[i], (*$3)[j]));
// 	}
//       }
//       $$ = new CVC3::Expr(VC->listExpr("_AND", tmp));
      delete (yyvsp[(3) - (4)].vec);
    }
    break;

  case 70:
#line 683 "smtlib.y"
    {
      (yyval.node) = new CVC3::Expr(VC->idExpr("_TRUE_EXPR"));
    }
    break;

  case 71:
#line 687 "smtlib.y"
    { 
      (yyval.node) = new CVC3::Expr(VC->idExpr("_FALSE_EXPR"));
    }
    break;

  case 72:
#line 691 "smtlib.y"
    {
      (yyval.node) = (yyvsp[(1) - (1)].node);
    }
    break;

  case 73:
#line 695 "smtlib.y"
    {
      (yyval.node) = (yyvsp[(1) - (1)].node);
    }
    break;

  case 74:
#line 702 "smtlib.y"
    {
      (yyval.vec) = new std::vector<CVC3::Expr>;
      (yyval.vec)->push_back(*(yyvsp[(1) - (1)].node));
      delete (yyvsp[(1) - (1)].node);
    }
    break;

  case 75:
#line 708 "smtlib.y"
    {
      (yyvsp[(1) - (2)].vec)->push_back(*(yyvsp[(2) - (2)].node));
      (yyval.vec) = (yyvsp[(1) - (2)].vec); 
      delete (yyvsp[(2) - (2)].node);
    }
    break;

  case 76:
#line 717 "smtlib.y"
    {
      (yyval.node) = (yyvsp[(1) - (1)].node);
    }
    break;

  case 77:
#line 721 "smtlib.y"
    {
      (yyval.node) = (yyvsp[(2) - (4)].node);
      delete (yyvsp[(3) - (4)].strvec);
    }
    break;

  case 78:
#line 726 "smtlib.y"
    {
      (yyvsp[(2) - (5)].vec)->insert((yyvsp[(2) - (5)].vec)->end(), (yyvsp[(3) - (5)].vec)->begin(), (yyvsp[(3) - (5)].vec)->end());
      (yyval.node) = new CVC3::Expr(VC->listExpr(*(yyvsp[(2) - (5)].vec)));
      delete (yyvsp[(2) - (5)].vec);
      delete (yyvsp[(3) - (5)].vec);
      delete (yyvsp[(4) - (5)].strvec);
    }
    break;

  case 79:
#line 734 "smtlib.y"
    {
      (yyvsp[(2) - (4)].vec)->insert((yyvsp[(2) - (4)].vec)->end(), (yyvsp[(3) - (4)].vec)->begin(), (yyvsp[(3) - (4)].vec)->end());
      (yyval.node) = new CVC3::Expr(VC->listExpr(*(yyvsp[(2) - (4)].vec)));
      delete (yyvsp[(2) - (4)].vec);
      delete (yyvsp[(3) - (4)].vec);
    }
    break;

  case 80:
#line 741 "smtlib.y"
    {
      (yyval.node) = new CVC3::Expr(VC->listExpr("_IF", *(yyvsp[(3) - (7)].node), *(yyvsp[(4) - (7)].node), *(yyvsp[(5) - (7)].node)));
      delete (yyvsp[(3) - (7)].node);
      delete (yyvsp[(4) - (7)].node);
      delete (yyvsp[(5) - (7)].node);
      delete (yyvsp[(6) - (7)].strvec);
    }
    break;

  case 81:
#line 749 "smtlib.y"
    {
      (yyval.node) = new CVC3::Expr(VC->listExpr("_IF", *(yyvsp[(3) - (6)].node), *(yyvsp[(4) - (6)].node), *(yyvsp[(5) - (6)].node)));
      delete (yyvsp[(3) - (6)].node);
      delete (yyvsp[(4) - (6)].node);
      delete (yyvsp[(5) - (6)].node);
    }
    break;

  case 82:
#line 756 "smtlib.y"
    {
      CVC3::Expr e(VC->listExpr(VC->listExpr(*(yyvsp[(4) - (9)].node), *(yyvsp[(5) - (9)].node))));
      (yyval.node) = new CVC3::Expr(VC->listExpr("_LET", e, *(yyvsp[(7) - (9)].node)));
      delete (yyvsp[(4) - (9)].node);
      delete (yyvsp[(5) - (9)].node);
      delete (yyvsp[(7) - (9)].node);
      delete (yyvsp[(8) - (9)].strvec);
    }
    break;

  case 83:
#line 765 "smtlib.y"
    {
      CVC3::Expr e(VC->listExpr(VC->listExpr(*(yyvsp[(4) - (8)].node), *(yyvsp[(5) - (8)].node))));
      (yyval.node) = new CVC3::Expr(VC->listExpr("_LET", e, *(yyvsp[(7) - (8)].node)));
      delete (yyvsp[(4) - (8)].node);
      delete (yyvsp[(5) - (8)].node);
      delete (yyvsp[(7) - (8)].node);
    }
    break;

  case 84:
#line 773 "smtlib.y"
    {
      CVC3::Expr e(VC->listExpr(VC->listExpr(*(yyvsp[(4) - (9)].node), *(yyvsp[(5) - (9)].node))));
      (yyval.node) = new CVC3::Expr(VC->listExpr("_LET", e, *(yyvsp[(7) - (9)].node)));
      delete (yyvsp[(4) - (9)].node);
      delete (yyvsp[(5) - (9)].node);
      delete (yyvsp[(7) - (9)].node);
      delete (yyvsp[(8) - (9)].strvec);
    }
    break;

  case 85:
#line 782 "smtlib.y"
    {
      CVC3::Expr e(VC->listExpr(VC->listExpr(*(yyvsp[(4) - (8)].node), *(yyvsp[(5) - (8)].node))));
      (yyval.node) = new CVC3::Expr(VC->listExpr("_LET", e, *(yyvsp[(7) - (8)].node)));
      delete (yyvsp[(4) - (8)].node);
      delete (yyvsp[(5) - (8)].node);
      delete (yyvsp[(7) - (8)].node);
    }
    break;

  case 86:
#line 793 "smtlib.y"
    {
      (yyval.node) = (yyvsp[(1) - (1)].node);
    }
    break;

  case 87:
#line 797 "smtlib.y"
    {
      if ((yyvsp[(1) - (1)].vec)->size() == 1) {
        (yyval.node) = new CVC3::Expr(((*(yyvsp[(1) - (1)].vec))[0]));
      }
      else {
        (yyval.node) = new CVC3::Expr(VC->listExpr(*(yyvsp[(1) - (1)].vec)));
      }
      delete (yyvsp[(1) - (1)].vec);
    }
    break;

  case 88:
#line 810 "smtlib.y"
    {
      (yyval.strvec) = new std::vector<std::string>;
      (yyval.strvec)->push_back(*(yyvsp[(1) - (1)].str));
      delete (yyvsp[(1) - (1)].str);
    }
    break;

  case 89:
#line 816 "smtlib.y"
    {
      (yyvsp[(1) - (2)].strvec)->push_back(*(yyvsp[(2) - (2)].str));
      (yyval.strvec) = (yyvsp[(1) - (2)].strvec);
      delete (yyvsp[(2) - (2)].str);
    }
    break;

  case 90:
#line 826 "smtlib.y"
    { (yyval.str) = (yyvsp[(1) - (1)].str); }
    break;

  case 91:
#line 828 "smtlib.y"
    { (yyval.str) = (yyvsp[(1) - (2)].str); }
    break;

  case 92:
#line 833 "smtlib.y"
    {
      (yyval.str) = NULL;
      delete (yyvsp[(1) - (1)].str);
    }
    break;

  case 93:
#line 842 "smtlib.y"
    {
      if (BVENABLED && *(yyvsp[(1) - (4)].str) == "BitVec") {
        (yyval.node) = new CVC3::Expr(VC->listExpr("_BITVECTOR", VC->ratExpr(*(yyvsp[(3) - (4)].str))));
      }
      else {
        (yyval.node) = new CVC3::Expr(VC->listExpr(*(yyvsp[(1) - (4)].str), VC->ratExpr(*(yyvsp[(3) - (4)].str))));
      }
      delete (yyvsp[(1) - (4)].str);
      delete (yyvsp[(3) - (4)].str);
    }
    break;

  case 94:
#line 853 "smtlib.y"
    {
      if (BVENABLED && ARRAYSENABLED && *(yyvsp[(1) - (6)].str) == "Array") {
        (yyval.node) = new CVC3::Expr(VC->listExpr("_ARRAY",
                                         VC->listExpr("_BITVECTOR", VC->ratExpr(*(yyvsp[(3) - (6)].str))),
                                         VC->listExpr("_BITVECTOR", VC->ratExpr(*(yyvsp[(5) - (6)].str)))));
      }
      else {
        (yyval.node) = new CVC3::Expr(VC->listExpr(*(yyvsp[(1) - (6)].str), VC->ratExpr(*(yyvsp[(3) - (6)].str)), VC->ratExpr(*(yyvsp[(5) - (6)].str))));
      }
      delete (yyvsp[(1) - (6)].str);
      delete (yyvsp[(3) - (6)].str);
      delete (yyvsp[(5) - (6)].str);
    }
    break;

  case 95:
#line 867 "smtlib.y"
    { 
      if (*(yyvsp[(1) - (1)].str) == "Real") {
	(yyval.node) = new CVC3::Expr(VC->idExpr("_REAL"));
      } else if (*(yyvsp[(1) - (1)].str) == "Int") {
	(yyval.node) = new CVC3::Expr(VC->idExpr("_INT"));
      } else {
	(yyval.node) = new CVC3::Expr(VC->idExpr(*(yyvsp[(1) - (1)].str)));
      }
      delete (yyvsp[(1) - (1)].str);
    }
    break;

  case 96:
#line 881 "smtlib.y"
    {
      if (BVENABLED && (*(yyvsp[(1) - (1)].str) == "bvlt" || *(yyvsp[(1) - (1)].str) == "bvult")) {
        (yyval.node) = new CVC3::Expr(VC->idExpr("_BVLT"));
      }
      else if (BVENABLED && (*(yyvsp[(1) - (1)].str) == "bvleq" || *(yyvsp[(1) - (1)].str) == "bvule")) {
        (yyval.node) = new CVC3::Expr(VC->idExpr("_BVLE"));
      }
      else if (BVENABLED && (*(yyvsp[(1) - (1)].str) == "bvgeq" || *(yyvsp[(1) - (1)].str) == "bvuge")) {
        (yyval.node) = new CVC3::Expr(VC->idExpr("_BVGE"));
      }
      else if (BVENABLED && (*(yyvsp[(1) - (1)].str) == "bvgt" || *(yyvsp[(1) - (1)].str) == "bvugt")) {
        (yyval.node) = new CVC3::Expr(VC->idExpr("_BVGT"));
      }
      else if (BVENABLED && *(yyvsp[(1) - (1)].str) == "bvslt") {
        (yyval.node) = new CVC3::Expr(VC->idExpr("_BVSLT"));
      }
      else if (BVENABLED && (*(yyvsp[(1) - (1)].str) == "bvsleq" || *(yyvsp[(1) - (1)].str) == "bvsle")) {
        (yyval.node) = new CVC3::Expr(VC->idExpr("_BVSLE"));
      }
      else if (BVENABLED && (*(yyvsp[(1) - (1)].str) == "bvsgeq" || *(yyvsp[(1) - (1)].str) == "bvsge")) {
        (yyval.node) = new CVC3::Expr(VC->idExpr("_BVSGE"));
      }
      else if (BVENABLED && *(yyvsp[(1) - (1)].str) == "bvsgt") {
        (yyval.node) = new CVC3::Expr(VC->idExpr("_BVSGT"));
      }
      else {
        (yyval.node) = new CVC3::Expr(VC->idExpr(*(yyvsp[(1) - (1)].str)));
      }
      delete (yyvsp[(1) - (1)].str);
    }
    break;

  case 97:
#line 912 "smtlib.y"
    { 
      if ((yyvsp[(1) - (1)].str)->length() == 1) {
	switch ((*(yyvsp[(1) - (1)].str))[0]) {
	  case '=': (yyval.node) = new CVC3::Expr(VC->idExpr("_EQ")); break;
	  case '<': (yyval.node) = new CVC3::Expr(VC->idExpr("_LT")); break;
	  case '>': (yyval.node) = new CVC3::Expr(VC->idExpr("_GT")); break;
	  default: (yyval.node) = new CVC3::Expr(VC->idExpr(*(yyvsp[(1) - (1)].str))); break;
	}
      }
      else {
	if (*(yyvsp[(1) - (1)].str) == "<=") {
	  (yyval.node) = new CVC3::Expr(VC->idExpr("_LE"));
	} else if (*(yyvsp[(1) - (1)].str) == ">=") {
	  (yyval.node) = new CVC3::Expr(VC->idExpr("_GE"));
	}
	else (yyval.node) = new CVC3::Expr(VC->idExpr(*(yyvsp[(1) - (1)].str)));
      }
      delete (yyvsp[(1) - (1)].str);
    }
    break;

  case 98:
#line 935 "smtlib.y"
    {
      (yyval.vec) = new std::vector<CVC3::Expr>;
      if (BVENABLED && *(yyvsp[(1) - (4)].str) == "repeat") {
        (yyval.vec)->push_back(VC->idExpr("_BVREPEAT"));
      }
      else if (BVENABLED && *(yyvsp[(1) - (4)].str) == "zero_extend") {
        (yyval.vec)->push_back(VC->idExpr("_BVZEROEXTEND"));
      }
      else if (BVENABLED && *(yyvsp[(1) - (4)].str) == "sign_extend") {
        (yyval.vec)->push_back(VC->idExpr("_SX"));
        (yyval.vec)->push_back(VC->idExpr("_smtlib"));
      }
      else if (BVENABLED && *(yyvsp[(1) - (4)].str) == "rotate_left") {
        (yyval.vec)->push_back(VC->idExpr("_BVROTL"));
      }
      else if (BVENABLED && *(yyvsp[(1) - (4)].str) == "rotate_right") {
        (yyval.vec)->push_back(VC->idExpr("_BVROTR"));
      }
      else if (BVENABLED &&
               (yyvsp[(1) - (4)].str)->size() > 2 &&
               (*(yyvsp[(1) - (4)].str))[0] == 'b' &&
               (*(yyvsp[(1) - (4)].str))[1] == 'v') {
        int i = 2;
        while ((*(yyvsp[(1) - (4)].str))[i] >= '0' && (*(yyvsp[(1) - (4)].str))[i] <= '9') ++i;
        if ((*(yyvsp[(1) - (4)].str))[i] == '\0') {
          (yyval.vec)->push_back(VC->idExpr("_BVCONST"));
          (yyval.vec)->push_back(VC->ratExpr((yyvsp[(1) - (4)].str)->substr(2), 10));
        }
        else (yyval.vec)->push_back(VC->idExpr(*(yyvsp[(1) - (4)].str)));
      }
      else (yyval.vec)->push_back(VC->idExpr(*(yyvsp[(1) - (4)].str)));
      (yyval.vec)->push_back(VC->ratExpr(*(yyvsp[(3) - (4)].str)));
      delete (yyvsp[(1) - (4)].str);
      delete (yyvsp[(3) - (4)].str);
    }
    break;

  case 99:
#line 971 "smtlib.y"
    {
      (yyval.vec) = new std::vector<CVC3::Expr>;
      if (BVENABLED && *(yyvsp[(1) - (6)].str) == "extract") {
        (yyval.vec)->push_back(VC->idExpr("_EXTRACT"));
      }
      else (yyval.vec)->push_back(VC->idExpr(*(yyvsp[(1) - (6)].str)));
      (yyval.vec)->push_back(VC->ratExpr(*(yyvsp[(3) - (6)].str)));
      (yyval.vec)->push_back(VC->ratExpr(*(yyvsp[(5) - (6)].str)));
      delete (yyvsp[(1) - (6)].str);
      delete (yyvsp[(3) - (6)].str);
      delete (yyvsp[(5) - (6)].str);
    }
    break;

  case 100:
#line 984 "smtlib.y"
    {
      (yyval.vec) = new std::vector<CVC3::Expr>;
      if (BVENABLED && (*(yyvsp[(1) - (1)].str) == "bvlt" || *(yyvsp[(1) - (1)].str) == "bvult")) {
        (yyval.vec)->push_back(VC->idExpr("_BVLT"));
      }
      else if (BVENABLED && (*(yyvsp[(1) - (1)].str) == "bvleq" || *(yyvsp[(1) - (1)].str) == "bvule")) {
        (yyval.vec)->push_back(VC->idExpr("_BVLE"));
      }
      else if (BVENABLED && (*(yyvsp[(1) - (1)].str) == "bvgeq" || *(yyvsp[(1) - (1)].str) == "bvuge")) {
        (yyval.vec)->push_back(VC->idExpr("_BVGE"));
      }
      else if (BVENABLED && (*(yyvsp[(1) - (1)].str) == "bvgt" || *(yyvsp[(1) - (1)].str) == "bvugt")) {
        (yyval.vec)->push_back(VC->idExpr("_BVGT"));
      }
      else if (BVENABLED && *(yyvsp[(1) - (1)].str) == "bvslt") {
        (yyval.vec)->push_back(VC->idExpr("_BVSLT"));
      }
      else if (BVENABLED && (*(yyvsp[(1) - (1)].str) == "bvsleq" || *(yyvsp[(1) - (1)].str) == "bvsle")) {
        (yyval.vec)->push_back(VC->idExpr("_BVSLE"));
      }
      else if (BVENABLED && (*(yyvsp[(1) - (1)].str) == "bvsgeq" || *(yyvsp[(1) - (1)].str) == "bvsge")) {
        (yyval.vec)->push_back(VC->idExpr("_BVSGE"));
      }
      else if (BVENABLED && *(yyvsp[(1) - (1)].str) == "bvsgt") {
        (yyval.vec)->push_back(VC->idExpr("_BVSGT"));
      }
      else if (ARRAYSENABLED && *(yyvsp[(1) - (1)].str) == "select") {
        (yyval.vec)->push_back(VC->idExpr("_READ"));
      }
      else if (ARRAYSENABLED && *(yyvsp[(1) - (1)].str) == "store") {
        (yyval.vec)->push_back(VC->idExpr("_WRITE"));
      }
      else if (BVENABLED && *(yyvsp[(1) - (1)].str) == "bit0") {
        (yyval.vec)->push_back(VC->idExpr("_BVCONST"));
        (yyval.vec)->push_back(VC->ratExpr(0));
        (yyval.vec)->push_back(VC->ratExpr(1));
      }
      else if (BVENABLED && *(yyvsp[(1) - (1)].str) == "bit1") {
        (yyval.vec)->push_back(VC->idExpr("_BVCONST"));
        (yyval.vec)->push_back(VC->ratExpr(1));
        (yyval.vec)->push_back(VC->ratExpr(1));
      }
      else if (BVENABLED && *(yyvsp[(1) - (1)].str) == "concat") {
        (yyval.vec)->push_back(VC->idExpr("_CONCAT"));
      }
      else if (BVENABLED && *(yyvsp[(1) - (1)].str) == "bvnot") {
        (yyval.vec)->push_back(VC->idExpr("_BVNEG"));
      }
      else if (BVENABLED && *(yyvsp[(1) - (1)].str) == "bvand") {
        (yyval.vec)->push_back(VC->idExpr("_BVAND"));
      }
      else if (BVENABLED && *(yyvsp[(1) - (1)].str) == "bvor") {
        (yyval.vec)->push_back(VC->idExpr("_BVOR"));
      }
      else if (BVENABLED && *(yyvsp[(1) - (1)].str) == "bvneg") {
        (yyval.vec)->push_back(VC->idExpr("_BVUMINUS"));
      }
      else if (BVENABLED && *(yyvsp[(1) - (1)].str) == "bvadd") {
        (yyval.vec)->push_back(VC->idExpr("_BVPLUS"));
      }
      else if (BVENABLED && *(yyvsp[(1) - (1)].str) == "bvmul") {
        (yyval.vec)->push_back(VC->idExpr("_BVMULT"));
      }
      else if (BVENABLED && *(yyvsp[(1) - (1)].str) == "bvudiv") {
        (yyval.vec)->push_back(VC->idExpr("_BVUDIV"));
      }
      else if (BVENABLED && *(yyvsp[(1) - (1)].str) == "bvurem") {
        (yyval.vec)->push_back(VC->idExpr("_BVUREM"));
      }
      else if (BVENABLED && *(yyvsp[(1) - (1)].str) == "bvshl") {
        (yyval.vec)->push_back(VC->idExpr("_BVSHL"));
      }
      else if (BVENABLED && *(yyvsp[(1) - (1)].str) == "bvlshr") {
        (yyval.vec)->push_back(VC->idExpr("_BVLSHR"));
      }

      else if (BVENABLED && *(yyvsp[(1) - (1)].str) == "bvxor") {
        (yyval.vec)->push_back(VC->idExpr("_BVXOR"));
      }
      else if (BVENABLED && *(yyvsp[(1) - (1)].str) == "bvxnor") {
        (yyval.vec)->push_back(VC->idExpr("_BVXNOR"));
      }
      else if (BVENABLED && *(yyvsp[(1) - (1)].str) == "bvcomp") {
        (yyval.vec)->push_back(VC->idExpr("_BVCOMP"));
      }

      else if (BVENABLED && *(yyvsp[(1) - (1)].str) == "bvsub") {
        (yyval.vec)->push_back(VC->idExpr("_BVSUB"));
      }
      else if (BVENABLED && *(yyvsp[(1) - (1)].str) == "bvsdiv") {
        (yyval.vec)->push_back(VC->idExpr("_BVSDIV"));
      }
      else if (BVENABLED && *(yyvsp[(1) - (1)].str) == "bvsrem") {
        (yyval.vec)->push_back(VC->idExpr("_BVSREM"));
      }
      else if (BVENABLED && *(yyvsp[(1) - (1)].str) == "bvsmod") {
        (yyval.vec)->push_back(VC->idExpr("_BVSMOD"));
      }
      else if (BVENABLED && *(yyvsp[(1) - (1)].str) == "bvashr") {
        (yyval.vec)->push_back(VC->idExpr("_BVASHR"));
      }

      // For backwards compatibility:
      else if (BVENABLED && *(yyvsp[(1) - (1)].str) == "shift_left0") {
        (yyval.vec)->push_back(VC->idExpr("_CONST_WIDTH_LEFTSHIFT"));
      }
      else if (BVENABLED && *(yyvsp[(1) - (1)].str) == "shift_right0") {
        (yyval.vec)->push_back(VC->idExpr("_RIGHTSHIFT"));
      }
      else if (BVENABLED && *(yyvsp[(1) - (1)].str) == "sign_extend") {
        (yyval.vec)->push_back(VC->idExpr("_SX"));
        (yyval.vec)->push_back(VC->idExpr("_smtlib"));
      }

      // Bitvector constants
      else if (BVENABLED &&
               (yyvsp[(1) - (1)].str)->size() > 2 &&
               (*(yyvsp[(1) - (1)].str))[0] == 'b' &&
               (*(yyvsp[(1) - (1)].str))[1] == 'v') {
        bool done = false;
        if ((*(yyvsp[(1) - (1)].str))[2] >= '0' && (*(yyvsp[(1) - (1)].str))[2] <= '9') {
          int i = 3;
          while ((*(yyvsp[(1) - (1)].str))[i] >= '0' && (*(yyvsp[(1) - (1)].str))[i] <= '9') ++i;
          if ((*(yyvsp[(1) - (1)].str))[i] == '\0') {
            (yyval.vec)->push_back(VC->idExpr("_BVCONST"));
            (yyval.vec)->push_back(VC->ratExpr((yyvsp[(1) - (1)].str)->substr(2), 10));
            (yyval.vec)->push_back(VC->ratExpr(32));
            done = true;
          }
        }
        else if ((yyvsp[(1) - (1)].str)->size() > 5) {
          std::string s = (yyvsp[(1) - (1)].str)->substr(0,5);
          if (s == "bvbin") {
            int i = 5;
            while ((*(yyvsp[(1) - (1)].str))[i] >= '0' && (*(yyvsp[(1) - (1)].str))[i] <= '1') ++i;
            if ((*(yyvsp[(1) - (1)].str))[i] == '\0') {
              (yyval.vec)->push_back(VC->idExpr("_BVCONST"));
              (yyval.vec)->push_back(VC->ratExpr((yyvsp[(1) - (1)].str)->substr(5), 2));
              (yyval.vec)->push_back(VC->ratExpr(i-5));
              done = true;
            }
          }
          else if (s == "bvhex") {
            int i = 5;
            char c = (*(yyvsp[(1) - (1)].str))[i];
            while ((c >= '0' && c <= '9') ||
                   (c >= 'a' && c <= 'f') ||
                   (c >= 'A' && c <= 'F')) {
              ++i;
              c =(*(yyvsp[(1) - (1)].str))[i];
            }
            if ((*(yyvsp[(1) - (1)].str))[i] == '\0') {
              (yyval.vec)->push_back(VC->idExpr("_BVCONST"));
              (yyval.vec)->push_back(VC->ratExpr((yyvsp[(1) - (1)].str)->substr(5), 16));
              (yyval.vec)->push_back(VC->ratExpr(i-5));
              done = true;
            }
          }
        }
        if (!done) (yyval.vec)->push_back(VC->idExpr(*(yyvsp[(1) - (1)].str)));
      }
      else {
        (yyval.vec)->push_back(VC->idExpr(*(yyvsp[(1) - (1)].str)));
      }
      delete (yyvsp[(1) - (1)].str);
    }
    break;

  case 101:
#line 1151 "smtlib.y"
    { 
      (yyval.vec) = new std::vector<CVC3::Expr>;
      if ((yyvsp[(1) - (1)].str)->length() == 1) {
	switch ((*(yyvsp[(1) - (1)].str))[0]) {
	case '+': (yyval.vec)->push_back(VC->idExpr("_PLUS")); break;
	case '-': (yyval.vec)->push_back(VC->idExpr("_MINUS")); break;
	case '*': (yyval.vec)->push_back(VC->idExpr("_MULT")); break;
	case '~': (yyval.vec)->push_back(VC->idExpr("_UMINUS")); break;
	case '/': (yyval.vec)->push_back(VC->idExpr("_DIVIDE")); break;
          //        case '=': $$->push_back(VC->idExpr("_EQ")); break;
          //        case '<': $$->push_back(VC->idExpr("_LT")); break;
          //        case '>': $$->push_back(VC->idExpr("_GT")); break;
	default: (yyval.vec)->push_back(VC->idExpr(*(yyvsp[(1) - (1)].str)));
	}
      }
      //      else {
      //	if (*$1 == "<=") {
      //	  $$->push_back(VC->idExpr("_LE"));
      //	} else if (*$1 == ">=") {
      //	  $$->push_back(VC->idExpr("_GE"));
      //	}
	else (yyval.vec)->push_back(VC->idExpr(*(yyvsp[(1) - (1)].str)));
      //      }
      delete (yyvsp[(1) - (1)].str);
    }
    break;

  case 102:
#line 1177 "smtlib.y"
    {
      (yyval.vec) = new std::vector<CVC3::Expr>;
      (yyval.vec)->push_back(VC->ratExpr(*(yyvsp[(1) - (1)].str)));
      delete (yyvsp[(1) - (1)].str);
    }
    break;

  case 103:
#line 1186 "smtlib.y"
    {
      (yyval.str) = (yyvsp[(2) - (2)].str);
    }
    break;

  case 104:
#line 1193 "smtlib.y"
    {
      (yyval.node) = new CVC3::Expr(VC->idExpr("_"+*(yyvsp[(2) - (2)].str)));
      delete (yyvsp[(2) - (2)].str);
    }
    break;

  case 105:
#line 1201 "smtlib.y"
    {
      (yyval.node) = new CVC3::Expr(VC->idExpr("_"+*(yyvsp[(2) - (2)].str)));
      delete (yyvsp[(2) - (2)].str);
    }
    break;

  case 106:
#line 1209 "smtlib.y"
    {
      (yyval.vec) = new std::vector<CVC3::Expr>;
      (yyval.vec)->push_back(*(yyvsp[(1) - (1)].node));
      delete (yyvsp[(1) - (1)].node);
    }
    break;

  case 107:
#line 1216 "smtlib.y"
    {
      (yyvsp[(1) - (2)].vec)->push_back(*(yyvsp[(2) - (2)].node));
      (yyval.vec) = (yyvsp[(1) - (2)].vec);
      delete (yyvsp[(2) - (2)].node);
    }
    break;

  case 108:
#line 1225 "smtlib.y"
    {
      (yyval.node) = (yyvsp[(1) - (1)].node);
    }
    break;

  case 109:
#line 1229 "smtlib.y"
    {
      (yyval.node) = (yyvsp[(1) - (1)].node);
    }
    break;

  case 110:
#line 1233 "smtlib.y"
    {
      (yyvsp[(2) - (5)].vec)->insert((yyvsp[(2) - (5)].vec)->end(), (yyvsp[(3) - (5)].vec)->begin(), (yyvsp[(3) - (5)].vec)->end());
      (yyval.node) = new CVC3::Expr(VC->listExpr(*(yyvsp[(2) - (5)].vec)));
      delete (yyvsp[(2) - (5)].vec);
      delete (yyvsp[(3) - (5)].vec);
      delete (yyvsp[(4) - (5)].strvec);
    }
    break;

  case 111:
#line 1241 "smtlib.y"
    {
      (yyvsp[(2) - (4)].vec)->insert((yyvsp[(2) - (4)].vec)->end(), (yyvsp[(3) - (4)].vec)->begin(), (yyvsp[(3) - (4)].vec)->end());
      (yyval.node) = new CVC3::Expr(VC->listExpr(*(yyvsp[(2) - (4)].vec)));
      delete (yyvsp[(2) - (4)].vec);
      delete (yyvsp[(3) - (4)].vec);
    }
    break;

  case 112:
#line 1248 "smtlib.y"
    {
      CVC3::Expr e(VC->listExpr(VC->listExpr(*(yyvsp[(4) - (9)].node), *(yyvsp[(5) - (9)].node))));
      (yyval.node) = new CVC3::Expr(VC->listExpr("_LET", e, *(yyvsp[(7) - (9)].node)));
      delete (yyvsp[(4) - (9)].node);
      delete (yyvsp[(5) - (9)].node);
      delete (yyvsp[(7) - (9)].node);
      delete (yyvsp[(8) - (9)].strvec);
    }
    break;

  case 113:
#line 1257 "smtlib.y"
    {
      CVC3::Expr e(VC->listExpr(VC->listExpr(*(yyvsp[(4) - (8)].node), *(yyvsp[(5) - (8)].node))));
      (yyval.node) = new CVC3::Expr(VC->listExpr("_LET", e, *(yyvsp[(7) - (8)].node)));
      delete (yyvsp[(4) - (8)].node);
      delete (yyvsp[(5) - (8)].node);
      delete (yyvsp[(7) - (8)].node);
    }
    break;

  case 114:
#line 1265 "smtlib.y"
    {
      CVC3::Expr e(VC->listExpr(VC->listExpr(*(yyvsp[(4) - (9)].node), *(yyvsp[(5) - (9)].node))));
      (yyval.node) = new CVC3::Expr(VC->listExpr("_LET", e, *(yyvsp[(7) - (9)].node)));
      delete (yyvsp[(4) - (9)].node);
      delete (yyvsp[(5) - (9)].node);
      delete (yyvsp[(7) - (9)].node);
      delete (yyvsp[(8) - (9)].strvec);
    }
    break;

  case 115:
#line 1274 "smtlib.y"
    {
      CVC3::Expr e(VC->listExpr(VC->listExpr(*(yyvsp[(4) - (8)].node), *(yyvsp[(5) - (8)].node))));
      (yyval.node) = new CVC3::Expr(VC->listExpr("_LET", e, *(yyvsp[(7) - (8)].node)));
      delete (yyvsp[(4) - (8)].node);
      delete (yyvsp[(5) - (8)].node);
      delete (yyvsp[(7) - (8)].node);
    }
    break;

  case 116:
#line 1285 "smtlib.y"
    {
      (yyval.vec) = new std::vector<CVC3::Expr>;
      if (BVENABLED && *(yyvsp[(1) - (4)].str) == "repeat") {
        (yyval.vec)->push_back(VC->idExpr("_BVREPEAT"));
      }
      else if (BVENABLED && *(yyvsp[(1) - (4)].str) == "zero_extend") {
        (yyval.vec)->push_back(VC->idExpr("_BVZEROEXTEND"));
      }
      else if (BVENABLED && *(yyvsp[(1) - (4)].str) == "sign_extend") {
        (yyval.vec)->push_back(VC->idExpr("_SX"));
        (yyval.vec)->push_back(VC->idExpr("_smtlib"));
      }
      else if (BVENABLED && *(yyvsp[(1) - (4)].str) == "rotate_left") {
        (yyval.vec)->push_back(VC->idExpr("_BVROTL"));
      }
      else if (BVENABLED && *(yyvsp[(1) - (4)].str) == "rotate_right") {
        (yyval.vec)->push_back(VC->idExpr("_BVROTR"));
      }
      else if (BVENABLED &&
               (yyvsp[(1) - (4)].str)->size() > 2 &&
               (*(yyvsp[(1) - (4)].str))[0] == 'b' &&
               (*(yyvsp[(1) - (4)].str))[1] == 'v') {
        int i = 2;
        while ((*(yyvsp[(1) - (4)].str))[i] >= '0' && (*(yyvsp[(1) - (4)].str))[i] <= '9') ++i;
        if ((*(yyvsp[(1) - (4)].str))[i] == '\0') {
          (yyval.vec)->push_back(VC->idExpr("_BVCONST"));
          (yyval.vec)->push_back(VC->ratExpr((yyvsp[(1) - (4)].str)->substr(2), 10));
        }
        else (yyval.vec)->push_back(VC->idExpr(*(yyvsp[(1) - (4)].str)));
      }
      else (yyval.vec)->push_back(VC->idExpr(*(yyvsp[(1) - (4)].str)));
      (yyval.vec)->push_back(VC->ratExpr(*(yyvsp[(3) - (4)].str)));
      delete (yyvsp[(1) - (4)].str);
      delete (yyvsp[(3) - (4)].str);
    }
    break;

  case 117:
#line 1321 "smtlib.y"
    {
      (yyval.vec) = new std::vector<CVC3::Expr>;
      if (BVENABLED && *(yyvsp[(1) - (6)].str) == "extract") {
        (yyval.vec)->push_back(VC->idExpr("_EXTRACT"));
      }
      else (yyval.vec)->push_back(VC->idExpr(*(yyvsp[(1) - (6)].str)));
      (yyval.vec)->push_back(VC->ratExpr(*(yyvsp[(3) - (6)].str)));
      (yyval.vec)->push_back(VC->ratExpr(*(yyvsp[(5) - (6)].str)));
      delete (yyvsp[(1) - (6)].str);
      delete (yyvsp[(3) - (6)].str);
      delete (yyvsp[(5) - (6)].str);
    }
    break;

  case 118:
#line 1334 "smtlib.y"
    {
      (yyval.vec) = new std::vector<CVC3::Expr>;
      if (BVENABLED && (*(yyvsp[(1) - (1)].str) == "bvlt" || *(yyvsp[(1) - (1)].str) == "bvult")) {
        (yyval.vec)->push_back(VC->idExpr("_BVLT"));
      }
      else if (BVENABLED && (*(yyvsp[(1) - (1)].str) == "bvleq" || *(yyvsp[(1) - (1)].str) == "bvule")) {
        (yyval.vec)->push_back(VC->idExpr("_BVLE"));
      }
      else if (BVENABLED && (*(yyvsp[(1) - (1)].str) == "bvgeq" || *(yyvsp[(1) - (1)].str) == "bvuge")) {
        (yyval.vec)->push_back(VC->idExpr("_BVGE"));
      }
      else if (BVENABLED && (*(yyvsp[(1) - (1)].str) == "bvgt" || *(yyvsp[(1) - (1)].str) == "bvugt")) {
        (yyval.vec)->push_back(VC->idExpr("_BVGT"));
      }
      else if (BVENABLED && *(yyvsp[(1) - (1)].str) == "bvslt") {
        (yyval.vec)->push_back(VC->idExpr("_BVSLT"));
      }
      else if (BVENABLED && (*(yyvsp[(1) - (1)].str) == "bvsleq" || *(yyvsp[(1) - (1)].str) == "bvsle")) {
        (yyval.vec)->push_back(VC->idExpr("_BVSLE"));
      }
      else if (BVENABLED && (*(yyvsp[(1) - (1)].str) == "bvsgeq" || *(yyvsp[(1) - (1)].str) == "bvsge")) {
        (yyval.vec)->push_back(VC->idExpr("_BVSGE"));
      }
      else if (BVENABLED && *(yyvsp[(1) - (1)].str) == "bvsgt") {
        (yyval.vec)->push_back(VC->idExpr("_BVSGT"));
      }
      else if (ARRAYSENABLED && *(yyvsp[(1) - (1)].str) == "select") {
        (yyval.vec)->push_back(VC->idExpr("_READ"));
      }
      else if (ARRAYSENABLED && *(yyvsp[(1) - (1)].str) == "store") {
        (yyval.vec)->push_back(VC->idExpr("_WRITE"));
      }
      else if (BVENABLED && *(yyvsp[(1) - (1)].str) == "bit0") {
        (yyval.vec)->push_back(VC->idExpr("_BVCONST"));
        (yyval.vec)->push_back(VC->ratExpr(0));
        (yyval.vec)->push_back(VC->ratExpr(1));
      }
      else if (BVENABLED && *(yyvsp[(1) - (1)].str) == "bit1") {
        (yyval.vec)->push_back(VC->idExpr("_BVCONST"));
        (yyval.vec)->push_back(VC->ratExpr(1));
        (yyval.vec)->push_back(VC->ratExpr(1));
      }
      else if (BVENABLED && *(yyvsp[(1) - (1)].str) == "concat") {
        (yyval.vec)->push_back(VC->idExpr("_CONCAT"));
      }
      else if (BVENABLED && *(yyvsp[(1) - (1)].str) == "bvnot") {
        (yyval.vec)->push_back(VC->idExpr("_BVNEG"));
      }
      else if (BVENABLED && *(yyvsp[(1) - (1)].str) == "bvand") {
        (yyval.vec)->push_back(VC->idExpr("_BVAND"));
      }
      else if (BVENABLED && *(yyvsp[(1) - (1)].str) == "bvor") {
        (yyval.vec)->push_back(VC->idExpr("_BVOR"));
      }
      else if (BVENABLED && *(yyvsp[(1) - (1)].str) == "bvneg") {
        (yyval.vec)->push_back(VC->idExpr("_BVUMINUS"));
      }
      else if (BVENABLED && *(yyvsp[(1) - (1)].str) == "bvadd") {
        (yyval.vec)->push_back(VC->idExpr("_BVPLUS"));
      }
      else if (BVENABLED && *(yyvsp[(1) - (1)].str) == "bvmul") {
        (yyval.vec)->push_back(VC->idExpr("_BVMULT"));
      }
      else if (BVENABLED && *(yyvsp[(1) - (1)].str) == "bvudiv") {
        (yyval.vec)->push_back(VC->idExpr("_BVUDIV"));
      }
      else if (BVENABLED && *(yyvsp[(1) - (1)].str) == "bvurem") {
        (yyval.vec)->push_back(VC->idExpr("_BVUREM"));
      }
      else if (BVENABLED && *(yyvsp[(1) - (1)].str) == "bvshl") {
        (yyval.vec)->push_back(VC->idExpr("_BVSHL"));
      }
      else if (BVENABLED && *(yyvsp[(1) - (1)].str) == "bvlshr") {
        (yyval.vec)->push_back(VC->idExpr("_BVLSHR"));
      }

      else if (BVENABLED && *(yyvsp[(1) - (1)].str) == "bvxor") {
        (yyval.vec)->push_back(VC->idExpr("_BVXOR"));
      }
      else if (BVENABLED && *(yyvsp[(1) - (1)].str) == "bvxnor") {
        (yyval.vec)->push_back(VC->idExpr("_BVXNOR"));
      }
      else if (BVENABLED && *(yyvsp[(1) - (1)].str) == "bvcomp") {
        (yyval.vec)->push_back(VC->idExpr("_BVCOMP"));
      }

      else if (BVENABLED && *(yyvsp[(1) - (1)].str) == "bvsub") {
        (yyval.vec)->push_back(VC->idExpr("_BVSUB"));
      }
      else if (BVENABLED && *(yyvsp[(1) - (1)].str) == "bvsdiv") {
        (yyval.vec)->push_back(VC->idExpr("_BVSDIV"));
      }
      else if (BVENABLED && *(yyvsp[(1) - (1)].str) == "bvsrem") {
        (yyval.vec)->push_back(VC->idExpr("_BVSREM"));
      }
      else if (BVENABLED && *(yyvsp[(1) - (1)].str) == "bvsmod") {
        (yyval.vec)->push_back(VC->idExpr("_BVSMOD"));
      }
      else if (BVENABLED && *(yyvsp[(1) - (1)].str) == "bvashr") {
        (yyval.vec)->push_back(VC->idExpr("_BVASHR"));
      }

      // predicates
      else if (BVENABLED && (*(yyvsp[(1) - (1)].str) == "bvlt" || *(yyvsp[(1) - (1)].str) == "bvult")) {
        (yyval.vec)->push_back(VC->idExpr("_BVLT"));
      }
      else if (BVENABLED && (*(yyvsp[(1) - (1)].str) == "bvleq" || *(yyvsp[(1) - (1)].str) == "bvule")) {
        (yyval.vec)->push_back(VC->idExpr("_BVLE"));
      }
      else if (BVENABLED && (*(yyvsp[(1) - (1)].str) == "bvgeq" || *(yyvsp[(1) - (1)].str) == "bvuge")) {
        (yyval.vec)->push_back(VC->idExpr("_BVGE"));
      }
      else if (BVENABLED && (*(yyvsp[(1) - (1)].str) == "bvgt" || *(yyvsp[(1) - (1)].str) == "bvugt")) {
        (yyval.vec)->push_back(VC->idExpr("_BVGT"));
      }
      else if (BVENABLED && *(yyvsp[(1) - (1)].str) == "bvslt") {
        (yyval.vec)->push_back(VC->idExpr("_BVSLT"));
      }
      else if (BVENABLED && (*(yyvsp[(1) - (1)].str) == "bvsleq" || *(yyvsp[(1) - (1)].str) == "bvsle")) {
        (yyval.vec)->push_back(VC->idExpr("_BVSLE"));
      }
      else if (BVENABLED && (*(yyvsp[(1) - (1)].str) == "bvsgeq" || *(yyvsp[(1) - (1)].str) == "bvsge")) {
        (yyval.vec)->push_back(VC->idExpr("_BVSGE"));
      }
      else if (BVENABLED && *(yyvsp[(1) - (1)].str) == "bvsgt") {
        (yyval.vec)->push_back(VC->idExpr("_BVSGT"));
      }

      // For backwards compatibility:
      else if (BVENABLED && *(yyvsp[(1) - (1)].str) == "shift_left0") {
        (yyval.vec)->push_back(VC->idExpr("_CONST_WIDTH_LEFTSHIFT"));
      }
      else if (BVENABLED && *(yyvsp[(1) - (1)].str) == "shift_right0") {
        (yyval.vec)->push_back(VC->idExpr("_RIGHTSHIFT"));
      }
      else if (BVENABLED && *(yyvsp[(1) - (1)].str) == "sign_extend") {
        (yyval.vec)->push_back(VC->idExpr("_SX"));
        (yyval.vec)->push_back(VC->idExpr("_smtlib"));
      }

      // Bitvector constants
      else if (BVENABLED &&
               (yyvsp[(1) - (1)].str)->size() > 2 &&
               (*(yyvsp[(1) - (1)].str))[0] == 'b' &&
               (*(yyvsp[(1) - (1)].str))[1] == 'v') {
        bool done = false;
        if ((*(yyvsp[(1) - (1)].str))[2] >= '0' && (*(yyvsp[(1) - (1)].str))[2] <= '9') {
          int i = 3;
          while ((*(yyvsp[(1) - (1)].str))[i] >= '0' && (*(yyvsp[(1) - (1)].str))[i] <= '9') ++i;
          if ((*(yyvsp[(1) - (1)].str))[i] == '\0') {
            (yyval.vec)->push_back(VC->idExpr("_BVCONST"));
            (yyval.vec)->push_back(VC->ratExpr((yyvsp[(1) - (1)].str)->substr(2), 10));
            (yyval.vec)->push_back(VC->ratExpr(32));
            done = true;
          }
        }
        else if ((yyvsp[(1) - (1)].str)->size() > 5) {
          std::string s = (yyvsp[(1) - (1)].str)->substr(0,5);
          if (s == "bvbin") {
            int i = 5;
            while ((*(yyvsp[(1) - (1)].str))[i] >= '0' && (*(yyvsp[(1) - (1)].str))[i] <= '1') ++i;
            if ((*(yyvsp[(1) - (1)].str))[i] == '\0') {
              (yyval.vec)->push_back(VC->idExpr("_BVCONST"));
              (yyval.vec)->push_back(VC->ratExpr((yyvsp[(1) - (1)].str)->substr(5), 2));
              (yyval.vec)->push_back(VC->ratExpr(i-5));
              done = true;
            }
          }
          else if (s == "bvhex") {
            int i = 5;
            char c = (*(yyvsp[(1) - (1)].str))[i];
            while ((c >= '0' && c <= '9') ||
                   (c >= 'a' && c <= 'f') ||
                   (c >= 'A' && c <= 'F')) {
              ++i;
              c =(*(yyvsp[(1) - (1)].str))[i];
            }
            if ((*(yyvsp[(1) - (1)].str))[i] == '\0') {
              (yyval.vec)->push_back(VC->idExpr("_BVCONST"));
              (yyval.vec)->push_back(VC->ratExpr((yyvsp[(1) - (1)].str)->substr(5), 16));
              (yyval.vec)->push_back(VC->ratExpr(i-5));
              done = true;
            }
          }
        }
        if (!done) (yyval.vec)->push_back(VC->idExpr(*(yyvsp[(1) - (1)].str)));
      }
      else {
        (yyval.vec)->push_back(VC->idExpr(*(yyvsp[(1) - (1)].str)));
      }
      delete (yyvsp[(1) - (1)].str);
    }
    break;

  case 119:
#line 1527 "smtlib.y"
    { 
      (yyval.vec) = new std::vector<CVC3::Expr>;
      if ((yyvsp[(1) - (1)].str)->length() == 1) {
	switch ((*(yyvsp[(1) - (1)].str))[0]) {
	case '+': (yyval.vec)->push_back(VC->idExpr("_PLUS")); break;
	case '-': (yyval.vec)->push_back(VC->idExpr("_MINUS")); break;
	case '*': (yyval.vec)->push_back(VC->idExpr("_MULT")); break;
	case '~': (yyval.vec)->push_back(VC->idExpr("_UMINUS")); break;
	case '/': (yyval.vec)->push_back(VC->idExpr("_DIVIDE")); break;
        case '=': (yyval.vec)->push_back(VC->idExpr("_EQ")); break;
        case '<': (yyval.vec)->push_back(VC->idExpr("_LT")); break;
        case '>': (yyval.vec)->push_back(VC->idExpr("_GT")); break;
	default: (yyval.vec)->push_back(VC->idExpr(*(yyvsp[(1) - (1)].str)));
	}
      }
      else {
	if (*(yyvsp[(1) - (1)].str) == "<=") {
	  (yyval.vec)->push_back(VC->idExpr("_LE"));
	} else if (*(yyvsp[(1) - (1)].str) == ">=") {
	  (yyval.vec)->push_back(VC->idExpr("_GE"));
	}
	else (yyval.vec)->push_back(VC->idExpr(*(yyvsp[(1) - (1)].str)));
      }
      delete (yyvsp[(1) - (1)].str);
    }
    break;

  case 120:
#line 1553 "smtlib.y"
    {
      (yyval.vec) = new std::vector<CVC3::Expr>;
      (yyval.vec)->push_back(VC->ratExpr(*(yyvsp[(1) - (1)].str)));
      delete (yyvsp[(1) - (1)].str);
    }
    break;


/* Line 1267 of yacc.c.  */
#line 3388 "parsesmtlib.cpp"
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


#line 1562 "smtlib.y"


