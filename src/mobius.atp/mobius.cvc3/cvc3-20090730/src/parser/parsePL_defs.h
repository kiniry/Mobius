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




#if ! defined YYSTYPE && ! defined YYSTYPE_IS_DECLARED
typedef union YYSTYPE
#line 179 "PL.y"
{
  std::string *str;
  CVC3::Expr *node;
  std::vector<CVC3::Expr> *vec;
  int kind;
}
/* Line 1489 of yacc.c.  */
#line 348 "parsePL.hpp"
	YYSTYPE;
# define yystype YYSTYPE /* obsolescent; will be withdrawn */
# define YYSTYPE_IS_DECLARED 1
# define YYSTYPE_IS_TRIVIAL 1
#endif

extern YYSTYPE PLlval;

