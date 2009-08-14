// $ANTLR 2.7.4: "java.print.g" -> "JavaPrinter.java"$

/*
 * JParse: a freely available Java parser
 * Copyright (C) 2000,2004 Jeremiah W. James
 *
 * This library is free software; you can redistribute it and/or modify it
 * under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation; either version 2.1 of the License, or (at
 * your option) any later version.
 *
 * This library is distributed in the hope that it will be useful, but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE.  See the GNU Lesser General Public
 * License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with this library; if not, write to the Free Software Foundation,
 * Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
 *
 * Author: Jerry James
 * Email: james@eecs.ku.edu, james@ittc.ku.edu, jamesj@acm.org
 * Address: EECS Department - University of Kansas
 *          Eaton Hall
 *          1520 W 15th St, Room 2001
 *          Lawrence, KS  66045-7621
 */
package test;

import antlr.CommonHiddenStreamToken;
import java.io.OutputStreamWriter;
import java.io.IOException;
import jparse.*;

public interface JavaPrinterTokenTypes {
	int EOF = 1;
	int NULL_TREE_LOOKAHEAD = 3;
	int FILE = 4;
	int VARIABLE_DEFS = 5;
	int MODIFIERS = 6;
	int ARRAY_DECLARATOR = 7;
	int TYPE = 8;
	int EXTENDS_CLAUSE = 9;
	int OBJBLOCK = 10;
	int IMPLEMENTS_CLAUSE = 11;
	int CTOR_DEF = 12;
	int METHOD_DEF = 13;
	int INSTANCE_INIT = 14;
	int VARIABLE_DEF = 15;
	int ARRAY_INIT = 16;
	int PARAMETERS = 17;
	int PARAMETER_DEF = 18;
	int SLIST = 19;
	int TYPE_STAT = 20;
	int EXPRESSION_STAT = 21;
	int LABELED_STAT = 22;
	int EMPTY_STAT = 23;
	int CASE_GROUP = 24;
	int FOR_INIT = 25;
	int FOR_CONDITION = 26;
	int FOR_ITERATOR = 27;
	int ELIST = 28;
	int CONCAT_ASSIGN = 29;
	int CONCATENATION = 30;
	int UNARY_MINUS = 31;
	int UNARY_PLUS = 32;
	int TYPECAST = 33;
	int INDEX_OP = 34;
	int METHOD_CALL = 35;
	int CONSTRUCTOR_CALL = 36;
	int POST_INC = 37;
	int POST_DEC = 38;
	int PAREN_EXPR = 39;
	int LITERAL_package = 40;
	int SEMI = 41;
	int LITERAL_import = 42;
	int IDENT = 43;
	int DOT = 44;
	int STAR = 45;
	int LITERAL_public = 46;
	int LITERAL_private = 47;
	int LITERAL_protected = 48;
	int LITERAL_static = 49;
	int LITERAL_final = 50;
	int LITERAL_synchronized = 51;
	int LITERAL_volatile = 52;
	int LITERAL_transient = 53;
	int LITERAL_native = 54;
	int LITERAL_abstract = 55;
	int LITERAL_strictfp = 56;
	int LITERAL_class = 57;
	int LITERAL_extends = 58;
	int LITERAL_implements = 59;
	int COMMA = 60;
	int LITERAL_interface = 61;
	int LCURLY = 62;
	int RCURLY = 63;
	int LPAREN = 64;
	int RPAREN = 65;
	int LITERAL_throws = 66;
	int LBRACK = 67;
	int RBRACK = 68;
	int LITERAL_void = 69;
	int LITERAL_boolean = 70;
	int LITERAL_byte = 71;
	int LITERAL_char = 72;
	int LITERAL_short = 73;
	int LITERAL_int = 74;
	int LITERAL_float = 75;
	int LITERAL_long = 76;
	int LITERAL_double = 77;
	int ASSIGN = 78;
	int COLON = 79;
	int LITERAL_if = 80;
	int LITERAL_else = 81;
	int LITERAL_for = 82;
	int LITERAL_while = 83;
	int LITERAL_do = 84;
	int LITERAL_break = 85;
	int LITERAL_continue = 86;
	int LITERAL_return = 87;
	int LITERAL_switch = 88;
	int LITERAL_throw = 89;
	int LITERAL_assert = 90;
	int LITERAL_case = 91;
	int LITERAL_default = 92;
	int LITERAL_try = 93;
	int LITERAL_finally = 94;
	int LITERAL_catch = 95;
	int PLUS_ASSIGN = 96;
	int MINUS_ASSIGN = 97;
	int STAR_ASSIGN = 98;
	int DIV_ASSIGN = 99;
	int MOD_ASSIGN = 100;
	int SR_ASSIGN = 101;
	int BSR_ASSIGN = 102;
	int SL_ASSIGN = 103;
	int BAND_ASSIGN = 104;
	int BXOR_ASSIGN = 105;
	int BOR_ASSIGN = 106;
	int QUESTION = 107;
	int LOR = 108;
	int LAND = 109;
	int BOR = 110;
	int BXOR = 111;
	int BAND = 112;
	int NOT_EQUAL = 113;
	int EQUAL = 114;
	int LT = 115;
	int GT = 116;
	int LE = 117;
	int GE = 118;
	int LITERAL_instanceof = 119;
	int SL = 120;
	int SR = 121;
	int BSR = 122;
	int PLUS = 123;
	int MINUS = 124;
	int DIV = 125;
	int MOD = 126;
	int INC = 127;
	int DEC = 128;
	int BNOT = 129;
	int LNOT = 130;
	int LITERAL_this = 131;
	int LITERAL_super = 132;
	int LITERAL_true = 133;
	int LITERAL_false = 134;
	int LITERAL_null = 135;
	int LITERAL_new = 136;
	int NUM_INT = 137;
	int CHAR_LITERAL = 138;
	int STRING_LITERAL = 139;
	int NUM_FLOAT = 140;
	int CONST = 141;
	int GOTO = 142;
	int WS = 143;
	int SL_COMMENT = 144;
	int ML_COMMENT = 145;
	int ESC = 146;
	int HEX_DIGIT = 147;
	int EXPONENT = 148;
	int FLOAT_SUFFIX = 149;
}
