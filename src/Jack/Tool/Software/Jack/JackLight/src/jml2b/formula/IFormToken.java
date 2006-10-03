//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: FormToken.java
/*
/*******************************************************************************
/* Warnings/Remarks:
/*  09/26/2003 : Simplify integration achieved
/******************************************************************************/
package jml2b.formula;

/**
 * This interface defines the token associated to formulas corresponding to
 * operators.
 * Those token come from Java token (<code>Ja_xxx</code>), Jml token
 * (<code>Jm_xxx</code>) or B token (<code>B_xxx</code>).
 * A priority is associated to each operator.
 * @author L. Burdy
 */

public interface IFormToken {

	/**
	 * Additive binary operator <code>a + b</code> with priority 180.
	 **/
	static final byte Ja_ADD_OP = 0;

	/**
	 * Equality binary operator <code>a == b</code> with priority 50.
	 **/
	static final byte Ja_EQUALS_OP = 1;

	/**
	 * Conjonction binary operator <code>a && b</code> with priority 40.
	 **/
	static final byte Ja_AND_OP = 2;

	/**
	 * Multiplicative binary operator <code>a * b</code> with priority 190.
	 **/
	static final byte Ja_MUL_OP = 3;

	/**
	 * Less or equal binary operator <code>a <= b</code> with priority 50.
	 **/
	static final byte Ja_LE_OP = 4;

	/**
	 * Unary minus operator <code>-a</code> with priority 210.
	 **/
	static final byte Ja_UNARY_NUMERIC_OP = 5;

	/**
	 * Identifier <code>a</code> with priority 250.
	 **/
	static final byte Ja_IDENT = 6;

	/**
	 * Comma binary operator <code>a , b</code> with priority 70.
	 **/
	static final byte Ja_COMMA = 7;

	/**
	 * Literal <code>this</code> with priority 250.
	 **/
	static final byte Ja_LITERAL_this = 8;

	/**
	 * Modulo binary operator <code>a mod b</code> with priority 190.
	 **/
	static final byte Ja_MOD = 9;

	/**
	 * Negation unary operator <code>!a</code> with priority 250.
	 **/
	static final byte Ja_LNOT = 10;

	/**
	 * Literal <code>true</code> with priority 250.
	 **/
	static final byte Ja_LITERAL_true = 11;

	/**
	 * Literal <code>false</code> with priority 250.
	 **/
	static final byte Ja_LITERAL_false = 12;

	/**
	 * Literal <code>null</code> with priority 250.
	 **/
	static final byte Ja_LITERAL_null = 13;

	/**
	 * Integer literal with priority 250.
	 **/
	static final byte Ja_NUM_INT = 14;

	/**
	 * Character literal with priority 250.
	 **/
	static final byte Ja_CHAR_LITERAL = 15;

	/**
	 * Java builtin type with priority 250.
	 **/
	static final byte Ja_JAVA_BUILTIN_TYPE = 16;

	/**
	 * Literal <code>super</code> with priority 250.
	 **/
	static final byte Ja_LITERAL_super = 17;

	/**
	 * String literal <code>"aaa"</code> with priority 250.
	 **/
	static final byte Ja_STRING_LITERAL = 18;

	/**
	 * Minus binary operator <code>a - b</code> with priority 180.
	 **/
	static final byte Ja_NEGATIVE_OP = 19;

	/**
	 * Disjonctive binary operator <code>a || b</code> with priority 40.
	 **/
	static final byte Ja_OR_OP = 20;

	/**
	 * Different binary operator <code>a != b</code> with priority 50.
	 **/
	static final byte Ja_DIFFERENT_OP = 21;

	/**
	 * Strictly less binary operator <code>a < b</code> with priority 50.
	 **/
	static final byte Ja_LESS_OP = 22;

	/**
	 * Greater or equal binary operator <code>a >= b</code> with priority 50.
	 **/
	static final byte Ja_GE_OP = 23;

	/**
	 * Strictly greater binary operator <code>a > b</code> with priority 50.
	 **/
	static final byte Ja_GREATER_OP = 24;

	/**
	 * Division binary operator <code>a / b</code> with priority 190.
	 **/
	static final byte Ja_DIV_OP = 25;

	/**
	 * Question tri-ary operator <code>a ? b : c</code> with priority 90.
	 **/
	static final byte Ja_QUESTION = 26;

	/**
	 * JML literal <code>\result</code> with priority 250.
	 **/
	static final byte Jm_T_RESULT = 27;

	/**
	 * JML Implication binary operator <code>a ==> b</code> with priority 30.
	 **/
	static final byte Jm_IMPLICATION_OP = 28;

	/**
	 * JML old unary operator <code>\old(a)</code> with priority 250.
	 **/
	static final byte Jm_T_OLD = 29;

	/**
	 * JML type unary operator <code>\type(a)</code> with priority 250.
	 **/
	static final byte Jm_T_TYPE = 30;

	/**
	 * JML subtype binary operator <code>a <: b</code> with priority 250.
	 **/
	static final byte Jm_IS_SUBTYPE = 31;

	/**
	 * B literal btrue <code>0=0</code> with priority 250.
	 **/
	static final byte B_BTRUE = 32;

	/**
	 * B bracket unary operator <code>{a}</code> with priority 250.
	 **/
	static final byte B_ACCOLADE = 33;

	/**
	 * B overriding binary operator <code>a <+ b</code> with priority 90.
	 **/
	static final byte B_OVERRIDING = 34;

	/**
	 * B union binary operator <code>a \/ b</code> with priority 140.
	 **/
	static final byte B_UNION = 35;

	/**
	 * B universal quantification operator <code>!a.b</code> with priority 250.
	 **/
	static final byte Jm_FORALL = 36;

	/**
	 * constant function <code>a * {b}</code> with priority 200.
	 **/
	static final byte CONSTANT_FUNCTION = 37;

	/**
	 * B total injection binary operator <code>a >-> b</code> with priority 120.
	 **/
	static final byte IS_ARRAY = 38;

	/**
	 * B interval binary operator <code>a .. b</code> with priority 170.
	 **/
	static final byte B_INTERVAL = 39;

	/**
	 * B application binary operator <code>a(b)</code> with priority 250
	 **/
	static final byte B_APPLICATION = 41;

	/**
	 * B belongs to binary operator <code>a : b</code> with priority 60
	 **/
	static final byte B_IN = 42;

	/**
	 * B boolean unary operator <code>bool(a)</code> with priority 250
	 **/
	static final byte B_BOOL = 43;

	/**
	 * B couple binary operator <code>a |-> b</code> with priority 250.
	 **/
	static final byte B_COUPLE = 44;

	/**
	 * B partial function binary operator <code>a +-> b</code> with priority 120.
	 **/
	static final byte IS_MEMBER_FIELD = 45;

	/**
	 * B existential quantifier operator <code>#a.b</code> with priority 250.
	 **/
	static final byte Jm_EXISTS = 46;

	/**
	 * Domain restriction equality operator <code>a <| b == a <| c</code> with 
	 * priority 50.
	 **/
	static final byte EQUALS_ON_OLD_INSTANCES = 47;

	/**
	 * Constant identifier with priority 250.
	 **/
	static final byte FINAL_IDENT = 48;

	/**
	 * Called old operator with priority 250.
	 **/
	static final byte T_CALLED_OLD = 49;

	/**
	 * Local variable declaration corresponding formally to a B_IN
	 **/
	static final byte LOCAL_VAR_DECL = 50;

	/**
	 * Set guarded by a condition
	 **/
	static final byte GUARDED_SET = 51;

	/**
	 * B intersection binary operator <code>a /\ b /= {}</code> with priority 160.
	 **/
	static final byte INTERSECTION_IS_NOT_EMPTY = 52;

	/**
	 * array range <code>UNION(x).(x : a | b[c])</code> with priority 250.
	 **/
	static final byte ARRAY_RANGE = 53;

	/**
	 * B domaine function with priority 250
	 **/
	static final byte B_DOM = 54;

	/**
	 * B set equality operator with priority 50.
	 **/
	static final byte B_SET_EQUALS = 55;

	/**
	 * B substraction dom operator with priority 40.
	 **/	//TO V?rif
	static final byte B_SUBSTRACTION_DOM = 56;

	/**
	 * B function equality operator with priority 50.
	 **/
	static final byte B_FUNCTION_EQUALS = 57;

	/**
	 * constant function function <code>a * {b * {c}}</code> with priority 200.
	 **/
	static final byte CONSTANT_FUNCTION_FUNCTION = 58;

	/**
	 * identifier corresponding to a modified field.
	 **/
	static final byte MODIFIED_FIELD = 59;
	
	static final byte T_VARIANT_OLD = 60;
	
	static final byte NEW_OBJECT = 61;

	/**
	 * Domain restriction equality operator <code>a <| b == a <| c</code> with 
	 * priority 50.
	 **/
	static final byte EQUALS_ON_OLD_INSTANCES_ARRAY = 62;
	
	static final byte T_TYPE = 63;

	static final byte IS_STATIC_FIELD = 64;
	
	static final byte ARRAY_ACCESS = 65;
	
	static final byte Jm_AND_THEN = 66;
	
	static final byte Jm_OR_ELSE = 67;

	/**
	 * B function equality operator with priority 50.
	 **/
	static final byte B_ARRAY_EQUALS = 68;

	/**
	 * Local xxxelements declaration corresponding formally to a B_IN
	 **/
	static final byte LOCAL_ELEMENTS_DECL = 69;
	
	/**
	 * All array elements corresping to a[*].
	 **/
	static final byte ALL_ARRAY_ELEMS = 70;

	static final byte METHOD_CALL = 71;

	static final byte DECL_PURE_METHOD = 72;
	/**
	 * Array given token name for the error displaying.
	 **/
	static final String[] toString =
		{
			"Ja_ADD_OP",
			"Ja_EQUALS_OP",
			"Ja_AND_OP",
			"Ja_MUL_OP",
			"Ja_LE_OP",
			"Ja_UNARY_NUMERIC_OP",
			"Ja_IDENT",
			"Ja_COMMA",
			"Ja_LITERAL_this",
			"Ja_MOD",
			"Ja_LNOT",
			"Ja_LITERAL_true",
			"Ja_LITERAL_false",
			"Ja_LITERAL_null",
			"Ja_NUM_INT",
			"Ja_CHAR_LITERAL",
			"Ja_JAVA_BUILTIN_TYPE",
			"Ja_LITERAL_super",
			"Ja_STRING_LITERAL",
			"Ja_NEGATIVE_OP",
			"Ja_OR_OP",
			"Ja_DIFFERENT_OP",
			"Ja_LESS_OP",
			"Ja_GE_OP",
			"Ja_GREATER_OP",
			"Ja_DIV_OP",
			"Ja_QUESTION",
			"Jm_T_RESULT",
			"Jm_IMPLICATION_OP",
			"Jm_T_OLD",
			"Jm_T_TYPE",
			"Jm_IS_SUBTYPE",
			"B_BTRUE",
			"B_ACCOLADE",
			"B_OVERRIDING",
			"B_UNION",
			"B_FORALL",
			"B_POWER",
			"IS_ARRAY",
			"B_INTERVAL",
			"B_EMPTYSET",
			"B_APPLICATION",
			"B_IN",
			"B_BOOL",
			"B_COUPLE",
			"IS_MEMBER_FIELD",
			"Jm_EXISTS",
			"EQUALS_RESTRICT_DOM",
			"FINAL_IDENT",
			"T_CALLED_OLD",
			"AS_TYPE",
			"GUARDED_SET",
			"INTERSECTION_IS_NOT_EMPTY",
			"B_UNION_Q",
			"B_DOM",
			"B_SET_EQUALS",
			"B_SUBSTRACTION_DOM",
			"B_FUNCTION_EQUALS",
			"CONSTANT_FUNCTION_FUNCTION",
			"MODIFIED_FIELD",
			"T_VARIANT_OLD",
			"NEW_OBJECT",
			"EQUALS_ON_OLD_INSTANCES",
			"T_TYPE",
			"IS_STATIC_FIELD",
			"ARRAY_ACCESS",
			"Jm_AND_THEN",
			"Jm_OR_ELSE",
			"B_ARRAY_EQUALS",
			"LOCAL_ELEMENTS_DECL",
			"ALL_ARRAY_ELEMS",
			"METHOD_CALL",
			"DECL_PURE_METHOD"};

}