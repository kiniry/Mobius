header {
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
}

/**
 * A Java 1.2 tree walker that prints out the parsed tree, exactly as it was
 * read in.  This tree walker is based on, but differs significantly from, the
 * public domain ANTLR tree walker identified as follows:
 *
 * Java 1.2 AST Recognizer Grammar
 *
 * Author:
 *     Terence Parr    parrt@jguru.com
 *
 * Version tracking now done with following ID:
 *
 * $Id: java.print.g,v 1.5 2004/07/08 18:29:01 james Exp $
 *
 * This grammar is in the PUBLIC DOMAIN
 *
 * BUGS
 */
class JavaPrinter extends TreeParser;

options {
	ASTLabelType = "JavaAST";		// Change the default AST node type
	k = 2;
	importVocab = Java;
}

{
	/**
	 * Where to send the output of the tree walker
	 */
	protected OutputStreamWriter out;
}

compilationUnit[OutputStreamWriter output]
	:	{ out = output; }
		#(FILE { #FILE.print(output); }
			(packageDefinition)?
			(importDefinition)*
			(typeDefinition)*
		)
		{ try {output.flush();} catch (IOException ioEx) { /* ignored */ } }
	;

packageDefinition
	:	#( p:"package" {#p.print(out);} identifier SEMI {#SEMI.print(out);} )
	;

importDefinition
	:	#( i:"import" {#i.print(out);} identifierStar SEMI {#SEMI.print(out);})
	;

typeDefinition
	:	#(cl:"class" modifiers id1:IDENT {#cl.print(out); #id1.print(out);}
			(extendsClause)? (implementsClause)? objBlock)
	|	#(in:"interface" modifiers id2:IDENT {#in.print(out); #id2.print(out);}
			(extendsClause)? interfaceBlock )
	|	SEMI {#SEMI.print(out);}
	;

typeSpec
	:	#(TYPE typeSpecArray)
	;

typeSpecArray
	:	#( ARRAY_DECLARATOR (typeSpecArray)? RBRACK
			{ #ARRAY_DECLARATOR.print(out); #RBRACK.print(out); } )
	|	type
	;

type
	:	identifier
	|	builtInType
	;

builtInType
    :   v:"void"	{#v.print(out);}
    |   b:"boolean"	{#b.print(out);}
    |   y:"byte"	{#y.print(out);}
    |   c:"char"	{#c.print(out);}
    |   s:"short"	{#s.print(out);}
    |   i:"int"		{#i.print(out);}
    |   f:"float"	{#f.print(out);}
    |   l:"long"	{#l.print(out);}
    |   d:"double"	{#d.print(out);}
    ;

modifiers
	:	#( MODIFIERS (modifier)* )
	;

modifier
    :   u:"public"			{#u.print(out);}
    |   p:"private"			{#p.print(out);}
    |   r:"protected"		{#r.print(out);}
    |   s:"static"			{#s.print(out);}
    |   f:"final"			{#f.print(out);}
    |   y:"synchronized"	{#y.print(out);}
    |   v:"volatile"		{#v.print(out);}
    |   t:"transient"		{#t.print(out);}
    |   n:"native"			{#n.print(out);}
    |   a:"abstract"		{#a.print(out);}
	|	i:"strictfp"		{#i.print(out);}
    ;

extendsClause
	:	#(e:"extends" {#e.print(out);} identifier
			(COMMA {#COMMA.print(out);} identifier)* )
	;

implementsClause
	:	#(i:"implements" {#i.print(out);} identifier
			(COMMA {#COMMA.print(out);} identifier)*)
	;

interfaceBlock
	:	#(	OBJBLOCK {#OBJBLOCK.print(out);}
			(	methodDecl
			|	variableDefs
			|	typeDefinition
			)*
			RCURLY {#RCURLY.print(out);}
		)
	;
	
objBlock
	:	#(	OBJBLOCK {#OBJBLOCK.print(out);}
			(	ctorDef
			|	methodDef
			|	variableDefs
			|	typeDefinition
			|	#(s:"static" {#s.print(out);} slist)
			|	#(INSTANCE_INIT slist)
			)*
			RCURLY {#RCURLY.print(out);}
		)
	;

ctorDef
	:	#(CTOR_DEF modifiers methodHead slist)
	;

methodDecl
	:	#(METHOD_DEF modifiers typeSpec methodHead SEMI {#SEMI.print(out);})
	;

methodDef
	:	#(METHOD_DEF modifiers typeSpec methodHead
			(slist | SEMI {#SEMI.print(out);} ))
	;

variableDefs
	:	#(VARIABLE_DEFS modifiers typeSpec
			variableDef (COMMA {#COMMA.print(out);} variableDef)*
			SEMI {#SEMI.print(out);} )
	;

variableDef
	:	#(VARIABLE_DEF variableDeclarator (varInitializer)? )
	;

variableDeclarator
	:	IDENT {#IDENT.print(out);} declaratorBrackets
	;

declaratorBrackets
	:	(l:ARRAY_DECLARATOR r:RBRACK {#l.print(out); #r.print(out);} )*
	;

varInitializer
	:	#(ASSIGN {#ASSIGN.print(out);} initializer)
	;

parameterDef
	:	#(PARAMETER_DEF modifiers typeSpec IDENT {#IDENT.print(out);}
			declaratorBrackets)
	;

initializer
	:	expression
	|	arrayInitializer
	;

arrayInitializer
	:	#(ARRAY_INIT {#ARRAY_INIT.print(out);}
			(initializer (commaInitializer)? )?
			RCURLY {#RCURLY.print(out);} )
	;

commaInitializer
	:	#(COMMA {#COMMA.print(out);} (initializer (commaInitializer)? )? )
	;

methodHead
	:	IDENT LPAREN {#IDENT.print(out); #LPAREN.print(out);}
		#( PARAMETERS
			(parameterDef (COMMA {#COMMA.print(out);} parameterDef)* )? )
		RPAREN {#RPAREN.print(out);} declaratorBrackets (throwsClause)?
	;

throwsClause
	:	#( t:"throws" {#t.print(out);} identifier
			(COMMA {#COMMA.print(out);} identifier)* )
	;

identifier
	:	IDENT {#IDENT.print(out);}
	|	#( DOT identifier IDENT {#DOT.print(out); #IDENT.print(out);} )
	;

identifierStar
	:	IDENT {#IDENT.print(out);}
	|	#(DOT identifier {#DOT.print(out);}
		  (STAR {#STAR.print(out);} | IDENT {#IDENT.print(out);} ) )
	;

slist
	:	#( SLIST {#SLIST.print(out);} (stat)* RCURLY {#RCURLY.print(out);} )
	;

stat:	variableDefs
	|	#(TYPE_STAT typeDefinition)
	|	#(EXPRESSION_STAT expression sm1:SEMI) {sm1.print(out);}
	|	#(LABELED_STAT c1:COLON {#LABELED_STAT.print(out); #c1.print(out);}
			stat)
	|	#(i:"if" l1:LPAREN {i.print(out); #l1.print(out);} expression r1:RPAREN
			{#r1.print(out);} stat (e:"else" {#e.print(out);} stat)? )
	|	#(f:"for" l2:LPAREN {f.print(out); #l2.print(out);}
			#(FOR_INIT (variableDefs | elist sm2:SEMI {#sm2.print(out);}) )
			#(FOR_CONDITION (expression)? sm3:SEMI {#sm3.print(out);} )
			#(FOR_ITERATOR elist)
			r2:RPAREN {#r2.print(out);} stat
		)
	|	#(w:"while" l3:LPAREN {#w.print(out); #l3.print(out);} expression
		  r3:RPAREN {#r3.print(out);} stat)
	|	#(d:"do" {#d.print(out);} stat wh:"while" l4:LPAREN
			{#wh.print(out); #l4.print(out);} expression r4:RPAREN sm4:SEMI
			{#r4.print(out); #sm4.print(out);} )
	|	#(b:"break" {#b.print(out);} (id1:IDENT {#id1.print(out);})?
			sm5:SEMI {#sm5.print(out);} )
	|	#(c:"continue" {#c.print(out);} (id2:IDENT {#id2.print(out);})?
			sm6:SEMI {#sm6.print(out);} )
	|	#(r:"return" {#r.print(out);} (expression)?
			sm7:SEMI {#sm7.print(out);} )
	|	#(sw:"switch" l5:LPAREN {#sw.print(out); #l5.print(out);} expression
			r5:RPAREN LCURLY {#r5.print(out); #LCURLY.print(out);}
			(caseGroup)* RCURLY {#RCURLY.print(out);} )
	|	#(t:"throw" {#t.print(out);} expression sm8:SEMI {#sm8.print(out);} )
	|	#(sy:"synchronized" l6:LPAREN {#sy.print(out); #l6.print(out);}
			expression r6:RPAREN {#r6.print(out);} stat)
    |   #(a:"assert" {#a.print(out);} expression
            (c2:COLON {#c2.print(out);} expression)?
            sm9:SEMI {#sm9.print(out);})
	|	tryBlock
	|	slist // nested SLIST
	|	EMPTY_STAT {#EMPTY_STAT.print(out);}
	;

caseGroup
	:	#(CASE_GROUP (( c:"case" {#c.print(out);} expression
					  | d:"default" {#d.print(out);})
					 COLON {#COLON.print(out);} )+ (stat)*)
	;

tryBlock
	:	#(t:"try" {#t.print(out);} slist (handler)*
			(f:"finally" {#f.print(out);} slist)? )
	;

handler
	:	#(c:"catch" LPAREN {#c.print(out); #LPAREN.print(out);} parameterDef
		  RPAREN {#RPAREN.print(out);} slist )
	;

elist
	:	#( ELIST (expression (COMMA {#COMMA.print(out);} expression)* )? )
	;

expression
	:	#(QUESTION expression {#QUESTION.print(out);} expression
			COLON {#COLON.print(out);} expression)
	|	#(ASSIGN expression {#ASSIGN.print(out);} expression)
	|	#(PLUS_ASSIGN expression {#PLUS_ASSIGN.print(out);} expression)
	|	#(CONCAT_ASSIGN expression {#CONCAT_ASSIGN.print(out);} expression)
	|	#(MINUS_ASSIGN expression {#MINUS_ASSIGN.print(out);} expression)
	|	#(STAR_ASSIGN expression {#STAR_ASSIGN.print(out);} expression)
	|	#(DIV_ASSIGN expression {#DIV_ASSIGN.print(out);} expression)
	|	#(MOD_ASSIGN expression {#MOD_ASSIGN.print(out);} expression)
	|	#(SR_ASSIGN expression {#SR_ASSIGN.print(out);} expression)
	|	#(BSR_ASSIGN expression {#BSR_ASSIGN.print(out);} expression)
	|	#(SL_ASSIGN expression {#SL_ASSIGN.print(out);} expression)
	|	#(BAND_ASSIGN expression {#BAND_ASSIGN.print(out);} expression)
	|	#(BXOR_ASSIGN expression {#BXOR_ASSIGN.print(out);} expression)
	|	#(BOR_ASSIGN expression {#BOR_ASSIGN.print(out);} expression)
	|	#(LOR expression {#LOR.print(out);} expression)
	|	#(LAND expression {#LAND.print(out);} expression)
	|	#(BOR expression {#BOR.print(out);} expression)
	|	#(BXOR expression {#BXOR.print(out);} expression)
	|	#(BAND expression {#BAND.print(out);} expression)
	|	#(NOT_EQUAL expression {#NOT_EQUAL.print(out);} expression)
	|	#(EQUAL expression {#EQUAL.print(out);} expression)
	|	#(LT expression {#LT.print(out);} expression)
	|	#(GT expression {#GT.print(out);} expression)
	|	#(LE expression {#LE.print(out);} expression)
	|	#(GE expression {#GE.print(out);} expression)
	|	#(SL expression {#SL.print(out);} expression)
	|	#(SR expression {#SR.print(out);} expression)
	|	#(BSR expression {#BSR.print(out);} expression)
	|	#(PLUS expression {#PLUS.print(out);} expression)
	|	#(CONCATENATION expression {#CONCATENATION.print(out);} expression)
	|	#(MINUS expression {#MINUS.print(out);} expression)
	|	#(DIV expression {#DIV.print(out);} expression)
	|	#(MOD expression {#MOD.print(out);} expression)
	|	#(STAR expression {#STAR.print(out);} expression)
	|	#(INC {#INC.print(out);} expression)
	|	#(DEC {#DEC.print(out);} expression)
	|	#(POST_INC expression {#POST_INC.print(out);})
	|	#(POST_DEC expression {#POST_DEC.print(out);})
	|	#(BNOT {#BNOT.print(out);} expression)
	|	#(LNOT {#LNOT.print(out);} expression)
	|	#(i:"instanceof" expression {#i.print(out);} expression)
	|	#(UNARY_MINUS {#UNARY_MINUS.print(out);} expression)
	|	#(UNARY_PLUS {#UNARY_PLUS.print(out);} expression)
	|	primaryExpression
	;

primaryExpression
    :   IDENT {#IDENT.print(out);}
    |   #(	d:DOT
			(	expression {#d.print(out);}
				(	IDENT {#IDENT.print(out);}
				|	arrayIndex
				|	th:"this" {#th.print(out);}
				|	c:"class" {#c.print(out);}
				|	#( ne:"new" IDENT {#ne.print(out); #IDENT.print(out);}
						lp:LPAREN {#lp.print(out);} elist
						rp:RPAREN {#rp.print(out);} )
				|	su:"super" {#su.print(out);}
				)
			|	#(ARRAY_DECLARATOR type RBRACK)
				{#ARRAY_DECLARATOR.print(out); #RBRACK.print(out);}
				(cl:"class" {#d.print(out); #cl.print(out);})?
			|	builtInType (cl2:"class" {#d.print(out); #cl2.print(out);})?
			)
		)
	|	arrayIndex
	|	#(call1:METHOD_CALL primaryExpression {#call1.print(out);} elist
			r2:RPAREN {#r2.print(out);} )
	|	#(call2:CONSTRUCTOR_CALL primaryExpression {#call2.print(out);} elist
			r3:RPAREN {#r3.print(out);} )
	|	#(t:TYPECAST {#t.print(out);} typeSpec r4:RPAREN {#r4.print(out);}
			expression)
	|   #(p:PAREN_EXPR {#p.print(out);} expression
			r5:RPAREN {#r5.print(out);} )
	|   newExpression
	|   constant
    |   s:"super"	{#s.print(out);}
    |   tr:"true"	{#tr.print(out);}
    |   f:"false"	{#f.print(out);}
    |   thi:"this"	{#thi.print(out);}
    |   nu:"null"	{#nu.print(out);}
	|	typeSpec // type name used with instanceof
	;

arrayIndex
	:	#(INDEX_OP primaryExpression {#INDEX_OP.print(out);} expression
		  RBRACK {#RBRACK.print(out);} )
	;

constant
    :   NUM_INT {#NUM_INT.print(out);}
    |   CHAR_LITERAL {#CHAR_LITERAL.print(out);}
    |   STRING_LITERAL {#STRING_LITERAL.print(out);}
    |   NUM_FLOAT {#NUM_FLOAT.print(out);}
    ;

newExpression
	:	#(	n:"new" {#n.print(out);} type
			(	newArrayDeclarator (arrayInitializer)?
			|	LPAREN {#LPAREN.print(out);} elist RPAREN {#RPAREN.print(out);}
				(#("class" objBlock) )?    // DON'T WRITE THAT "class"!
			)
		)
	;

newArrayDeclarator
	:	#( ARRAY_DECLARATOR (newArrayDeclarator)?
			{#ARRAY_DECLARATOR.print(out);} (expression)?
			RBRACK {#RBRACK.print(out);} )
	;
