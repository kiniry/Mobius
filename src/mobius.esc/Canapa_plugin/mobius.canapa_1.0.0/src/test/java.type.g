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
import jparse.expr.*;
}

/**
 * A Java 1.2 tree walker that prints out expression types as they are
 * encountered.  This tree walker is based on, but differs significantly from,
 * the public domain ANTLR tree walker identified as follows:
 *
 * Java 1.2 AST Recognizer Grammar
 *
 * Author:
 *     Terence Parr    parrt@jguru.com
 *
 * Version tracking now done with following ID:
 *
 * $Id: java.type.g,v 1.5 2004/07/08 18:29:01 james Exp $
 *
 * This grammar is in the PUBLIC DOMAIN
 *
 * BUGS
 */
class JavaTyper extends TreeParser;

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

	/**
	 * Print the type of an expression
	 *
	 * @param expr the expression to print
	 */
	protected void printType(final AST expr) {
		final ExpressionAST ex = (ExpressionAST)expr;
		final Type type = ex.retrieveType();
        try {
            out.write(" has type ");
            out.write(type == null ? "null" : type.getName());
            out.write(" and");
        } catch (IOException ioEx) {
            // FIXME: What should we do here?
        }
		printExceptions(ex);
	}

	protected void printExceptions(final HasExceptions hasEx) {
		final Type[] exceptions = hasEx.getExceptionTypes();
        try {
            out.write(" throws ");
            if (exceptions.length == 0) {
                out.write("nothing");
            } else {
                out.write(exceptions[0].getName());
                for (int i = 1; i < exceptions.length; i++) {
                    out.write(", ");
                    out.write(exceptions[i].getName());
                }
                out.write('\n');
            }
		} catch (IOException ioEx) {
            // FIXME: What should we do here?
        }
	}
}

compilationUnit[OutputStreamWriter output]
	:	{ out = output; }
		#(FILE
			(packageDefinition)?
			(importDefinition)*
			(typeDefinitionExcept[false])*
		)
		{ try {output.flush();} catch (IOException ioEx) { /* ignored */ } }
	;

packageDefinition
	:	#( "package" identifier[false] SEMI )
	;

importDefinition
	:	#( "import" identifierStar SEMI )
	;

typeDefinition
	:	#("class" modifiers[true] IDENT (extendsClause)? (implementsClause)?
			objBlock)
	|	#("interface" modifiers[true] IDENT (extendsClause)?
			interfaceBlock[true] )
	|	SEMI
	;

typeDefinitionExcept[boolean inner]
	:	#("class" modifiers[false] IDENT (extendsClause)? (implementsClause)?
			objBlockExcept[inner])
	|	#("interface" modifiers[false] IDENT (extendsClause)?
			interfaceBlock[inner] )
	|	SEMI
	;

typeSpec[boolean print]
	:	#(TYPE typeSpecArray[print])
	;

typeSpecType
	:	#(TYPE typeSpecArrayType)
	;

typeSpecArray[boolean print]
	:	#( ARRAY_DECLARATOR (typeSpecArray[print])? RBRACK
			{
				if (print) {
					#ARRAY_DECLARATOR.print(out);
					#RBRACK.print(out);
				}
			}
		)
	|	type[print]
	;

typeSpecArrayType
	:	#( ARRAY_DECLARATOR (typeSpecArrayType)? RBRACK )
	|	typeType
	;

type[boolean print]
	:	identifier[print]
	|	builtInType[print]
	;

typeType
	:	identifierType
	|	builtInTypeType
	;

builtInType[boolean print]
    :   v:"void"	{if (print) #v.print(out);}
    |   b:"boolean"	{if (print) #b.print(out);}
    |   y:"byte"	{if (print) #y.print(out);}
    |   c:"char"	{if (print) #c.print(out);}
    |   s:"short"	{if (print) #s.print(out);}
    |   i:"int"		{if (print) #i.print(out);}
    |   f:"float"	{if (print) #f.print(out);}
    |   l:"long"	{if (print) #l.print(out);}
    |   d:"double"	{if (print) #d.print(out);}
    ;

builtInTypeType
    :   (	"void"
		|   "boolean"
		|   "byte"
		|   "char"
		|   "short"
		|   "int"
		|   "float"
		|   "long"
		|   "double"
		)
		{ builtInType(#builtInTypeType, true); printType(#builtInTypeType); }
    ;

modifiers[boolean print]
	:	#( MODIFIERS (modifier[print])* )
	;

modifier[boolean print]
    :   u:"public"			{if (print) #u.print(out);}
    |   p:"private"			{if (print) #p.print(out);}
    |   r:"protected"		{if (print) #r.print(out);}
    |   s:"static"			{if (print) #s.print(out);}
    |   f:"final"			{if (print) #f.print(out);}
    |   y:"synchronized"	{if (print) #y.print(out);}
    |   v:"volatile"		{if (print) #v.print(out);}
    |   t:"transient"		{if (print) #t.print(out);}
    |   n:"native"			{if (print) #n.print(out);}
    |   a:"abstract"		{if (print) #a.print(out);}
	|	i:"strictfp"		{if (print) #i.print(out);}
    ;

extendsClause
	:	#("extends" identifier[false] (COMMA identifier[false])* )
	;

implementsClause
	:	#("implements" identifier[false] (COMMA identifier[false])*)
	;

interfaceBlock[boolean inner]
	:	#(	OBJBLOCK
			(	methodDecl[inner]
			|	variableDefs
			|	typeDefinition
			)*
			RCURLY
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

objBlockExcept[boolean inner]
	:	#(	OBJBLOCK
			(	ctorDefExcept[inner]
			|	methodDefExcept[inner]
			|	variableDefsExcept
			|	typeDefinitionExcept[true]
			|	#("static" slistExcept)
			|	#(INSTANCE_INIT slistExcept)
			)*
			RCURLY
		)
	;

ctorDef
	:	#(CTOR_DEF modifiers[true] methodHead slist)
	;

ctorDefExcept[boolean inner]
	:	#(CTOR_DEF modifiers[false] methodHeadExcept[inner] slistExcept)
	;

methodDecl[boolean inner]
	:	#(METHOD_DEF modifiers[false] typeSpec[false] methodHeadExcept[inner]
			SEMI)
	;

methodDef
	:	#(METHOD_DEF modifiers[true] typeSpec[true] methodHead
			(slist | SEMI {#SEMI.print(out);} ))
	;

methodDefExcept[boolean inner]
	:	#(METHOD_DEF modifiers[false] typeSpec[false] methodHeadExcept[inner]
			(slistExcept | SEMI ))
	;

variableDefs
	:	#(VARIABLE_DEFS modifiers[true] typeSpec[true]
			variableDef (COMMA {#COMMA.print(out);} variableDef)*
			SEMI {#SEMI.print(out);} )
	;

variableDefsExcept
	:	#(VARIABLE_DEFS modifiers[false] typeSpec[false] variableDefExcept
			(COMMA variableDefExcept)* SEMI)
		{	variableDefs(#variableDefsExcept);
			printExceptions((HasExceptions)#variableDefsExcept);
		}
	;

variableDef
	:	#(VARIABLE_DEF variableDeclarator (varInitializer)? )
	;

variableDefExcept
	:	#(VARIABLE_DEF variableDeclaratorExcept (varInitializerExcept)? )
	;

variableDeclarator
	:	IDENT {#IDENT.print(out);} declaratorBrackets
	;

variableDeclaratorExcept
	:	IDENT declaratorBracketsExcept
	;

declaratorBrackets
	:	(l:ARRAY_DECLARATOR r:RBRACK {#l.print(out); #r.print(out);} )*
	;

declaratorBracketsExcept
	:	(ARRAY_DECLARATOR RBRACK)*
	;

varInitializer
	:	#(ASSIGN {#ASSIGN.print(out);} initializer)
	;

varInitializerExcept
	:	#(ASSIGN initializerType)
	;

parameterDef
	:	#(PARAMETER_DEF modifiers[true] typeSpec[true]
			IDENT {#IDENT.print(out);} declaratorBrackets)
	;

parameterDefExcept
	:	#(PARAMETER_DEF modifiers[false] typeSpec[false] IDENT
			declaratorBrackets)
	;

initializer
	:	expression
	|	arrayInitializer
	;

initializerType
	:	expressionType
	|	arrayInitializerType
	;

arrayInitializer
	:	#(a:ARRAY_INIT {#a.print(out);} (initializer (commaInitializer)? )?
			r:RCURLY {#r.print(out);})
	;

arrayInitializerType
	:	#(ARRAY_INIT (initializerType (commaInitializerType)? )? RCURLY)
		{ printType(#arrayInitializerType); }
	;

commaInitializer
	:	#(c:COMMA {#c.print(out);} (initializer (commaInitializer)? )? )
	;

commaInitializerType
	:	#(COMMA (initializerType (commaInitializerType)? )? )
	;

methodHead
	:	IDENT LPAREN { #IDENT.print(out); #LPAREN.print(out); }
		#( PARAMETERS (parameterDef (COMMA parameterDef)* )? )
		RPAREN { #RPAREN.print(out); } declaratorBrackets (throwsClause)?
	;

methodHeadExcept[boolean inner]
	:	IDENT LPAREN { if (inner) { #IDENT.print(out); #LPAREN.print(out); } }
		#( PARAMETERS (parameterDefExcept (COMMA parameterDefExcept)* )? )
		RPAREN { if (inner) #RPAREN.print(out); } declaratorBrackets
		(throwsClause)?
	;

throwsClause
	:	#( "throws" identifier[false] (COMMA identifier[false])* )
	;

identifier[boolean print]
	:	id1:IDENT {if (print) #id1.print(out);}
	|	#( DOT identifier[print] id2:IDENT
			{
				if (print) {
					#DOT.print(out);
					#id2.print(out);
				}
			}
		)
	;

identifierType
	:	(	IDENT
		|	#( DOT identifierType IDENT )
		)
		{ identifier(#identifierType, true); printType(#identifierType); }
	;

identifierStar
	:	IDENT
	|	#(DOT identifier[false] (STAR | IDENT ) )
	;

slist
	:	#( SLIST {#SLIST.print(out);} (stat)* RCURLY {#RCURLY.print(out);} )
	;

slistExcept
	:	#( SLIST (statExcept)* RCURLY )
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

statExcept
	:	variableDefsExcept
	|	tryBlockExcept
	|	slistExcept // nested SLIST
	|	moreStatExcept
	;

moreStatExcept
	:	(	#(TYPE_STAT typeDefinitionExcept[true])
		|	#(EXPRESSION_STAT expressionType SEMI)
		|	#(LABELED_STAT COLON statExcept)
		|	#("if" LPAREN expressionType RPAREN statExcept
				("else" statExcept)? )
		|	#("for" LPAREN
				#(FOR_INIT (variableDefsExcept | elistType SEMI) )
				#(FOR_CONDITION (expressionType)? SEMI)
				#(FOR_ITERATOR elistType)
				RPAREN statExcept
			)
		|	#("while" LPAREN expressionType RPAREN statExcept)
		|	#("do" statExcept "while" LPAREN expressionType RPAREN SEMI)
		|	#("break" (IDENT)? SEMI)
		|	#("continue" (IDENT)? SEMI)
		|	#("return" (expressionType)? SEMI)
		|	#("switch" LPAREN expressionType RPAREN
				LCURLY (caseGroupExcept)* RCURLY)
		|	#("throw" expressionType SEMI)
		|	#("synchronized" LPAREN expressionType RPAREN statExcept)
		|	EMPTY_STAT
		)
		{
			stat(#moreStatExcept);
			printExceptions((HasExceptions)#moreStatExcept);
		}
	;

caseGroup
	:	#(CASE_GROUP (( c:"case" {#c.print(out);} expression
					  | d:"default" {#d.print(out);})
					 COLON {#COLON.print(out);} )+ (stat)*)
	;

caseGroupExcept
	:	#(CASE_GROUP (( "case" expressionType | "default") COLON )+
			(statExcept)*)
		{	caseGroup(#caseGroupExcept); }
	;

tryBlock
	:	#(t:"try" {#t.print(out);} slist (handler)*
			(f:"finally" {#f.print(out);} slist)? )
	;

tryBlockExcept
	:	#("try" slistExcept (handlerExcept)* ("finally" slistExcept)? )
		{
			tryBlock(#tryBlockExcept);
			printExceptions((HasExceptions)#tryBlockExcept);
		}
	;

handler
	:	#(c:"catch" LPAREN {#c.print(out); #LPAREN.print(out);} parameterDef
		  RPAREN {#RPAREN.print(out);} slist )
	;

handlerExcept
	:	#("catch" LPAREN parameterDefExcept RPAREN slistExcept )
		{
			handler(#handlerExcept);
			printExceptions((HasExceptions)#handlerExcept);
		}
	;

elist
	:	#( ELIST (expression (COMMA {#COMMA.print(out);} expression)* )? )
	;

elistType
	:	#( ELIST (expressionType (COMMA expressionType)* )? )
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

expressionType
	:	(	#(QUESTION expressionType expressionType COLON expressionType)
		|	#(ASSIGN expressionType expressionType)
		|	#(PLUS_ASSIGN expressionType expressionType)
		|	#(CONCAT_ASSIGN expressionType expressionType)
		|	#(MINUS_ASSIGN expressionType expressionType)
		|	#(STAR_ASSIGN expressionType expressionType)
		|	#(DIV_ASSIGN expressionType expressionType)
		|	#(MOD_ASSIGN expressionType expressionType)
		|	#(SR_ASSIGN expressionType expressionType)
		|	#(BSR_ASSIGN expressionType expressionType)
		|	#(SL_ASSIGN expressionType expressionType)
		|	#(BAND_ASSIGN expressionType expressionType)
		|	#(BXOR_ASSIGN expressionType expressionType)
		|	#(BOR_ASSIGN expressionType expressionType)
		|	#(LOR expressionType expressionType)
		|	#(LAND expressionType expressionType)
		|	#(BOR expressionType expressionType)
		|	#(BXOR expressionType expressionType)
		|	#(BAND expressionType expressionType)
		|	#(NOT_EQUAL expressionType expressionType)
		|	#(EQUAL expressionType expressionType)
		|	#(LT expressionType expressionType)
		|	#(GT expressionType expressionType)
		|	#(LE expressionType expressionType)
		|	#(GE expressionType expressionType)
		|	#(SL expressionType expressionType)
		|	#(SR expressionType expressionType)
		|	#(BSR expressionType expressionType)
		|	#(PLUS expressionType expressionType)
		|	#(CONCATENATION expressionType expressionType)
		|	#(MINUS expressionType expressionType)
		|	#(DIV expressionType expressionType)
		|	#(MOD expressionType expressionType)
		|	#(STAR expressionType expressionType)
		|	#(INC expressionType)
		|	#(DEC expressionType)
		|	#(POST_INC expressionType)
		|	#(POST_DEC expressionType)
		|	#(BNOT expressionType)
		|	#(LNOT expressionType)
		|	#("instanceof" expressionType expressionType)
		|	#(UNARY_MINUS expressionType)
		|	#(UNARY_PLUS expressionType)
		)
		{ expression(#expressionType); printType(#expressionType); } 
	|	primaryExpressionType
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
			|	#(ARRAY_DECLARATOR type[true] RBRACK)
				{#ARRAY_DECLARATOR.print(out); #RBRACK.print(out);}
				(cl:"class" {#d.print(out); #cl.print(out);})?
			|	builtInType[true] (cl2:"class"
					{#d.print(out); #cl2.print(out);})?
			)
		)
	|	arrayIndex
	|	#(call1:METHOD_CALL primaryExpression {#call1.print(out);} elist
			r2:RPAREN {#r2.print(out);} )
	|	#(call2:CONSTRUCTOR_CALL primaryExpression {#call2.print(out);} elist
			r3:RPAREN {#r3.print(out);} )
	|	#(t:TYPECAST {#t.print(out);} typeSpec[true]
			r4:RPAREN {#r4.print(out);} expression)
	|   #(p:PAREN_EXPR {#p.print(out);} expression
			r5:RPAREN {#r5.print(out);} )
	|   newExpression
	|   constant
    |   s:"super"	{#s.print(out);}
    |   tr:"true"	{#tr.print(out);}
    |   f:"false"	{#f.print(out);}
    |   thi:"this"	{#thi.print(out);}
    |   nu:"null"	{#nu.print(out);}
	|	typeSpec[true] // type name used with instanceof
	;

primaryExpressionType
    :   (	IDENT
		|   #(	DOT
				(	expressionType
					(	IDENT
					|	arrayIndexType
					|	"this"
					|	"class"
					|	#( "new" IDENT LPAREN elistType RPAREN )
					|	"super"
					)
				|	#(ARRAY_DECLARATOR typeType RBRACK) ("class")?
				|	builtInTypeType ("class")?
				)
			)
		|	#(METHOD_CALL primaryExpressionType elistType RPAREN)
		|	#(CONSTRUCTOR_CALL primaryExpressionType elistType RPAREN)
		|	#(TYPECAST typeSpecType RPAREN expressionType)
		|   #(PAREN_EXPR expressionType RPAREN)
		|   "super"
		|   "true"
		|   "false"
		|   "this"
		|   "null"
		)
		{
			primaryExpression(#primaryExpressionType);
			printType(#primaryExpressionType);
		}
	|	arrayIndexType
	|   newExpressionType
	|   constantType
	|	typeSpecType // type name used with instanceof
	;

arrayIndex
	:	#(INDEX_OP primaryExpression {#INDEX_OP.print(out);} expression
		  RBRACK {#RBRACK.print(out);} )
	;

arrayIndexType
	:	#(INDEX_OP primaryExpressionType expressionType RBRACK)
		{ arrayIndex(#arrayIndexType); printType(#arrayIndexType); }
	;

constant
    :   NUM_INT {#NUM_INT.print(out);}
    |   CHAR_LITERAL {#CHAR_LITERAL.print(out);}
    |   STRING_LITERAL {#STRING_LITERAL.print(out);}
    |   NUM_FLOAT {#NUM_FLOAT.print(out);}
    ;

constantType
    :   constant
		{ printType(#constantType); }
    ;

newExpression
	:	#(	n:"new" {#n.print(out);} type[true]
			(	newArrayDeclarator (arrayInitializer)?
			|	LPAREN {#LPAREN.print(out);} elist RPAREN {#RPAREN.print(out);}
				(#("class" objBlock))?    // DON'T PRINT THAT "class"!
			)
		)
	;

newExpressionType
	:	#(	"new" typeType
			(	newArrayDeclaratorType (arrayInitializerType)?
			|	LPAREN elistType RPAREN (#(c:"class" objBlockExcept[true]))?
			)
		)
		{ newExpression(#newExpressionType); printType(#newExpressionType); }
		;

newArrayDeclarator
	:	#(ARRAY_DECLARATOR (newArrayDeclarator)?
			{#ARRAY_DECLARATOR.print(out);} (expression)?
			RBRACK {#RBRACK.print(out);} )
	;

newArrayDeclaratorType
	:	#(ARRAY_DECLARATOR (newArrayDeclaratorType)? (expressionType)? RBRACK)
	;
