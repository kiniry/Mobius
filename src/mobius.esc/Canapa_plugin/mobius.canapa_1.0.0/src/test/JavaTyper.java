// $ANTLR 2.7.4: "java.type.g" -> "JavaTyper.java"$

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

import antlr.TreeParser;
import antlr.Token;
import antlr.collections.AST;
import antlr.RecognitionException;
import antlr.ANTLRException;
import antlr.NoViableAltException;
import antlr.MismatchedTokenException;
import antlr.SemanticException;
import antlr.collections.impl.BitSet;
import antlr.ASTPair;
import antlr.collections.impl.ASTArray;


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
public class JavaTyper extends antlr.TreeParser       implements JavaTyperTokenTypes
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
public JavaTyper() {
	tokenNames = _tokenNames;
}

	public final void compilationUnit(AST _t,
		OutputStreamWriter output
	) throws RecognitionException {
		
		JavaAST compilationUnit_AST_in = (_t == ASTNULL) ? null : (JavaAST)_t;
		
		try {      // for error handling
			out = output;
			AST __t2 = _t;
			JavaAST tmp1_AST_in = (JavaAST)_t;
			match(_t,FILE);
			_t = _t.getFirstChild();
			{
			if (_t==null) _t=ASTNULL;
			switch ( _t.getType()) {
			case LITERAL_package:
			{
				packageDefinition(_t);
				_t = _retTree;
				break;
			}
			case 3:
			case SEMI:
			case LITERAL_import:
			case LITERAL_class:
			case LITERAL_interface:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(_t);
			}
			}
			}
			{
			_loop5:
			do {
				if (_t==null) _t=ASTNULL;
				if ((_t.getType()==LITERAL_import)) {
					importDefinition(_t);
					_t = _retTree;
				}
				else {
					break _loop5;
				}
				
			} while (true);
			}
			{
			_loop7:
			do {
				if (_t==null) _t=ASTNULL;
				if ((_t.getType()==SEMI||_t.getType()==LITERAL_class||_t.getType()==LITERAL_interface)) {
					typeDefinitionExcept(_t,false);
					_t = _retTree;
				}
				else {
					break _loop7;
				}
				
			} while (true);
			}
			_t = __t2;
			_t = _t.getNextSibling();
			try {output.flush();} catch (IOException ioEx) { /* ignored */ }
		}
		catch (RecognitionException ex) {
			reportError(ex);
			if (_t!=null) {_t = _t.getNextSibling();}
		}
		_retTree = _t;
	}
	
	public final void packageDefinition(AST _t) throws RecognitionException {
		
		JavaAST packageDefinition_AST_in = (_t == ASTNULL) ? null : (JavaAST)_t;
		
		try {      // for error handling
			AST __t9 = _t;
			JavaAST tmp2_AST_in = (JavaAST)_t;
			match(_t,LITERAL_package);
			_t = _t.getFirstChild();
			identifier(_t,false);
			_t = _retTree;
			JavaAST tmp3_AST_in = (JavaAST)_t;
			match(_t,SEMI);
			_t = _t.getNextSibling();
			_t = __t9;
			_t = _t.getNextSibling();
		}
		catch (RecognitionException ex) {
			reportError(ex);
			if (_t!=null) {_t = _t.getNextSibling();}
		}
		_retTree = _t;
	}
	
	public final void importDefinition(AST _t) throws RecognitionException {
		
		JavaAST importDefinition_AST_in = (_t == ASTNULL) ? null : (JavaAST)_t;
		
		try {      // for error handling
			AST __t11 = _t;
			JavaAST tmp4_AST_in = (JavaAST)_t;
			match(_t,LITERAL_import);
			_t = _t.getFirstChild();
			identifierStar(_t);
			_t = _retTree;
			JavaAST tmp5_AST_in = (JavaAST)_t;
			match(_t,SEMI);
			_t = _t.getNextSibling();
			_t = __t11;
			_t = _t.getNextSibling();
		}
		catch (RecognitionException ex) {
			reportError(ex);
			if (_t!=null) {_t = _t.getNextSibling();}
		}
		_retTree = _t;
	}
	
	public final void typeDefinitionExcept(AST _t,
		boolean inner
	) throws RecognitionException {
		
		JavaAST typeDefinitionExcept_AST_in = (_t == ASTNULL) ? null : (JavaAST)_t;
		
		try {      // for error handling
			if (_t==null) _t=ASTNULL;
			switch ( _t.getType()) {
			case LITERAL_class:
			{
				AST __t19 = _t;
				JavaAST tmp6_AST_in = (JavaAST)_t;
				match(_t,LITERAL_class);
				_t = _t.getFirstChild();
				modifiers(_t,false);
				_t = _retTree;
				JavaAST tmp7_AST_in = (JavaAST)_t;
				match(_t,IDENT);
				_t = _t.getNextSibling();
				{
				if (_t==null) _t=ASTNULL;
				switch ( _t.getType()) {
				case LITERAL_extends:
				{
					extendsClause(_t);
					_t = _retTree;
					break;
				}
				case OBJBLOCK:
				case LITERAL_implements:
				{
					break;
				}
				default:
				{
					throw new NoViableAltException(_t);
				}
				}
				}
				{
				if (_t==null) _t=ASTNULL;
				switch ( _t.getType()) {
				case LITERAL_implements:
				{
					implementsClause(_t);
					_t = _retTree;
					break;
				}
				case OBJBLOCK:
				{
					break;
				}
				default:
				{
					throw new NoViableAltException(_t);
				}
				}
				}
				objBlockExcept(_t,inner);
				_t = _retTree;
				_t = __t19;
				_t = _t.getNextSibling();
				break;
			}
			case LITERAL_interface:
			{
				AST __t22 = _t;
				JavaAST tmp8_AST_in = (JavaAST)_t;
				match(_t,LITERAL_interface);
				_t = _t.getFirstChild();
				modifiers(_t,false);
				_t = _retTree;
				JavaAST tmp9_AST_in = (JavaAST)_t;
				match(_t,IDENT);
				_t = _t.getNextSibling();
				{
				if (_t==null) _t=ASTNULL;
				switch ( _t.getType()) {
				case LITERAL_extends:
				{
					extendsClause(_t);
					_t = _retTree;
					break;
				}
				case OBJBLOCK:
				{
					break;
				}
				default:
				{
					throw new NoViableAltException(_t);
				}
				}
				}
				interfaceBlock(_t,inner);
				_t = _retTree;
				_t = __t22;
				_t = _t.getNextSibling();
				break;
			}
			case SEMI:
			{
				JavaAST tmp10_AST_in = (JavaAST)_t;
				match(_t,SEMI);
				_t = _t.getNextSibling();
				break;
			}
			default:
			{
				throw new NoViableAltException(_t);
			}
			}
		}
		catch (RecognitionException ex) {
			reportError(ex);
			if (_t!=null) {_t = _t.getNextSibling();}
		}
		_retTree = _t;
	}
	
	public final void identifier(AST _t,
		boolean print
	) throws RecognitionException {
		
		JavaAST identifier_AST_in = (_t == ASTNULL) ? null : (JavaAST)_t;
		JavaAST id1 = null;
		JavaAST id2 = null;
		
		try {      // for error handling
			if (_t==null) _t=ASTNULL;
			switch ( _t.getType()) {
			case IDENT:
			{
				id1 = (JavaAST)_t;
				match(_t,IDENT);
				_t = _t.getNextSibling();
				if (print) id1.print(out);
				break;
			}
			case DOT:
			{
				AST __t145 = _t;
				JavaAST tmp11_AST_in = (JavaAST)_t;
				match(_t,DOT);
				_t = _t.getFirstChild();
				identifier(_t,print);
				_t = _retTree;
				id2 = (JavaAST)_t;
				match(_t,IDENT);
				_t = _t.getNextSibling();
				
								if (print) {
									tmp11_AST_in.print(out);
									id2.print(out);
								}
							
				_t = __t145;
				_t = _t.getNextSibling();
				break;
			}
			default:
			{
				throw new NoViableAltException(_t);
			}
			}
		}
		catch (RecognitionException ex) {
			reportError(ex);
			if (_t!=null) {_t = _t.getNextSibling();}
		}
		_retTree = _t;
	}
	
	public final void identifierStar(AST _t) throws RecognitionException {
		
		JavaAST identifierStar_AST_in = (_t == ASTNULL) ? null : (JavaAST)_t;
		
		try {      // for error handling
			if (_t==null) _t=ASTNULL;
			switch ( _t.getType()) {
			case IDENT:
			{
				JavaAST tmp12_AST_in = (JavaAST)_t;
				match(_t,IDENT);
				_t = _t.getNextSibling();
				break;
			}
			case DOT:
			{
				AST __t150 = _t;
				JavaAST tmp13_AST_in = (JavaAST)_t;
				match(_t,DOT);
				_t = _t.getFirstChild();
				identifier(_t,false);
				_t = _retTree;
				{
				if (_t==null) _t=ASTNULL;
				switch ( _t.getType()) {
				case STAR:
				{
					JavaAST tmp14_AST_in = (JavaAST)_t;
					match(_t,STAR);
					_t = _t.getNextSibling();
					break;
				}
				case IDENT:
				{
					JavaAST tmp15_AST_in = (JavaAST)_t;
					match(_t,IDENT);
					_t = _t.getNextSibling();
					break;
				}
				default:
				{
					throw new NoViableAltException(_t);
				}
				}
				}
				_t = __t150;
				_t = _t.getNextSibling();
				break;
			}
			default:
			{
				throw new NoViableAltException(_t);
			}
			}
		}
		catch (RecognitionException ex) {
			reportError(ex);
			if (_t!=null) {_t = _t.getNextSibling();}
		}
		_retTree = _t;
	}
	
	public final void typeDefinition(AST _t) throws RecognitionException {
		
		JavaAST typeDefinition_AST_in = (_t == ASTNULL) ? null : (JavaAST)_t;
		
		try {      // for error handling
			if (_t==null) _t=ASTNULL;
			switch ( _t.getType()) {
			case LITERAL_class:
			{
				AST __t13 = _t;
				JavaAST tmp16_AST_in = (JavaAST)_t;
				match(_t,LITERAL_class);
				_t = _t.getFirstChild();
				modifiers(_t,true);
				_t = _retTree;
				JavaAST tmp17_AST_in = (JavaAST)_t;
				match(_t,IDENT);
				_t = _t.getNextSibling();
				{
				if (_t==null) _t=ASTNULL;
				switch ( _t.getType()) {
				case LITERAL_extends:
				{
					extendsClause(_t);
					_t = _retTree;
					break;
				}
				case OBJBLOCK:
				case LITERAL_implements:
				{
					break;
				}
				default:
				{
					throw new NoViableAltException(_t);
				}
				}
				}
				{
				if (_t==null) _t=ASTNULL;
				switch ( _t.getType()) {
				case LITERAL_implements:
				{
					implementsClause(_t);
					_t = _retTree;
					break;
				}
				case OBJBLOCK:
				{
					break;
				}
				default:
				{
					throw new NoViableAltException(_t);
				}
				}
				}
				objBlock(_t);
				_t = _retTree;
				_t = __t13;
				_t = _t.getNextSibling();
				break;
			}
			case LITERAL_interface:
			{
				AST __t16 = _t;
				JavaAST tmp18_AST_in = (JavaAST)_t;
				match(_t,LITERAL_interface);
				_t = _t.getFirstChild();
				modifiers(_t,true);
				_t = _retTree;
				JavaAST tmp19_AST_in = (JavaAST)_t;
				match(_t,IDENT);
				_t = _t.getNextSibling();
				{
				if (_t==null) _t=ASTNULL;
				switch ( _t.getType()) {
				case LITERAL_extends:
				{
					extendsClause(_t);
					_t = _retTree;
					break;
				}
				case OBJBLOCK:
				{
					break;
				}
				default:
				{
					throw new NoViableAltException(_t);
				}
				}
				}
				interfaceBlock(_t,true);
				_t = _retTree;
				_t = __t16;
				_t = _t.getNextSibling();
				break;
			}
			case SEMI:
			{
				JavaAST tmp20_AST_in = (JavaAST)_t;
				match(_t,SEMI);
				_t = _t.getNextSibling();
				break;
			}
			default:
			{
				throw new NoViableAltException(_t);
			}
			}
		}
		catch (RecognitionException ex) {
			reportError(ex);
			if (_t!=null) {_t = _t.getNextSibling();}
		}
		_retTree = _t;
	}
	
	public final void modifiers(AST _t,
		boolean print
	) throws RecognitionException {
		
		JavaAST modifiers_AST_in = (_t == ASTNULL) ? null : (JavaAST)_t;
		
		try {      // for error handling
			AST __t40 = _t;
			JavaAST tmp21_AST_in = (JavaAST)_t;
			match(_t,MODIFIERS);
			_t = _t.getFirstChild();
			{
			_loop42:
			do {
				if (_t==null) _t=ASTNULL;
				if (((_t.getType() >= LITERAL_public && _t.getType() <= LITERAL_strictfp))) {
					modifier(_t,print);
					_t = _retTree;
				}
				else {
					break _loop42;
				}
				
			} while (true);
			}
			_t = __t40;
			_t = _t.getNextSibling();
		}
		catch (RecognitionException ex) {
			reportError(ex);
			if (_t!=null) {_t = _t.getNextSibling();}
		}
		_retTree = _t;
	}
	
	public final void extendsClause(AST _t) throws RecognitionException {
		
		JavaAST extendsClause_AST_in = (_t == ASTNULL) ? null : (JavaAST)_t;
		
		try {      // for error handling
			AST __t45 = _t;
			JavaAST tmp22_AST_in = (JavaAST)_t;
			match(_t,LITERAL_extends);
			_t = _t.getFirstChild();
			identifier(_t,false);
			_t = _retTree;
			{
			_loop47:
			do {
				if (_t==null) _t=ASTNULL;
				if ((_t.getType()==COMMA)) {
					JavaAST tmp23_AST_in = (JavaAST)_t;
					match(_t,COMMA);
					_t = _t.getNextSibling();
					identifier(_t,false);
					_t = _retTree;
				}
				else {
					break _loop47;
				}
				
			} while (true);
			}
			_t = __t45;
			_t = _t.getNextSibling();
		}
		catch (RecognitionException ex) {
			reportError(ex);
			if (_t!=null) {_t = _t.getNextSibling();}
		}
		_retTree = _t;
	}
	
	public final void implementsClause(AST _t) throws RecognitionException {
		
		JavaAST implementsClause_AST_in = (_t == ASTNULL) ? null : (JavaAST)_t;
		
		try {      // for error handling
			AST __t49 = _t;
			JavaAST tmp24_AST_in = (JavaAST)_t;
			match(_t,LITERAL_implements);
			_t = _t.getFirstChild();
			identifier(_t,false);
			_t = _retTree;
			{
			_loop51:
			do {
				if (_t==null) _t=ASTNULL;
				if ((_t.getType()==COMMA)) {
					JavaAST tmp25_AST_in = (JavaAST)_t;
					match(_t,COMMA);
					_t = _t.getNextSibling();
					identifier(_t,false);
					_t = _retTree;
				}
				else {
					break _loop51;
				}
				
			} while (true);
			}
			_t = __t49;
			_t = _t.getNextSibling();
		}
		catch (RecognitionException ex) {
			reportError(ex);
			if (_t!=null) {_t = _t.getNextSibling();}
		}
		_retTree = _t;
	}
	
	public final void objBlock(AST _t) throws RecognitionException {
		
		JavaAST objBlock_AST_in = (_t == ASTNULL) ? null : (JavaAST)_t;
		JavaAST s = null;
		
		try {      // for error handling
			AST __t57 = _t;
			JavaAST tmp26_AST_in = (JavaAST)_t;
			match(_t,OBJBLOCK);
			_t = _t.getFirstChild();
			tmp26_AST_in.print(out);
			{
			_loop61:
			do {
				if (_t==null) _t=ASTNULL;
				switch ( _t.getType()) {
				case CTOR_DEF:
				{
					ctorDef(_t);
					_t = _retTree;
					break;
				}
				case METHOD_DEF:
				{
					methodDef(_t);
					_t = _retTree;
					break;
				}
				case VARIABLE_DEFS:
				{
					variableDefs(_t);
					_t = _retTree;
					break;
				}
				case SEMI:
				case LITERAL_class:
				case LITERAL_interface:
				{
					typeDefinition(_t);
					_t = _retTree;
					break;
				}
				case LITERAL_static:
				{
					AST __t59 = _t;
					s = _t==ASTNULL ? null :(JavaAST)_t;
					match(_t,LITERAL_static);
					_t = _t.getFirstChild();
					s.print(out);
					slist(_t);
					_t = _retTree;
					_t = __t59;
					_t = _t.getNextSibling();
					break;
				}
				case INSTANCE_INIT:
				{
					AST __t60 = _t;
					JavaAST tmp27_AST_in = (JavaAST)_t;
					match(_t,INSTANCE_INIT);
					_t = _t.getFirstChild();
					slist(_t);
					_t = _retTree;
					_t = __t60;
					_t = _t.getNextSibling();
					break;
				}
				default:
				{
					break _loop61;
				}
				}
			} while (true);
			}
			JavaAST tmp28_AST_in = (JavaAST)_t;
			match(_t,RCURLY);
			_t = _t.getNextSibling();
			tmp28_AST_in.print(out);
			_t = __t57;
			_t = _t.getNextSibling();
		}
		catch (RecognitionException ex) {
			reportError(ex);
			if (_t!=null) {_t = _t.getNextSibling();}
		}
		_retTree = _t;
	}
	
	public final void interfaceBlock(AST _t,
		boolean inner
	) throws RecognitionException {
		
		JavaAST interfaceBlock_AST_in = (_t == ASTNULL) ? null : (JavaAST)_t;
		
		try {      // for error handling
			AST __t53 = _t;
			JavaAST tmp29_AST_in = (JavaAST)_t;
			match(_t,OBJBLOCK);
			_t = _t.getFirstChild();
			{
			_loop55:
			do {
				if (_t==null) _t=ASTNULL;
				switch ( _t.getType()) {
				case METHOD_DEF:
				{
					methodDecl(_t,inner);
					_t = _retTree;
					break;
				}
				case VARIABLE_DEFS:
				{
					variableDefs(_t);
					_t = _retTree;
					break;
				}
				case SEMI:
				case LITERAL_class:
				case LITERAL_interface:
				{
					typeDefinition(_t);
					_t = _retTree;
					break;
				}
				default:
				{
					break _loop55;
				}
				}
			} while (true);
			}
			JavaAST tmp30_AST_in = (JavaAST)_t;
			match(_t,RCURLY);
			_t = _t.getNextSibling();
			_t = __t53;
			_t = _t.getNextSibling();
		}
		catch (RecognitionException ex) {
			reportError(ex);
			if (_t!=null) {_t = _t.getNextSibling();}
		}
		_retTree = _t;
	}
	
	public final void objBlockExcept(AST _t,
		boolean inner
	) throws RecognitionException {
		
		JavaAST objBlockExcept_AST_in = (_t == ASTNULL) ? null : (JavaAST)_t;
		
		try {      // for error handling
			AST __t63 = _t;
			JavaAST tmp31_AST_in = (JavaAST)_t;
			match(_t,OBJBLOCK);
			_t = _t.getFirstChild();
			{
			_loop67:
			do {
				if (_t==null) _t=ASTNULL;
				switch ( _t.getType()) {
				case CTOR_DEF:
				{
					ctorDefExcept(_t,inner);
					_t = _retTree;
					break;
				}
				case METHOD_DEF:
				{
					methodDefExcept(_t,inner);
					_t = _retTree;
					break;
				}
				case VARIABLE_DEFS:
				{
					variableDefsExcept(_t);
					_t = _retTree;
					break;
				}
				case SEMI:
				case LITERAL_class:
				case LITERAL_interface:
				{
					typeDefinitionExcept(_t,true);
					_t = _retTree;
					break;
				}
				case LITERAL_static:
				{
					AST __t65 = _t;
					JavaAST tmp32_AST_in = (JavaAST)_t;
					match(_t,LITERAL_static);
					_t = _t.getFirstChild();
					slistExcept(_t);
					_t = _retTree;
					_t = __t65;
					_t = _t.getNextSibling();
					break;
				}
				case INSTANCE_INIT:
				{
					AST __t66 = _t;
					JavaAST tmp33_AST_in = (JavaAST)_t;
					match(_t,INSTANCE_INIT);
					_t = _t.getFirstChild();
					slistExcept(_t);
					_t = _retTree;
					_t = __t66;
					_t = _t.getNextSibling();
					break;
				}
				default:
				{
					break _loop67;
				}
				}
			} while (true);
			}
			JavaAST tmp34_AST_in = (JavaAST)_t;
			match(_t,RCURLY);
			_t = _t.getNextSibling();
			_t = __t63;
			_t = _t.getNextSibling();
		}
		catch (RecognitionException ex) {
			reportError(ex);
			if (_t!=null) {_t = _t.getNextSibling();}
		}
		_retTree = _t;
	}
	
	public final void typeSpec(AST _t,
		boolean print
	) throws RecognitionException {
		
		JavaAST typeSpec_AST_in = (_t == ASTNULL) ? null : (JavaAST)_t;
		
		try {      // for error handling
			AST __t25 = _t;
			JavaAST tmp35_AST_in = (JavaAST)_t;
			match(_t,TYPE);
			_t = _t.getFirstChild();
			typeSpecArray(_t,print);
			_t = _retTree;
			_t = __t25;
			_t = _t.getNextSibling();
		}
		catch (RecognitionException ex) {
			reportError(ex);
			if (_t!=null) {_t = _t.getNextSibling();}
		}
		_retTree = _t;
	}
	
	public final void typeSpecArray(AST _t,
		boolean print
	) throws RecognitionException {
		
		JavaAST typeSpecArray_AST_in = (_t == ASTNULL) ? null : (JavaAST)_t;
		
		try {      // for error handling
			if (_t==null) _t=ASTNULL;
			switch ( _t.getType()) {
			case ARRAY_DECLARATOR:
			{
				AST __t29 = _t;
				JavaAST tmp36_AST_in = (JavaAST)_t;
				match(_t,ARRAY_DECLARATOR);
				_t = _t.getFirstChild();
				{
				if (_t==null) _t=ASTNULL;
				switch ( _t.getType()) {
				case ARRAY_DECLARATOR:
				case IDENT:
				case DOT:
				case LITERAL_void:
				case LITERAL_boolean:
				case LITERAL_byte:
				case LITERAL_char:
				case LITERAL_short:
				case LITERAL_int:
				case LITERAL_float:
				case LITERAL_long:
				case LITERAL_double:
				{
					typeSpecArray(_t,print);
					_t = _retTree;
					break;
				}
				case RBRACK:
				{
					break;
				}
				default:
				{
					throw new NoViableAltException(_t);
				}
				}
				}
				JavaAST tmp37_AST_in = (JavaAST)_t;
				match(_t,RBRACK);
				_t = _t.getNextSibling();
				
								if (print) {
									tmp36_AST_in.print(out);
									tmp37_AST_in.print(out);
								}
							
				_t = __t29;
				_t = _t.getNextSibling();
				break;
			}
			case IDENT:
			case DOT:
			case LITERAL_void:
			case LITERAL_boolean:
			case LITERAL_byte:
			case LITERAL_char:
			case LITERAL_short:
			case LITERAL_int:
			case LITERAL_float:
			case LITERAL_long:
			case LITERAL_double:
			{
				type(_t,print);
				_t = _retTree;
				break;
			}
			default:
			{
				throw new NoViableAltException(_t);
			}
			}
		}
		catch (RecognitionException ex) {
			reportError(ex);
			if (_t!=null) {_t = _t.getNextSibling();}
		}
		_retTree = _t;
	}
	
	public final void typeSpecType(AST _t) throws RecognitionException {
		
		JavaAST typeSpecType_AST_in = (_t == ASTNULL) ? null : (JavaAST)_t;
		
		try {      // for error handling
			AST __t27 = _t;
			JavaAST tmp38_AST_in = (JavaAST)_t;
			match(_t,TYPE);
			_t = _t.getFirstChild();
			typeSpecArrayType(_t);
			_t = _retTree;
			_t = __t27;
			_t = _t.getNextSibling();
		}
		catch (RecognitionException ex) {
			reportError(ex);
			if (_t!=null) {_t = _t.getNextSibling();}
		}
		_retTree = _t;
	}
	
	public final void typeSpecArrayType(AST _t) throws RecognitionException {
		
		JavaAST typeSpecArrayType_AST_in = (_t == ASTNULL) ? null : (JavaAST)_t;
		
		try {      // for error handling
			if (_t==null) _t=ASTNULL;
			switch ( _t.getType()) {
			case ARRAY_DECLARATOR:
			{
				AST __t32 = _t;
				JavaAST tmp39_AST_in = (JavaAST)_t;
				match(_t,ARRAY_DECLARATOR);
				_t = _t.getFirstChild();
				{
				if (_t==null) _t=ASTNULL;
				switch ( _t.getType()) {
				case ARRAY_DECLARATOR:
				case IDENT:
				case DOT:
				case LITERAL_void:
				case LITERAL_boolean:
				case LITERAL_byte:
				case LITERAL_char:
				case LITERAL_short:
				case LITERAL_int:
				case LITERAL_float:
				case LITERAL_long:
				case LITERAL_double:
				{
					typeSpecArrayType(_t);
					_t = _retTree;
					break;
				}
				case RBRACK:
				{
					break;
				}
				default:
				{
					throw new NoViableAltException(_t);
				}
				}
				}
				JavaAST tmp40_AST_in = (JavaAST)_t;
				match(_t,RBRACK);
				_t = _t.getNextSibling();
				_t = __t32;
				_t = _t.getNextSibling();
				break;
			}
			case IDENT:
			case DOT:
			case LITERAL_void:
			case LITERAL_boolean:
			case LITERAL_byte:
			case LITERAL_char:
			case LITERAL_short:
			case LITERAL_int:
			case LITERAL_float:
			case LITERAL_long:
			case LITERAL_double:
			{
				typeType(_t);
				_t = _retTree;
				break;
			}
			default:
			{
				throw new NoViableAltException(_t);
			}
			}
		}
		catch (RecognitionException ex) {
			reportError(ex);
			if (_t!=null) {_t = _t.getNextSibling();}
		}
		_retTree = _t;
	}
	
	public final void type(AST _t,
		boolean print
	) throws RecognitionException {
		
		JavaAST type_AST_in = (_t == ASTNULL) ? null : (JavaAST)_t;
		
		try {      // for error handling
			if (_t==null) _t=ASTNULL;
			switch ( _t.getType()) {
			case IDENT:
			case DOT:
			{
				identifier(_t,print);
				_t = _retTree;
				break;
			}
			case LITERAL_void:
			case LITERAL_boolean:
			case LITERAL_byte:
			case LITERAL_char:
			case LITERAL_short:
			case LITERAL_int:
			case LITERAL_float:
			case LITERAL_long:
			case LITERAL_double:
			{
				builtInType(_t,print);
				_t = _retTree;
				break;
			}
			default:
			{
				throw new NoViableAltException(_t);
			}
			}
		}
		catch (RecognitionException ex) {
			reportError(ex);
			if (_t!=null) {_t = _t.getNextSibling();}
		}
		_retTree = _t;
	}
	
	public final void typeType(AST _t) throws RecognitionException {
		
		JavaAST typeType_AST_in = (_t == ASTNULL) ? null : (JavaAST)_t;
		
		try {      // for error handling
			if (_t==null) _t=ASTNULL;
			switch ( _t.getType()) {
			case IDENT:
			case DOT:
			{
				identifierType(_t);
				_t = _retTree;
				break;
			}
			case LITERAL_void:
			case LITERAL_boolean:
			case LITERAL_byte:
			case LITERAL_char:
			case LITERAL_short:
			case LITERAL_int:
			case LITERAL_float:
			case LITERAL_long:
			case LITERAL_double:
			{
				builtInTypeType(_t);
				_t = _retTree;
				break;
			}
			default:
			{
				throw new NoViableAltException(_t);
			}
			}
		}
		catch (RecognitionException ex) {
			reportError(ex);
			if (_t!=null) {_t = _t.getNextSibling();}
		}
		_retTree = _t;
	}
	
	public final void builtInType(AST _t,
		boolean print
	) throws RecognitionException {
		
		JavaAST builtInType_AST_in = (_t == ASTNULL) ? null : (JavaAST)_t;
		JavaAST v = null;
		JavaAST b = null;
		JavaAST y = null;
		JavaAST c = null;
		JavaAST s = null;
		JavaAST i = null;
		JavaAST f = null;
		JavaAST l = null;
		JavaAST d = null;
		
		try {      // for error handling
			if (_t==null) _t=ASTNULL;
			switch ( _t.getType()) {
			case LITERAL_void:
			{
				v = (JavaAST)_t;
				match(_t,LITERAL_void);
				_t = _t.getNextSibling();
				if (print) v.print(out);
				break;
			}
			case LITERAL_boolean:
			{
				b = (JavaAST)_t;
				match(_t,LITERAL_boolean);
				_t = _t.getNextSibling();
				if (print) b.print(out);
				break;
			}
			case LITERAL_byte:
			{
				y = (JavaAST)_t;
				match(_t,LITERAL_byte);
				_t = _t.getNextSibling();
				if (print) y.print(out);
				break;
			}
			case LITERAL_char:
			{
				c = (JavaAST)_t;
				match(_t,LITERAL_char);
				_t = _t.getNextSibling();
				if (print) c.print(out);
				break;
			}
			case LITERAL_short:
			{
				s = (JavaAST)_t;
				match(_t,LITERAL_short);
				_t = _t.getNextSibling();
				if (print) s.print(out);
				break;
			}
			case LITERAL_int:
			{
				i = (JavaAST)_t;
				match(_t,LITERAL_int);
				_t = _t.getNextSibling();
				if (print) i.print(out);
				break;
			}
			case LITERAL_float:
			{
				f = (JavaAST)_t;
				match(_t,LITERAL_float);
				_t = _t.getNextSibling();
				if (print) f.print(out);
				break;
			}
			case LITERAL_long:
			{
				l = (JavaAST)_t;
				match(_t,LITERAL_long);
				_t = _t.getNextSibling();
				if (print) l.print(out);
				break;
			}
			case LITERAL_double:
			{
				d = (JavaAST)_t;
				match(_t,LITERAL_double);
				_t = _t.getNextSibling();
				if (print) d.print(out);
				break;
			}
			default:
			{
				throw new NoViableAltException(_t);
			}
			}
		}
		catch (RecognitionException ex) {
			reportError(ex);
			if (_t!=null) {_t = _t.getNextSibling();}
		}
		_retTree = _t;
	}
	
	public final void identifierType(AST _t) throws RecognitionException {
		
		JavaAST identifierType_AST_in = (_t == ASTNULL) ? null : (JavaAST)_t;
		
		try {      // for error handling
			{
			if (_t==null) _t=ASTNULL;
			switch ( _t.getType()) {
			case IDENT:
			{
				JavaAST tmp41_AST_in = (JavaAST)_t;
				match(_t,IDENT);
				_t = _t.getNextSibling();
				break;
			}
			case DOT:
			{
				AST __t148 = _t;
				JavaAST tmp42_AST_in = (JavaAST)_t;
				match(_t,DOT);
				_t = _t.getFirstChild();
				identifierType(_t);
				_t = _retTree;
				JavaAST tmp43_AST_in = (JavaAST)_t;
				match(_t,IDENT);
				_t = _t.getNextSibling();
				_t = __t148;
				_t = _t.getNextSibling();
				break;
			}
			default:
			{
				throw new NoViableAltException(_t);
			}
			}
			}
			identifier(identifierType_AST_in, true); printType(identifierType_AST_in);
		}
		catch (RecognitionException ex) {
			reportError(ex);
			if (_t!=null) {_t = _t.getNextSibling();}
		}
		_retTree = _t;
	}
	
	public final void builtInTypeType(AST _t) throws RecognitionException {
		
		JavaAST builtInTypeType_AST_in = (_t == ASTNULL) ? null : (JavaAST)_t;
		
		try {      // for error handling
			{
			if (_t==null) _t=ASTNULL;
			switch ( _t.getType()) {
			case LITERAL_void:
			{
				JavaAST tmp44_AST_in = (JavaAST)_t;
				match(_t,LITERAL_void);
				_t = _t.getNextSibling();
				break;
			}
			case LITERAL_boolean:
			{
				JavaAST tmp45_AST_in = (JavaAST)_t;
				match(_t,LITERAL_boolean);
				_t = _t.getNextSibling();
				break;
			}
			case LITERAL_byte:
			{
				JavaAST tmp46_AST_in = (JavaAST)_t;
				match(_t,LITERAL_byte);
				_t = _t.getNextSibling();
				break;
			}
			case LITERAL_char:
			{
				JavaAST tmp47_AST_in = (JavaAST)_t;
				match(_t,LITERAL_char);
				_t = _t.getNextSibling();
				break;
			}
			case LITERAL_short:
			{
				JavaAST tmp48_AST_in = (JavaAST)_t;
				match(_t,LITERAL_short);
				_t = _t.getNextSibling();
				break;
			}
			case LITERAL_int:
			{
				JavaAST tmp49_AST_in = (JavaAST)_t;
				match(_t,LITERAL_int);
				_t = _t.getNextSibling();
				break;
			}
			case LITERAL_float:
			{
				JavaAST tmp50_AST_in = (JavaAST)_t;
				match(_t,LITERAL_float);
				_t = _t.getNextSibling();
				break;
			}
			case LITERAL_long:
			{
				JavaAST tmp51_AST_in = (JavaAST)_t;
				match(_t,LITERAL_long);
				_t = _t.getNextSibling();
				break;
			}
			case LITERAL_double:
			{
				JavaAST tmp52_AST_in = (JavaAST)_t;
				match(_t,LITERAL_double);
				_t = _t.getNextSibling();
				break;
			}
			default:
			{
				throw new NoViableAltException(_t);
			}
			}
			}
			builtInType(builtInTypeType_AST_in, true); printType(builtInTypeType_AST_in);
		}
		catch (RecognitionException ex) {
			reportError(ex);
			if (_t!=null) {_t = _t.getNextSibling();}
		}
		_retTree = _t;
	}
	
	public final void modifier(AST _t,
		boolean print
	) throws RecognitionException {
		
		JavaAST modifier_AST_in = (_t == ASTNULL) ? null : (JavaAST)_t;
		JavaAST u = null;
		JavaAST p = null;
		JavaAST r = null;
		JavaAST s = null;
		JavaAST f = null;
		JavaAST y = null;
		JavaAST v = null;
		JavaAST t = null;
		JavaAST n = null;
		JavaAST a = null;
		JavaAST i = null;
		
		try {      // for error handling
			if (_t==null) _t=ASTNULL;
			switch ( _t.getType()) {
			case LITERAL_public:
			{
				u = (JavaAST)_t;
				match(_t,LITERAL_public);
				_t = _t.getNextSibling();
				if (print) u.print(out);
				break;
			}
			case LITERAL_private:
			{
				p = (JavaAST)_t;
				match(_t,LITERAL_private);
				_t = _t.getNextSibling();
				if (print) p.print(out);
				break;
			}
			case LITERAL_protected:
			{
				r = (JavaAST)_t;
				match(_t,LITERAL_protected);
				_t = _t.getNextSibling();
				if (print) r.print(out);
				break;
			}
			case LITERAL_static:
			{
				s = (JavaAST)_t;
				match(_t,LITERAL_static);
				_t = _t.getNextSibling();
				if (print) s.print(out);
				break;
			}
			case LITERAL_final:
			{
				f = (JavaAST)_t;
				match(_t,LITERAL_final);
				_t = _t.getNextSibling();
				if (print) f.print(out);
				break;
			}
			case LITERAL_synchronized:
			{
				y = (JavaAST)_t;
				match(_t,LITERAL_synchronized);
				_t = _t.getNextSibling();
				if (print) y.print(out);
				break;
			}
			case LITERAL_volatile:
			{
				v = (JavaAST)_t;
				match(_t,LITERAL_volatile);
				_t = _t.getNextSibling();
				if (print) v.print(out);
				break;
			}
			case LITERAL_transient:
			{
				t = (JavaAST)_t;
				match(_t,LITERAL_transient);
				_t = _t.getNextSibling();
				if (print) t.print(out);
				break;
			}
			case LITERAL_native:
			{
				n = (JavaAST)_t;
				match(_t,LITERAL_native);
				_t = _t.getNextSibling();
				if (print) n.print(out);
				break;
			}
			case LITERAL_abstract:
			{
				a = (JavaAST)_t;
				match(_t,LITERAL_abstract);
				_t = _t.getNextSibling();
				if (print) a.print(out);
				break;
			}
			case LITERAL_strictfp:
			{
				i = (JavaAST)_t;
				match(_t,LITERAL_strictfp);
				_t = _t.getNextSibling();
				if (print) i.print(out);
				break;
			}
			default:
			{
				throw new NoViableAltException(_t);
			}
			}
		}
		catch (RecognitionException ex) {
			reportError(ex);
			if (_t!=null) {_t = _t.getNextSibling();}
		}
		_retTree = _t;
	}
	
	public final void methodDecl(AST _t,
		boolean inner
	) throws RecognitionException {
		
		JavaAST methodDecl_AST_in = (_t == ASTNULL) ? null : (JavaAST)_t;
		
		try {      // for error handling
			AST __t73 = _t;
			JavaAST tmp53_AST_in = (JavaAST)_t;
			match(_t,METHOD_DEF);
			_t = _t.getFirstChild();
			modifiers(_t,false);
			_t = _retTree;
			typeSpec(_t,false);
			_t = _retTree;
			methodHeadExcept(_t,inner);
			_t = _retTree;
			JavaAST tmp54_AST_in = (JavaAST)_t;
			match(_t,SEMI);
			_t = _t.getNextSibling();
			_t = __t73;
			_t = _t.getNextSibling();
		}
		catch (RecognitionException ex) {
			reportError(ex);
			if (_t!=null) {_t = _t.getNextSibling();}
		}
		_retTree = _t;
	}
	
	public final void variableDefs(AST _t) throws RecognitionException {
		
		JavaAST variableDefs_AST_in = (_t == ASTNULL) ? null : (JavaAST)_t;
		
		try {      // for error handling
			AST __t81 = _t;
			JavaAST tmp55_AST_in = (JavaAST)_t;
			match(_t,VARIABLE_DEFS);
			_t = _t.getFirstChild();
			modifiers(_t,true);
			_t = _retTree;
			typeSpec(_t,true);
			_t = _retTree;
			variableDef(_t);
			_t = _retTree;
			{
			_loop83:
			do {
				if (_t==null) _t=ASTNULL;
				if ((_t.getType()==COMMA)) {
					JavaAST tmp56_AST_in = (JavaAST)_t;
					match(_t,COMMA);
					_t = _t.getNextSibling();
					tmp56_AST_in.print(out);
					variableDef(_t);
					_t = _retTree;
				}
				else {
					break _loop83;
				}
				
			} while (true);
			}
			JavaAST tmp57_AST_in = (JavaAST)_t;
			match(_t,SEMI);
			_t = _t.getNextSibling();
			tmp57_AST_in.print(out);
			_t = __t81;
			_t = _t.getNextSibling();
		}
		catch (RecognitionException ex) {
			reportError(ex);
			if (_t!=null) {_t = _t.getNextSibling();}
		}
		_retTree = _t;
	}
	
	public final void ctorDef(AST _t) throws RecognitionException {
		
		JavaAST ctorDef_AST_in = (_t == ASTNULL) ? null : (JavaAST)_t;
		
		try {      // for error handling
			AST __t69 = _t;
			JavaAST tmp58_AST_in = (JavaAST)_t;
			match(_t,CTOR_DEF);
			_t = _t.getFirstChild();
			modifiers(_t,true);
			_t = _retTree;
			methodHead(_t);
			_t = _retTree;
			slist(_t);
			_t = _retTree;
			_t = __t69;
			_t = _t.getNextSibling();
		}
		catch (RecognitionException ex) {
			reportError(ex);
			if (_t!=null) {_t = _t.getNextSibling();}
		}
		_retTree = _t;
	}
	
	public final void methodDef(AST _t) throws RecognitionException {
		
		JavaAST methodDef_AST_in = (_t == ASTNULL) ? null : (JavaAST)_t;
		
		try {      // for error handling
			AST __t75 = _t;
			JavaAST tmp59_AST_in = (JavaAST)_t;
			match(_t,METHOD_DEF);
			_t = _t.getFirstChild();
			modifiers(_t,true);
			_t = _retTree;
			typeSpec(_t,true);
			_t = _retTree;
			methodHead(_t);
			_t = _retTree;
			{
			if (_t==null) _t=ASTNULL;
			switch ( _t.getType()) {
			case SLIST:
			{
				slist(_t);
				_t = _retTree;
				break;
			}
			case SEMI:
			{
				JavaAST tmp60_AST_in = (JavaAST)_t;
				match(_t,SEMI);
				_t = _t.getNextSibling();
				tmp60_AST_in.print(out);
				break;
			}
			default:
			{
				throw new NoViableAltException(_t);
			}
			}
			}
			_t = __t75;
			_t = _t.getNextSibling();
		}
		catch (RecognitionException ex) {
			reportError(ex);
			if (_t!=null) {_t = _t.getNextSibling();}
		}
		_retTree = _t;
	}
	
	public final void slist(AST _t) throws RecognitionException {
		
		JavaAST slist_AST_in = (_t == ASTNULL) ? null : (JavaAST)_t;
		
		try {      // for error handling
			AST __t153 = _t;
			JavaAST tmp61_AST_in = (JavaAST)_t;
			match(_t,SLIST);
			_t = _t.getFirstChild();
			tmp61_AST_in.print(out);
			{
			_loop155:
			do {
				if (_t==null) _t=ASTNULL;
				if ((_tokenSet_0.member(_t.getType()))) {
					stat(_t);
					_t = _retTree;
				}
				else {
					break _loop155;
				}
				
			} while (true);
			}
			JavaAST tmp62_AST_in = (JavaAST)_t;
			match(_t,RCURLY);
			_t = _t.getNextSibling();
			tmp62_AST_in.print(out);
			_t = __t153;
			_t = _t.getNextSibling();
		}
		catch (RecognitionException ex) {
			reportError(ex);
			if (_t!=null) {_t = _t.getNextSibling();}
		}
		_retTree = _t;
	}
	
	public final void ctorDefExcept(AST _t,
		boolean inner
	) throws RecognitionException {
		
		JavaAST ctorDefExcept_AST_in = (_t == ASTNULL) ? null : (JavaAST)_t;
		
		try {      // for error handling
			AST __t71 = _t;
			JavaAST tmp63_AST_in = (JavaAST)_t;
			match(_t,CTOR_DEF);
			_t = _t.getFirstChild();
			modifiers(_t,false);
			_t = _retTree;
			methodHeadExcept(_t,inner);
			_t = _retTree;
			slistExcept(_t);
			_t = _retTree;
			_t = __t71;
			_t = _t.getNextSibling();
		}
		catch (RecognitionException ex) {
			reportError(ex);
			if (_t!=null) {_t = _t.getNextSibling();}
		}
		_retTree = _t;
	}
	
	public final void methodDefExcept(AST _t,
		boolean inner
	) throws RecognitionException {
		
		JavaAST methodDefExcept_AST_in = (_t == ASTNULL) ? null : (JavaAST)_t;
		
		try {      // for error handling
			AST __t78 = _t;
			JavaAST tmp64_AST_in = (JavaAST)_t;
			match(_t,METHOD_DEF);
			_t = _t.getFirstChild();
			modifiers(_t,false);
			_t = _retTree;
			typeSpec(_t,false);
			_t = _retTree;
			methodHeadExcept(_t,inner);
			_t = _retTree;
			{
			if (_t==null) _t=ASTNULL;
			switch ( _t.getType()) {
			case SLIST:
			{
				slistExcept(_t);
				_t = _retTree;
				break;
			}
			case SEMI:
			{
				JavaAST tmp65_AST_in = (JavaAST)_t;
				match(_t,SEMI);
				_t = _t.getNextSibling();
				break;
			}
			default:
			{
				throw new NoViableAltException(_t);
			}
			}
			}
			_t = __t78;
			_t = _t.getNextSibling();
		}
		catch (RecognitionException ex) {
			reportError(ex);
			if (_t!=null) {_t = _t.getNextSibling();}
		}
		_retTree = _t;
	}
	
	public final void variableDefsExcept(AST _t) throws RecognitionException {
		
		JavaAST variableDefsExcept_AST_in = (_t == ASTNULL) ? null : (JavaAST)_t;
		
		try {      // for error handling
			AST __t85 = _t;
			JavaAST tmp66_AST_in = (JavaAST)_t;
			match(_t,VARIABLE_DEFS);
			_t = _t.getFirstChild();
			modifiers(_t,false);
			_t = _retTree;
			typeSpec(_t,false);
			_t = _retTree;
			variableDefExcept(_t);
			_t = _retTree;
			{
			_loop87:
			do {
				if (_t==null) _t=ASTNULL;
				if ((_t.getType()==COMMA)) {
					JavaAST tmp67_AST_in = (JavaAST)_t;
					match(_t,COMMA);
					_t = _t.getNextSibling();
					variableDefExcept(_t);
					_t = _retTree;
				}
				else {
					break _loop87;
				}
				
			} while (true);
			}
			JavaAST tmp68_AST_in = (JavaAST)_t;
			match(_t,SEMI);
			_t = _t.getNextSibling();
			_t = __t85;
			_t = _t.getNextSibling();
				variableDefs(variableDefsExcept_AST_in);
						printExceptions((HasExceptions)variableDefsExcept_AST_in);
					
		}
		catch (RecognitionException ex) {
			reportError(ex);
			if (_t!=null) {_t = _t.getNextSibling();}
		}
		_retTree = _t;
	}
	
	public final void slistExcept(AST _t) throws RecognitionException {
		
		JavaAST slistExcept_AST_in = (_t == ASTNULL) ? null : (JavaAST)_t;
		
		try {      // for error handling
			AST __t157 = _t;
			JavaAST tmp69_AST_in = (JavaAST)_t;
			match(_t,SLIST);
			_t = _t.getFirstChild();
			{
			_loop159:
			do {
				if (_t==null) _t=ASTNULL;
				if ((_tokenSet_1.member(_t.getType()))) {
					statExcept(_t);
					_t = _retTree;
				}
				else {
					break _loop159;
				}
				
			} while (true);
			}
			JavaAST tmp70_AST_in = (JavaAST)_t;
			match(_t,RCURLY);
			_t = _t.getNextSibling();
			_t = __t157;
			_t = _t.getNextSibling();
		}
		catch (RecognitionException ex) {
			reportError(ex);
			if (_t!=null) {_t = _t.getNextSibling();}
		}
		_retTree = _t;
	}
	
	public final void methodHead(AST _t) throws RecognitionException {
		
		JavaAST methodHead_AST_in = (_t == ASTNULL) ? null : (JavaAST)_t;
		
		try {      // for error handling
			JavaAST tmp71_AST_in = (JavaAST)_t;
			match(_t,IDENT);
			_t = _t.getNextSibling();
			JavaAST tmp72_AST_in = (JavaAST)_t;
			match(_t,LPAREN);
			_t = _t.getNextSibling();
			tmp71_AST_in.print(out); tmp72_AST_in.print(out);
			AST __t129 = _t;
			JavaAST tmp73_AST_in = (JavaAST)_t;
			match(_t,PARAMETERS);
			_t = _t.getFirstChild();
			{
			if (_t==null) _t=ASTNULL;
			switch ( _t.getType()) {
			case PARAMETER_DEF:
			{
				parameterDef(_t);
				_t = _retTree;
				{
				_loop132:
				do {
					if (_t==null) _t=ASTNULL;
					if ((_t.getType()==COMMA)) {
						JavaAST tmp74_AST_in = (JavaAST)_t;
						match(_t,COMMA);
						_t = _t.getNextSibling();
						parameterDef(_t);
						_t = _retTree;
					}
					else {
						break _loop132;
					}
					
				} while (true);
				}
				break;
			}
			case 3:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(_t);
			}
			}
			}
			_t = __t129;
			_t = _t.getNextSibling();
			JavaAST tmp75_AST_in = (JavaAST)_t;
			match(_t,RPAREN);
			_t = _t.getNextSibling();
			tmp75_AST_in.print(out);
			declaratorBrackets(_t);
			_t = _retTree;
			{
			if (_t==null) _t=ASTNULL;
			switch ( _t.getType()) {
			case LITERAL_throws:
			{
				throwsClause(_t);
				_t = _retTree;
				break;
			}
			case SLIST:
			case SEMI:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(_t);
			}
			}
			}
		}
		catch (RecognitionException ex) {
			reportError(ex);
			if (_t!=null) {_t = _t.getNextSibling();}
		}
		_retTree = _t;
	}
	
	public final void methodHeadExcept(AST _t,
		boolean inner
	) throws RecognitionException {
		
		JavaAST methodHeadExcept_AST_in = (_t == ASTNULL) ? null : (JavaAST)_t;
		
		try {      // for error handling
			JavaAST tmp76_AST_in = (JavaAST)_t;
			match(_t,IDENT);
			_t = _t.getNextSibling();
			JavaAST tmp77_AST_in = (JavaAST)_t;
			match(_t,LPAREN);
			_t = _t.getNextSibling();
			if (inner) { tmp76_AST_in.print(out); tmp77_AST_in.print(out); }
			AST __t135 = _t;
			JavaAST tmp78_AST_in = (JavaAST)_t;
			match(_t,PARAMETERS);
			_t = _t.getFirstChild();
			{
			if (_t==null) _t=ASTNULL;
			switch ( _t.getType()) {
			case PARAMETER_DEF:
			{
				parameterDefExcept(_t);
				_t = _retTree;
				{
				_loop138:
				do {
					if (_t==null) _t=ASTNULL;
					if ((_t.getType()==COMMA)) {
						JavaAST tmp79_AST_in = (JavaAST)_t;
						match(_t,COMMA);
						_t = _t.getNextSibling();
						parameterDefExcept(_t);
						_t = _retTree;
					}
					else {
						break _loop138;
					}
					
				} while (true);
				}
				break;
			}
			case 3:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(_t);
			}
			}
			}
			_t = __t135;
			_t = _t.getNextSibling();
			JavaAST tmp80_AST_in = (JavaAST)_t;
			match(_t,RPAREN);
			_t = _t.getNextSibling();
			if (inner) tmp80_AST_in.print(out);
			declaratorBrackets(_t);
			_t = _retTree;
			{
			if (_t==null) _t=ASTNULL;
			switch ( _t.getType()) {
			case LITERAL_throws:
			{
				throwsClause(_t);
				_t = _retTree;
				break;
			}
			case SLIST:
			case SEMI:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(_t);
			}
			}
			}
		}
		catch (RecognitionException ex) {
			reportError(ex);
			if (_t!=null) {_t = _t.getNextSibling();}
		}
		_retTree = _t;
	}
	
	public final void variableDef(AST _t) throws RecognitionException {
		
		JavaAST variableDef_AST_in = (_t == ASTNULL) ? null : (JavaAST)_t;
		
		try {      // for error handling
			AST __t89 = _t;
			JavaAST tmp81_AST_in = (JavaAST)_t;
			match(_t,VARIABLE_DEF);
			_t = _t.getFirstChild();
			variableDeclarator(_t);
			_t = _retTree;
			{
			if (_t==null) _t=ASTNULL;
			switch ( _t.getType()) {
			case ASSIGN:
			{
				varInitializer(_t);
				_t = _retTree;
				break;
			}
			case 3:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(_t);
			}
			}
			}
			_t = __t89;
			_t = _t.getNextSibling();
		}
		catch (RecognitionException ex) {
			reportError(ex);
			if (_t!=null) {_t = _t.getNextSibling();}
		}
		_retTree = _t;
	}
	
	public final void variableDefExcept(AST _t) throws RecognitionException {
		
		JavaAST variableDefExcept_AST_in = (_t == ASTNULL) ? null : (JavaAST)_t;
		
		try {      // for error handling
			AST __t92 = _t;
			JavaAST tmp82_AST_in = (JavaAST)_t;
			match(_t,VARIABLE_DEF);
			_t = _t.getFirstChild();
			variableDeclaratorExcept(_t);
			_t = _retTree;
			{
			if (_t==null) _t=ASTNULL;
			switch ( _t.getType()) {
			case ASSIGN:
			{
				varInitializerExcept(_t);
				_t = _retTree;
				break;
			}
			case 3:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(_t);
			}
			}
			}
			_t = __t92;
			_t = _t.getNextSibling();
		}
		catch (RecognitionException ex) {
			reportError(ex);
			if (_t!=null) {_t = _t.getNextSibling();}
		}
		_retTree = _t;
	}
	
	public final void variableDeclarator(AST _t) throws RecognitionException {
		
		JavaAST variableDeclarator_AST_in = (_t == ASTNULL) ? null : (JavaAST)_t;
		
		try {      // for error handling
			JavaAST tmp83_AST_in = (JavaAST)_t;
			match(_t,IDENT);
			_t = _t.getNextSibling();
			tmp83_AST_in.print(out);
			declaratorBrackets(_t);
			_t = _retTree;
		}
		catch (RecognitionException ex) {
			reportError(ex);
			if (_t!=null) {_t = _t.getNextSibling();}
		}
		_retTree = _t;
	}
	
	public final void varInitializer(AST _t) throws RecognitionException {
		
		JavaAST varInitializer_AST_in = (_t == ASTNULL) ? null : (JavaAST)_t;
		
		try {      // for error handling
			AST __t103 = _t;
			JavaAST tmp84_AST_in = (JavaAST)_t;
			match(_t,ASSIGN);
			_t = _t.getFirstChild();
			tmp84_AST_in.print(out);
			initializer(_t);
			_t = _retTree;
			_t = __t103;
			_t = _t.getNextSibling();
		}
		catch (RecognitionException ex) {
			reportError(ex);
			if (_t!=null) {_t = _t.getNextSibling();}
		}
		_retTree = _t;
	}
	
	public final void variableDeclaratorExcept(AST _t) throws RecognitionException {
		
		JavaAST variableDeclaratorExcept_AST_in = (_t == ASTNULL) ? null : (JavaAST)_t;
		
		try {      // for error handling
			JavaAST tmp85_AST_in = (JavaAST)_t;
			match(_t,IDENT);
			_t = _t.getNextSibling();
			declaratorBracketsExcept(_t);
			_t = _retTree;
		}
		catch (RecognitionException ex) {
			reportError(ex);
			if (_t!=null) {_t = _t.getNextSibling();}
		}
		_retTree = _t;
	}
	
	public final void varInitializerExcept(AST _t) throws RecognitionException {
		
		JavaAST varInitializerExcept_AST_in = (_t == ASTNULL) ? null : (JavaAST)_t;
		
		try {      // for error handling
			AST __t105 = _t;
			JavaAST tmp86_AST_in = (JavaAST)_t;
			match(_t,ASSIGN);
			_t = _t.getFirstChild();
			initializerType(_t);
			_t = _retTree;
			_t = __t105;
			_t = _t.getNextSibling();
		}
		catch (RecognitionException ex) {
			reportError(ex);
			if (_t!=null) {_t = _t.getNextSibling();}
		}
		_retTree = _t;
	}
	
	public final void declaratorBrackets(AST _t) throws RecognitionException {
		
		JavaAST declaratorBrackets_AST_in = (_t == ASTNULL) ? null : (JavaAST)_t;
		JavaAST l = null;
		JavaAST r = null;
		
		try {      // for error handling
			{
			_loop98:
			do {
				if (_t==null) _t=ASTNULL;
				if ((_t.getType()==ARRAY_DECLARATOR)) {
					l = (JavaAST)_t;
					match(_t,ARRAY_DECLARATOR);
					_t = _t.getNextSibling();
					r = (JavaAST)_t;
					match(_t,RBRACK);
					_t = _t.getNextSibling();
					l.print(out); r.print(out);
				}
				else {
					break _loop98;
				}
				
			} while (true);
			}
		}
		catch (RecognitionException ex) {
			reportError(ex);
			if (_t!=null) {_t = _t.getNextSibling();}
		}
		_retTree = _t;
	}
	
	public final void declaratorBracketsExcept(AST _t) throws RecognitionException {
		
		JavaAST declaratorBracketsExcept_AST_in = (_t == ASTNULL) ? null : (JavaAST)_t;
		
		try {      // for error handling
			{
			_loop101:
			do {
				if (_t==null) _t=ASTNULL;
				if ((_t.getType()==ARRAY_DECLARATOR)) {
					JavaAST tmp87_AST_in = (JavaAST)_t;
					match(_t,ARRAY_DECLARATOR);
					_t = _t.getNextSibling();
					JavaAST tmp88_AST_in = (JavaAST)_t;
					match(_t,RBRACK);
					_t = _t.getNextSibling();
				}
				else {
					break _loop101;
				}
				
			} while (true);
			}
		}
		catch (RecognitionException ex) {
			reportError(ex);
			if (_t!=null) {_t = _t.getNextSibling();}
		}
		_retTree = _t;
	}
	
	public final void initializer(AST _t) throws RecognitionException {
		
		JavaAST initializer_AST_in = (_t == ASTNULL) ? null : (JavaAST)_t;
		
		try {      // for error handling
			if (_t==null) _t=ASTNULL;
			switch ( _t.getType()) {
			case TYPE:
			case CONCAT_ASSIGN:
			case CONCATENATION:
			case UNARY_MINUS:
			case UNARY_PLUS:
			case TYPECAST:
			case INDEX_OP:
			case METHOD_CALL:
			case CONSTRUCTOR_CALL:
			case POST_INC:
			case POST_DEC:
			case PAREN_EXPR:
			case IDENT:
			case DOT:
			case STAR:
			case ASSIGN:
			case PLUS_ASSIGN:
			case MINUS_ASSIGN:
			case STAR_ASSIGN:
			case DIV_ASSIGN:
			case MOD_ASSIGN:
			case SR_ASSIGN:
			case BSR_ASSIGN:
			case SL_ASSIGN:
			case BAND_ASSIGN:
			case BXOR_ASSIGN:
			case BOR_ASSIGN:
			case QUESTION:
			case LOR:
			case LAND:
			case BOR:
			case BXOR:
			case BAND:
			case NOT_EQUAL:
			case EQUAL:
			case LT:
			case GT:
			case LE:
			case GE:
			case LITERAL_instanceof:
			case SL:
			case SR:
			case BSR:
			case PLUS:
			case MINUS:
			case DIV:
			case MOD:
			case INC:
			case DEC:
			case BNOT:
			case LNOT:
			case LITERAL_this:
			case LITERAL_super:
			case LITERAL_true:
			case LITERAL_false:
			case LITERAL_null:
			case LITERAL_new:
			case NUM_INT:
			case CHAR_LITERAL:
			case STRING_LITERAL:
			case NUM_FLOAT:
			{
				expression(_t);
				_t = _retTree;
				break;
			}
			case ARRAY_INIT:
			{
				arrayInitializer(_t);
				_t = _retTree;
				break;
			}
			default:
			{
				throw new NoViableAltException(_t);
			}
			}
		}
		catch (RecognitionException ex) {
			reportError(ex);
			if (_t!=null) {_t = _t.getNextSibling();}
		}
		_retTree = _t;
	}
	
	public final void initializerType(AST _t) throws RecognitionException {
		
		JavaAST initializerType_AST_in = (_t == ASTNULL) ? null : (JavaAST)_t;
		
		try {      // for error handling
			if (_t==null) _t=ASTNULL;
			switch ( _t.getType()) {
			case TYPE:
			case CONCAT_ASSIGN:
			case CONCATENATION:
			case UNARY_MINUS:
			case UNARY_PLUS:
			case TYPECAST:
			case INDEX_OP:
			case METHOD_CALL:
			case CONSTRUCTOR_CALL:
			case POST_INC:
			case POST_DEC:
			case PAREN_EXPR:
			case IDENT:
			case DOT:
			case STAR:
			case ASSIGN:
			case PLUS_ASSIGN:
			case MINUS_ASSIGN:
			case STAR_ASSIGN:
			case DIV_ASSIGN:
			case MOD_ASSIGN:
			case SR_ASSIGN:
			case BSR_ASSIGN:
			case SL_ASSIGN:
			case BAND_ASSIGN:
			case BXOR_ASSIGN:
			case BOR_ASSIGN:
			case QUESTION:
			case LOR:
			case LAND:
			case BOR:
			case BXOR:
			case BAND:
			case NOT_EQUAL:
			case EQUAL:
			case LT:
			case GT:
			case LE:
			case GE:
			case LITERAL_instanceof:
			case SL:
			case SR:
			case BSR:
			case PLUS:
			case MINUS:
			case DIV:
			case MOD:
			case INC:
			case DEC:
			case BNOT:
			case LNOT:
			case LITERAL_this:
			case LITERAL_super:
			case LITERAL_true:
			case LITERAL_false:
			case LITERAL_null:
			case LITERAL_new:
			case NUM_INT:
			case CHAR_LITERAL:
			case STRING_LITERAL:
			case NUM_FLOAT:
			{
				expressionType(_t);
				_t = _retTree;
				break;
			}
			case ARRAY_INIT:
			{
				arrayInitializerType(_t);
				_t = _retTree;
				break;
			}
			default:
			{
				throw new NoViableAltException(_t);
			}
			}
		}
		catch (RecognitionException ex) {
			reportError(ex);
			if (_t!=null) {_t = _t.getNextSibling();}
		}
		_retTree = _t;
	}
	
	public final void parameterDef(AST _t) throws RecognitionException {
		
		JavaAST parameterDef_AST_in = (_t == ASTNULL) ? null : (JavaAST)_t;
		
		try {      // for error handling
			AST __t107 = _t;
			JavaAST tmp89_AST_in = (JavaAST)_t;
			match(_t,PARAMETER_DEF);
			_t = _t.getFirstChild();
			modifiers(_t,true);
			_t = _retTree;
			typeSpec(_t,true);
			_t = _retTree;
			JavaAST tmp90_AST_in = (JavaAST)_t;
			match(_t,IDENT);
			_t = _t.getNextSibling();
			tmp90_AST_in.print(out);
			declaratorBrackets(_t);
			_t = _retTree;
			_t = __t107;
			_t = _t.getNextSibling();
		}
		catch (RecognitionException ex) {
			reportError(ex);
			if (_t!=null) {_t = _t.getNextSibling();}
		}
		_retTree = _t;
	}
	
	public final void parameterDefExcept(AST _t) throws RecognitionException {
		
		JavaAST parameterDefExcept_AST_in = (_t == ASTNULL) ? null : (JavaAST)_t;
		
		try {      // for error handling
			AST __t109 = _t;
			JavaAST tmp91_AST_in = (JavaAST)_t;
			match(_t,PARAMETER_DEF);
			_t = _t.getFirstChild();
			modifiers(_t,false);
			_t = _retTree;
			typeSpec(_t,false);
			_t = _retTree;
			JavaAST tmp92_AST_in = (JavaAST)_t;
			match(_t,IDENT);
			_t = _t.getNextSibling();
			declaratorBrackets(_t);
			_t = _retTree;
			_t = __t109;
			_t = _t.getNextSibling();
		}
		catch (RecognitionException ex) {
			reportError(ex);
			if (_t!=null) {_t = _t.getNextSibling();}
		}
		_retTree = _t;
	}
	
	public final void expression(AST _t) throws RecognitionException {
		
		JavaAST expression_AST_in = (_t == ASTNULL) ? null : (JavaAST)_t;
		JavaAST i = null;
		
		try {      // for error handling
			if (_t==null) _t=ASTNULL;
			switch ( _t.getType()) {
			case QUESTION:
			{
				AST __t253 = _t;
				JavaAST tmp93_AST_in = (JavaAST)_t;
				match(_t,QUESTION);
				_t = _t.getFirstChild();
				expression(_t);
				_t = _retTree;
				tmp93_AST_in.print(out);
				expression(_t);
				_t = _retTree;
				JavaAST tmp94_AST_in = (JavaAST)_t;
				match(_t,COLON);
				_t = _t.getNextSibling();
				tmp94_AST_in.print(out);
				expression(_t);
				_t = _retTree;
				_t = __t253;
				_t = _t.getNextSibling();
				break;
			}
			case ASSIGN:
			{
				AST __t254 = _t;
				JavaAST tmp95_AST_in = (JavaAST)_t;
				match(_t,ASSIGN);
				_t = _t.getFirstChild();
				expression(_t);
				_t = _retTree;
				tmp95_AST_in.print(out);
				expression(_t);
				_t = _retTree;
				_t = __t254;
				_t = _t.getNextSibling();
				break;
			}
			case PLUS_ASSIGN:
			{
				AST __t255 = _t;
				JavaAST tmp96_AST_in = (JavaAST)_t;
				match(_t,PLUS_ASSIGN);
				_t = _t.getFirstChild();
				expression(_t);
				_t = _retTree;
				tmp96_AST_in.print(out);
				expression(_t);
				_t = _retTree;
				_t = __t255;
				_t = _t.getNextSibling();
				break;
			}
			case CONCAT_ASSIGN:
			{
				AST __t256 = _t;
				JavaAST tmp97_AST_in = (JavaAST)_t;
				match(_t,CONCAT_ASSIGN);
				_t = _t.getFirstChild();
				expression(_t);
				_t = _retTree;
				tmp97_AST_in.print(out);
				expression(_t);
				_t = _retTree;
				_t = __t256;
				_t = _t.getNextSibling();
				break;
			}
			case MINUS_ASSIGN:
			{
				AST __t257 = _t;
				JavaAST tmp98_AST_in = (JavaAST)_t;
				match(_t,MINUS_ASSIGN);
				_t = _t.getFirstChild();
				expression(_t);
				_t = _retTree;
				tmp98_AST_in.print(out);
				expression(_t);
				_t = _retTree;
				_t = __t257;
				_t = _t.getNextSibling();
				break;
			}
			case STAR_ASSIGN:
			{
				AST __t258 = _t;
				JavaAST tmp99_AST_in = (JavaAST)_t;
				match(_t,STAR_ASSIGN);
				_t = _t.getFirstChild();
				expression(_t);
				_t = _retTree;
				tmp99_AST_in.print(out);
				expression(_t);
				_t = _retTree;
				_t = __t258;
				_t = _t.getNextSibling();
				break;
			}
			case DIV_ASSIGN:
			{
				AST __t259 = _t;
				JavaAST tmp100_AST_in = (JavaAST)_t;
				match(_t,DIV_ASSIGN);
				_t = _t.getFirstChild();
				expression(_t);
				_t = _retTree;
				tmp100_AST_in.print(out);
				expression(_t);
				_t = _retTree;
				_t = __t259;
				_t = _t.getNextSibling();
				break;
			}
			case MOD_ASSIGN:
			{
				AST __t260 = _t;
				JavaAST tmp101_AST_in = (JavaAST)_t;
				match(_t,MOD_ASSIGN);
				_t = _t.getFirstChild();
				expression(_t);
				_t = _retTree;
				tmp101_AST_in.print(out);
				expression(_t);
				_t = _retTree;
				_t = __t260;
				_t = _t.getNextSibling();
				break;
			}
			case SR_ASSIGN:
			{
				AST __t261 = _t;
				JavaAST tmp102_AST_in = (JavaAST)_t;
				match(_t,SR_ASSIGN);
				_t = _t.getFirstChild();
				expression(_t);
				_t = _retTree;
				tmp102_AST_in.print(out);
				expression(_t);
				_t = _retTree;
				_t = __t261;
				_t = _t.getNextSibling();
				break;
			}
			case BSR_ASSIGN:
			{
				AST __t262 = _t;
				JavaAST tmp103_AST_in = (JavaAST)_t;
				match(_t,BSR_ASSIGN);
				_t = _t.getFirstChild();
				expression(_t);
				_t = _retTree;
				tmp103_AST_in.print(out);
				expression(_t);
				_t = _retTree;
				_t = __t262;
				_t = _t.getNextSibling();
				break;
			}
			case SL_ASSIGN:
			{
				AST __t263 = _t;
				JavaAST tmp104_AST_in = (JavaAST)_t;
				match(_t,SL_ASSIGN);
				_t = _t.getFirstChild();
				expression(_t);
				_t = _retTree;
				tmp104_AST_in.print(out);
				expression(_t);
				_t = _retTree;
				_t = __t263;
				_t = _t.getNextSibling();
				break;
			}
			case BAND_ASSIGN:
			{
				AST __t264 = _t;
				JavaAST tmp105_AST_in = (JavaAST)_t;
				match(_t,BAND_ASSIGN);
				_t = _t.getFirstChild();
				expression(_t);
				_t = _retTree;
				tmp105_AST_in.print(out);
				expression(_t);
				_t = _retTree;
				_t = __t264;
				_t = _t.getNextSibling();
				break;
			}
			case BXOR_ASSIGN:
			{
				AST __t265 = _t;
				JavaAST tmp106_AST_in = (JavaAST)_t;
				match(_t,BXOR_ASSIGN);
				_t = _t.getFirstChild();
				expression(_t);
				_t = _retTree;
				tmp106_AST_in.print(out);
				expression(_t);
				_t = _retTree;
				_t = __t265;
				_t = _t.getNextSibling();
				break;
			}
			case BOR_ASSIGN:
			{
				AST __t266 = _t;
				JavaAST tmp107_AST_in = (JavaAST)_t;
				match(_t,BOR_ASSIGN);
				_t = _t.getFirstChild();
				expression(_t);
				_t = _retTree;
				tmp107_AST_in.print(out);
				expression(_t);
				_t = _retTree;
				_t = __t266;
				_t = _t.getNextSibling();
				break;
			}
			case LOR:
			{
				AST __t267 = _t;
				JavaAST tmp108_AST_in = (JavaAST)_t;
				match(_t,LOR);
				_t = _t.getFirstChild();
				expression(_t);
				_t = _retTree;
				tmp108_AST_in.print(out);
				expression(_t);
				_t = _retTree;
				_t = __t267;
				_t = _t.getNextSibling();
				break;
			}
			case LAND:
			{
				AST __t268 = _t;
				JavaAST tmp109_AST_in = (JavaAST)_t;
				match(_t,LAND);
				_t = _t.getFirstChild();
				expression(_t);
				_t = _retTree;
				tmp109_AST_in.print(out);
				expression(_t);
				_t = _retTree;
				_t = __t268;
				_t = _t.getNextSibling();
				break;
			}
			case BOR:
			{
				AST __t269 = _t;
				JavaAST tmp110_AST_in = (JavaAST)_t;
				match(_t,BOR);
				_t = _t.getFirstChild();
				expression(_t);
				_t = _retTree;
				tmp110_AST_in.print(out);
				expression(_t);
				_t = _retTree;
				_t = __t269;
				_t = _t.getNextSibling();
				break;
			}
			case BXOR:
			{
				AST __t270 = _t;
				JavaAST tmp111_AST_in = (JavaAST)_t;
				match(_t,BXOR);
				_t = _t.getFirstChild();
				expression(_t);
				_t = _retTree;
				tmp111_AST_in.print(out);
				expression(_t);
				_t = _retTree;
				_t = __t270;
				_t = _t.getNextSibling();
				break;
			}
			case BAND:
			{
				AST __t271 = _t;
				JavaAST tmp112_AST_in = (JavaAST)_t;
				match(_t,BAND);
				_t = _t.getFirstChild();
				expression(_t);
				_t = _retTree;
				tmp112_AST_in.print(out);
				expression(_t);
				_t = _retTree;
				_t = __t271;
				_t = _t.getNextSibling();
				break;
			}
			case NOT_EQUAL:
			{
				AST __t272 = _t;
				JavaAST tmp113_AST_in = (JavaAST)_t;
				match(_t,NOT_EQUAL);
				_t = _t.getFirstChild();
				expression(_t);
				_t = _retTree;
				tmp113_AST_in.print(out);
				expression(_t);
				_t = _retTree;
				_t = __t272;
				_t = _t.getNextSibling();
				break;
			}
			case EQUAL:
			{
				AST __t273 = _t;
				JavaAST tmp114_AST_in = (JavaAST)_t;
				match(_t,EQUAL);
				_t = _t.getFirstChild();
				expression(_t);
				_t = _retTree;
				tmp114_AST_in.print(out);
				expression(_t);
				_t = _retTree;
				_t = __t273;
				_t = _t.getNextSibling();
				break;
			}
			case LT:
			{
				AST __t274 = _t;
				JavaAST tmp115_AST_in = (JavaAST)_t;
				match(_t,LT);
				_t = _t.getFirstChild();
				expression(_t);
				_t = _retTree;
				tmp115_AST_in.print(out);
				expression(_t);
				_t = _retTree;
				_t = __t274;
				_t = _t.getNextSibling();
				break;
			}
			case GT:
			{
				AST __t275 = _t;
				JavaAST tmp116_AST_in = (JavaAST)_t;
				match(_t,GT);
				_t = _t.getFirstChild();
				expression(_t);
				_t = _retTree;
				tmp116_AST_in.print(out);
				expression(_t);
				_t = _retTree;
				_t = __t275;
				_t = _t.getNextSibling();
				break;
			}
			case LE:
			{
				AST __t276 = _t;
				JavaAST tmp117_AST_in = (JavaAST)_t;
				match(_t,LE);
				_t = _t.getFirstChild();
				expression(_t);
				_t = _retTree;
				tmp117_AST_in.print(out);
				expression(_t);
				_t = _retTree;
				_t = __t276;
				_t = _t.getNextSibling();
				break;
			}
			case GE:
			{
				AST __t277 = _t;
				JavaAST tmp118_AST_in = (JavaAST)_t;
				match(_t,GE);
				_t = _t.getFirstChild();
				expression(_t);
				_t = _retTree;
				tmp118_AST_in.print(out);
				expression(_t);
				_t = _retTree;
				_t = __t277;
				_t = _t.getNextSibling();
				break;
			}
			case SL:
			{
				AST __t278 = _t;
				JavaAST tmp119_AST_in = (JavaAST)_t;
				match(_t,SL);
				_t = _t.getFirstChild();
				expression(_t);
				_t = _retTree;
				tmp119_AST_in.print(out);
				expression(_t);
				_t = _retTree;
				_t = __t278;
				_t = _t.getNextSibling();
				break;
			}
			case SR:
			{
				AST __t279 = _t;
				JavaAST tmp120_AST_in = (JavaAST)_t;
				match(_t,SR);
				_t = _t.getFirstChild();
				expression(_t);
				_t = _retTree;
				tmp120_AST_in.print(out);
				expression(_t);
				_t = _retTree;
				_t = __t279;
				_t = _t.getNextSibling();
				break;
			}
			case BSR:
			{
				AST __t280 = _t;
				JavaAST tmp121_AST_in = (JavaAST)_t;
				match(_t,BSR);
				_t = _t.getFirstChild();
				expression(_t);
				_t = _retTree;
				tmp121_AST_in.print(out);
				expression(_t);
				_t = _retTree;
				_t = __t280;
				_t = _t.getNextSibling();
				break;
			}
			case PLUS:
			{
				AST __t281 = _t;
				JavaAST tmp122_AST_in = (JavaAST)_t;
				match(_t,PLUS);
				_t = _t.getFirstChild();
				expression(_t);
				_t = _retTree;
				tmp122_AST_in.print(out);
				expression(_t);
				_t = _retTree;
				_t = __t281;
				_t = _t.getNextSibling();
				break;
			}
			case CONCATENATION:
			{
				AST __t282 = _t;
				JavaAST tmp123_AST_in = (JavaAST)_t;
				match(_t,CONCATENATION);
				_t = _t.getFirstChild();
				expression(_t);
				_t = _retTree;
				tmp123_AST_in.print(out);
				expression(_t);
				_t = _retTree;
				_t = __t282;
				_t = _t.getNextSibling();
				break;
			}
			case MINUS:
			{
				AST __t283 = _t;
				JavaAST tmp124_AST_in = (JavaAST)_t;
				match(_t,MINUS);
				_t = _t.getFirstChild();
				expression(_t);
				_t = _retTree;
				tmp124_AST_in.print(out);
				expression(_t);
				_t = _retTree;
				_t = __t283;
				_t = _t.getNextSibling();
				break;
			}
			case DIV:
			{
				AST __t284 = _t;
				JavaAST tmp125_AST_in = (JavaAST)_t;
				match(_t,DIV);
				_t = _t.getFirstChild();
				expression(_t);
				_t = _retTree;
				tmp125_AST_in.print(out);
				expression(_t);
				_t = _retTree;
				_t = __t284;
				_t = _t.getNextSibling();
				break;
			}
			case MOD:
			{
				AST __t285 = _t;
				JavaAST tmp126_AST_in = (JavaAST)_t;
				match(_t,MOD);
				_t = _t.getFirstChild();
				expression(_t);
				_t = _retTree;
				tmp126_AST_in.print(out);
				expression(_t);
				_t = _retTree;
				_t = __t285;
				_t = _t.getNextSibling();
				break;
			}
			case STAR:
			{
				AST __t286 = _t;
				JavaAST tmp127_AST_in = (JavaAST)_t;
				match(_t,STAR);
				_t = _t.getFirstChild();
				expression(_t);
				_t = _retTree;
				tmp127_AST_in.print(out);
				expression(_t);
				_t = _retTree;
				_t = __t286;
				_t = _t.getNextSibling();
				break;
			}
			case INC:
			{
				AST __t287 = _t;
				JavaAST tmp128_AST_in = (JavaAST)_t;
				match(_t,INC);
				_t = _t.getFirstChild();
				tmp128_AST_in.print(out);
				expression(_t);
				_t = _retTree;
				_t = __t287;
				_t = _t.getNextSibling();
				break;
			}
			case DEC:
			{
				AST __t288 = _t;
				JavaAST tmp129_AST_in = (JavaAST)_t;
				match(_t,DEC);
				_t = _t.getFirstChild();
				tmp129_AST_in.print(out);
				expression(_t);
				_t = _retTree;
				_t = __t288;
				_t = _t.getNextSibling();
				break;
			}
			case POST_INC:
			{
				AST __t289 = _t;
				JavaAST tmp130_AST_in = (JavaAST)_t;
				match(_t,POST_INC);
				_t = _t.getFirstChild();
				expression(_t);
				_t = _retTree;
				tmp130_AST_in.print(out);
				_t = __t289;
				_t = _t.getNextSibling();
				break;
			}
			case POST_DEC:
			{
				AST __t290 = _t;
				JavaAST tmp131_AST_in = (JavaAST)_t;
				match(_t,POST_DEC);
				_t = _t.getFirstChild();
				expression(_t);
				_t = _retTree;
				tmp131_AST_in.print(out);
				_t = __t290;
				_t = _t.getNextSibling();
				break;
			}
			case BNOT:
			{
				AST __t291 = _t;
				JavaAST tmp132_AST_in = (JavaAST)_t;
				match(_t,BNOT);
				_t = _t.getFirstChild();
				tmp132_AST_in.print(out);
				expression(_t);
				_t = _retTree;
				_t = __t291;
				_t = _t.getNextSibling();
				break;
			}
			case LNOT:
			{
				AST __t292 = _t;
				JavaAST tmp133_AST_in = (JavaAST)_t;
				match(_t,LNOT);
				_t = _t.getFirstChild();
				tmp133_AST_in.print(out);
				expression(_t);
				_t = _retTree;
				_t = __t292;
				_t = _t.getNextSibling();
				break;
			}
			case LITERAL_instanceof:
			{
				AST __t293 = _t;
				i = _t==ASTNULL ? null :(JavaAST)_t;
				match(_t,LITERAL_instanceof);
				_t = _t.getFirstChild();
				expression(_t);
				_t = _retTree;
				i.print(out);
				expression(_t);
				_t = _retTree;
				_t = __t293;
				_t = _t.getNextSibling();
				break;
			}
			case UNARY_MINUS:
			{
				AST __t294 = _t;
				JavaAST tmp134_AST_in = (JavaAST)_t;
				match(_t,UNARY_MINUS);
				_t = _t.getFirstChild();
				tmp134_AST_in.print(out);
				expression(_t);
				_t = _retTree;
				_t = __t294;
				_t = _t.getNextSibling();
				break;
			}
			case UNARY_PLUS:
			{
				AST __t295 = _t;
				JavaAST tmp135_AST_in = (JavaAST)_t;
				match(_t,UNARY_PLUS);
				_t = _t.getFirstChild();
				tmp135_AST_in.print(out);
				expression(_t);
				_t = _retTree;
				_t = __t295;
				_t = _t.getNextSibling();
				break;
			}
			case TYPE:
			case TYPECAST:
			case INDEX_OP:
			case METHOD_CALL:
			case CONSTRUCTOR_CALL:
			case PAREN_EXPR:
			case IDENT:
			case DOT:
			case LITERAL_this:
			case LITERAL_super:
			case LITERAL_true:
			case LITERAL_false:
			case LITERAL_null:
			case LITERAL_new:
			case NUM_INT:
			case CHAR_LITERAL:
			case STRING_LITERAL:
			case NUM_FLOAT:
			{
				primaryExpression(_t);
				_t = _retTree;
				break;
			}
			default:
			{
				throw new NoViableAltException(_t);
			}
			}
		}
		catch (RecognitionException ex) {
			reportError(ex);
			if (_t!=null) {_t = _t.getNextSibling();}
		}
		_retTree = _t;
	}
	
	public final void arrayInitializer(AST _t) throws RecognitionException {
		
		JavaAST arrayInitializer_AST_in = (_t == ASTNULL) ? null : (JavaAST)_t;
		JavaAST a = null;
		JavaAST r = null;
		
		try {      // for error handling
			AST __t113 = _t;
			a = _t==ASTNULL ? null :(JavaAST)_t;
			match(_t,ARRAY_INIT);
			_t = _t.getFirstChild();
			a.print(out);
			{
			if (_t==null) _t=ASTNULL;
			switch ( _t.getType()) {
			case TYPE:
			case ARRAY_INIT:
			case CONCAT_ASSIGN:
			case CONCATENATION:
			case UNARY_MINUS:
			case UNARY_PLUS:
			case TYPECAST:
			case INDEX_OP:
			case METHOD_CALL:
			case CONSTRUCTOR_CALL:
			case POST_INC:
			case POST_DEC:
			case PAREN_EXPR:
			case IDENT:
			case DOT:
			case STAR:
			case ASSIGN:
			case PLUS_ASSIGN:
			case MINUS_ASSIGN:
			case STAR_ASSIGN:
			case DIV_ASSIGN:
			case MOD_ASSIGN:
			case SR_ASSIGN:
			case BSR_ASSIGN:
			case SL_ASSIGN:
			case BAND_ASSIGN:
			case BXOR_ASSIGN:
			case BOR_ASSIGN:
			case QUESTION:
			case LOR:
			case LAND:
			case BOR:
			case BXOR:
			case BAND:
			case NOT_EQUAL:
			case EQUAL:
			case LT:
			case GT:
			case LE:
			case GE:
			case LITERAL_instanceof:
			case SL:
			case SR:
			case BSR:
			case PLUS:
			case MINUS:
			case DIV:
			case MOD:
			case INC:
			case DEC:
			case BNOT:
			case LNOT:
			case LITERAL_this:
			case LITERAL_super:
			case LITERAL_true:
			case LITERAL_false:
			case LITERAL_null:
			case LITERAL_new:
			case NUM_INT:
			case CHAR_LITERAL:
			case STRING_LITERAL:
			case NUM_FLOAT:
			{
				initializer(_t);
				_t = _retTree;
				{
				if (_t==null) _t=ASTNULL;
				switch ( _t.getType()) {
				case COMMA:
				{
					commaInitializer(_t);
					_t = _retTree;
					break;
				}
				case RCURLY:
				{
					break;
				}
				default:
				{
					throw new NoViableAltException(_t);
				}
				}
				}
				break;
			}
			case RCURLY:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(_t);
			}
			}
			}
			r = (JavaAST)_t;
			match(_t,RCURLY);
			_t = _t.getNextSibling();
			r.print(out);
			_t = __t113;
			_t = _t.getNextSibling();
		}
		catch (RecognitionException ex) {
			reportError(ex);
			if (_t!=null) {_t = _t.getNextSibling();}
		}
		_retTree = _t;
	}
	
	public final void expressionType(AST _t) throws RecognitionException {
		
		JavaAST expressionType_AST_in = (_t == ASTNULL) ? null : (JavaAST)_t;
		
		try {      // for error handling
			if (_t==null) _t=ASTNULL;
			switch ( _t.getType()) {
			case CONCAT_ASSIGN:
			case CONCATENATION:
			case UNARY_MINUS:
			case UNARY_PLUS:
			case POST_INC:
			case POST_DEC:
			case STAR:
			case ASSIGN:
			case PLUS_ASSIGN:
			case MINUS_ASSIGN:
			case STAR_ASSIGN:
			case DIV_ASSIGN:
			case MOD_ASSIGN:
			case SR_ASSIGN:
			case BSR_ASSIGN:
			case SL_ASSIGN:
			case BAND_ASSIGN:
			case BXOR_ASSIGN:
			case BOR_ASSIGN:
			case QUESTION:
			case LOR:
			case LAND:
			case BOR:
			case BXOR:
			case BAND:
			case NOT_EQUAL:
			case EQUAL:
			case LT:
			case GT:
			case LE:
			case GE:
			case LITERAL_instanceof:
			case SL:
			case SR:
			case BSR:
			case PLUS:
			case MINUS:
			case DIV:
			case MOD:
			case INC:
			case DEC:
			case BNOT:
			case LNOT:
			{
				{
				if (_t==null) _t=ASTNULL;
				switch ( _t.getType()) {
				case QUESTION:
				{
					AST __t298 = _t;
					JavaAST tmp136_AST_in = (JavaAST)_t;
					match(_t,QUESTION);
					_t = _t.getFirstChild();
					expressionType(_t);
					_t = _retTree;
					expressionType(_t);
					_t = _retTree;
					JavaAST tmp137_AST_in = (JavaAST)_t;
					match(_t,COLON);
					_t = _t.getNextSibling();
					expressionType(_t);
					_t = _retTree;
					_t = __t298;
					_t = _t.getNextSibling();
					break;
				}
				case ASSIGN:
				{
					AST __t299 = _t;
					JavaAST tmp138_AST_in = (JavaAST)_t;
					match(_t,ASSIGN);
					_t = _t.getFirstChild();
					expressionType(_t);
					_t = _retTree;
					expressionType(_t);
					_t = _retTree;
					_t = __t299;
					_t = _t.getNextSibling();
					break;
				}
				case PLUS_ASSIGN:
				{
					AST __t300 = _t;
					JavaAST tmp139_AST_in = (JavaAST)_t;
					match(_t,PLUS_ASSIGN);
					_t = _t.getFirstChild();
					expressionType(_t);
					_t = _retTree;
					expressionType(_t);
					_t = _retTree;
					_t = __t300;
					_t = _t.getNextSibling();
					break;
				}
				case CONCAT_ASSIGN:
				{
					AST __t301 = _t;
					JavaAST tmp140_AST_in = (JavaAST)_t;
					match(_t,CONCAT_ASSIGN);
					_t = _t.getFirstChild();
					expressionType(_t);
					_t = _retTree;
					expressionType(_t);
					_t = _retTree;
					_t = __t301;
					_t = _t.getNextSibling();
					break;
				}
				case MINUS_ASSIGN:
				{
					AST __t302 = _t;
					JavaAST tmp141_AST_in = (JavaAST)_t;
					match(_t,MINUS_ASSIGN);
					_t = _t.getFirstChild();
					expressionType(_t);
					_t = _retTree;
					expressionType(_t);
					_t = _retTree;
					_t = __t302;
					_t = _t.getNextSibling();
					break;
				}
				case STAR_ASSIGN:
				{
					AST __t303 = _t;
					JavaAST tmp142_AST_in = (JavaAST)_t;
					match(_t,STAR_ASSIGN);
					_t = _t.getFirstChild();
					expressionType(_t);
					_t = _retTree;
					expressionType(_t);
					_t = _retTree;
					_t = __t303;
					_t = _t.getNextSibling();
					break;
				}
				case DIV_ASSIGN:
				{
					AST __t304 = _t;
					JavaAST tmp143_AST_in = (JavaAST)_t;
					match(_t,DIV_ASSIGN);
					_t = _t.getFirstChild();
					expressionType(_t);
					_t = _retTree;
					expressionType(_t);
					_t = _retTree;
					_t = __t304;
					_t = _t.getNextSibling();
					break;
				}
				case MOD_ASSIGN:
				{
					AST __t305 = _t;
					JavaAST tmp144_AST_in = (JavaAST)_t;
					match(_t,MOD_ASSIGN);
					_t = _t.getFirstChild();
					expressionType(_t);
					_t = _retTree;
					expressionType(_t);
					_t = _retTree;
					_t = __t305;
					_t = _t.getNextSibling();
					break;
				}
				case SR_ASSIGN:
				{
					AST __t306 = _t;
					JavaAST tmp145_AST_in = (JavaAST)_t;
					match(_t,SR_ASSIGN);
					_t = _t.getFirstChild();
					expressionType(_t);
					_t = _retTree;
					expressionType(_t);
					_t = _retTree;
					_t = __t306;
					_t = _t.getNextSibling();
					break;
				}
				case BSR_ASSIGN:
				{
					AST __t307 = _t;
					JavaAST tmp146_AST_in = (JavaAST)_t;
					match(_t,BSR_ASSIGN);
					_t = _t.getFirstChild();
					expressionType(_t);
					_t = _retTree;
					expressionType(_t);
					_t = _retTree;
					_t = __t307;
					_t = _t.getNextSibling();
					break;
				}
				case SL_ASSIGN:
				{
					AST __t308 = _t;
					JavaAST tmp147_AST_in = (JavaAST)_t;
					match(_t,SL_ASSIGN);
					_t = _t.getFirstChild();
					expressionType(_t);
					_t = _retTree;
					expressionType(_t);
					_t = _retTree;
					_t = __t308;
					_t = _t.getNextSibling();
					break;
				}
				case BAND_ASSIGN:
				{
					AST __t309 = _t;
					JavaAST tmp148_AST_in = (JavaAST)_t;
					match(_t,BAND_ASSIGN);
					_t = _t.getFirstChild();
					expressionType(_t);
					_t = _retTree;
					expressionType(_t);
					_t = _retTree;
					_t = __t309;
					_t = _t.getNextSibling();
					break;
				}
				case BXOR_ASSIGN:
				{
					AST __t310 = _t;
					JavaAST tmp149_AST_in = (JavaAST)_t;
					match(_t,BXOR_ASSIGN);
					_t = _t.getFirstChild();
					expressionType(_t);
					_t = _retTree;
					expressionType(_t);
					_t = _retTree;
					_t = __t310;
					_t = _t.getNextSibling();
					break;
				}
				case BOR_ASSIGN:
				{
					AST __t311 = _t;
					JavaAST tmp150_AST_in = (JavaAST)_t;
					match(_t,BOR_ASSIGN);
					_t = _t.getFirstChild();
					expressionType(_t);
					_t = _retTree;
					expressionType(_t);
					_t = _retTree;
					_t = __t311;
					_t = _t.getNextSibling();
					break;
				}
				case LOR:
				{
					AST __t312 = _t;
					JavaAST tmp151_AST_in = (JavaAST)_t;
					match(_t,LOR);
					_t = _t.getFirstChild();
					expressionType(_t);
					_t = _retTree;
					expressionType(_t);
					_t = _retTree;
					_t = __t312;
					_t = _t.getNextSibling();
					break;
				}
				case LAND:
				{
					AST __t313 = _t;
					JavaAST tmp152_AST_in = (JavaAST)_t;
					match(_t,LAND);
					_t = _t.getFirstChild();
					expressionType(_t);
					_t = _retTree;
					expressionType(_t);
					_t = _retTree;
					_t = __t313;
					_t = _t.getNextSibling();
					break;
				}
				case BOR:
				{
					AST __t314 = _t;
					JavaAST tmp153_AST_in = (JavaAST)_t;
					match(_t,BOR);
					_t = _t.getFirstChild();
					expressionType(_t);
					_t = _retTree;
					expressionType(_t);
					_t = _retTree;
					_t = __t314;
					_t = _t.getNextSibling();
					break;
				}
				case BXOR:
				{
					AST __t315 = _t;
					JavaAST tmp154_AST_in = (JavaAST)_t;
					match(_t,BXOR);
					_t = _t.getFirstChild();
					expressionType(_t);
					_t = _retTree;
					expressionType(_t);
					_t = _retTree;
					_t = __t315;
					_t = _t.getNextSibling();
					break;
				}
				case BAND:
				{
					AST __t316 = _t;
					JavaAST tmp155_AST_in = (JavaAST)_t;
					match(_t,BAND);
					_t = _t.getFirstChild();
					expressionType(_t);
					_t = _retTree;
					expressionType(_t);
					_t = _retTree;
					_t = __t316;
					_t = _t.getNextSibling();
					break;
				}
				case NOT_EQUAL:
				{
					AST __t317 = _t;
					JavaAST tmp156_AST_in = (JavaAST)_t;
					match(_t,NOT_EQUAL);
					_t = _t.getFirstChild();
					expressionType(_t);
					_t = _retTree;
					expressionType(_t);
					_t = _retTree;
					_t = __t317;
					_t = _t.getNextSibling();
					break;
				}
				case EQUAL:
				{
					AST __t318 = _t;
					JavaAST tmp157_AST_in = (JavaAST)_t;
					match(_t,EQUAL);
					_t = _t.getFirstChild();
					expressionType(_t);
					_t = _retTree;
					expressionType(_t);
					_t = _retTree;
					_t = __t318;
					_t = _t.getNextSibling();
					break;
				}
				case LT:
				{
					AST __t319 = _t;
					JavaAST tmp158_AST_in = (JavaAST)_t;
					match(_t,LT);
					_t = _t.getFirstChild();
					expressionType(_t);
					_t = _retTree;
					expressionType(_t);
					_t = _retTree;
					_t = __t319;
					_t = _t.getNextSibling();
					break;
				}
				case GT:
				{
					AST __t320 = _t;
					JavaAST tmp159_AST_in = (JavaAST)_t;
					match(_t,GT);
					_t = _t.getFirstChild();
					expressionType(_t);
					_t = _retTree;
					expressionType(_t);
					_t = _retTree;
					_t = __t320;
					_t = _t.getNextSibling();
					break;
				}
				case LE:
				{
					AST __t321 = _t;
					JavaAST tmp160_AST_in = (JavaAST)_t;
					match(_t,LE);
					_t = _t.getFirstChild();
					expressionType(_t);
					_t = _retTree;
					expressionType(_t);
					_t = _retTree;
					_t = __t321;
					_t = _t.getNextSibling();
					break;
				}
				case GE:
				{
					AST __t322 = _t;
					JavaAST tmp161_AST_in = (JavaAST)_t;
					match(_t,GE);
					_t = _t.getFirstChild();
					expressionType(_t);
					_t = _retTree;
					expressionType(_t);
					_t = _retTree;
					_t = __t322;
					_t = _t.getNextSibling();
					break;
				}
				case SL:
				{
					AST __t323 = _t;
					JavaAST tmp162_AST_in = (JavaAST)_t;
					match(_t,SL);
					_t = _t.getFirstChild();
					expressionType(_t);
					_t = _retTree;
					expressionType(_t);
					_t = _retTree;
					_t = __t323;
					_t = _t.getNextSibling();
					break;
				}
				case SR:
				{
					AST __t324 = _t;
					JavaAST tmp163_AST_in = (JavaAST)_t;
					match(_t,SR);
					_t = _t.getFirstChild();
					expressionType(_t);
					_t = _retTree;
					expressionType(_t);
					_t = _retTree;
					_t = __t324;
					_t = _t.getNextSibling();
					break;
				}
				case BSR:
				{
					AST __t325 = _t;
					JavaAST tmp164_AST_in = (JavaAST)_t;
					match(_t,BSR);
					_t = _t.getFirstChild();
					expressionType(_t);
					_t = _retTree;
					expressionType(_t);
					_t = _retTree;
					_t = __t325;
					_t = _t.getNextSibling();
					break;
				}
				case PLUS:
				{
					AST __t326 = _t;
					JavaAST tmp165_AST_in = (JavaAST)_t;
					match(_t,PLUS);
					_t = _t.getFirstChild();
					expressionType(_t);
					_t = _retTree;
					expressionType(_t);
					_t = _retTree;
					_t = __t326;
					_t = _t.getNextSibling();
					break;
				}
				case CONCATENATION:
				{
					AST __t327 = _t;
					JavaAST tmp166_AST_in = (JavaAST)_t;
					match(_t,CONCATENATION);
					_t = _t.getFirstChild();
					expressionType(_t);
					_t = _retTree;
					expressionType(_t);
					_t = _retTree;
					_t = __t327;
					_t = _t.getNextSibling();
					break;
				}
				case MINUS:
				{
					AST __t328 = _t;
					JavaAST tmp167_AST_in = (JavaAST)_t;
					match(_t,MINUS);
					_t = _t.getFirstChild();
					expressionType(_t);
					_t = _retTree;
					expressionType(_t);
					_t = _retTree;
					_t = __t328;
					_t = _t.getNextSibling();
					break;
				}
				case DIV:
				{
					AST __t329 = _t;
					JavaAST tmp168_AST_in = (JavaAST)_t;
					match(_t,DIV);
					_t = _t.getFirstChild();
					expressionType(_t);
					_t = _retTree;
					expressionType(_t);
					_t = _retTree;
					_t = __t329;
					_t = _t.getNextSibling();
					break;
				}
				case MOD:
				{
					AST __t330 = _t;
					JavaAST tmp169_AST_in = (JavaAST)_t;
					match(_t,MOD);
					_t = _t.getFirstChild();
					expressionType(_t);
					_t = _retTree;
					expressionType(_t);
					_t = _retTree;
					_t = __t330;
					_t = _t.getNextSibling();
					break;
				}
				case STAR:
				{
					AST __t331 = _t;
					JavaAST tmp170_AST_in = (JavaAST)_t;
					match(_t,STAR);
					_t = _t.getFirstChild();
					expressionType(_t);
					_t = _retTree;
					expressionType(_t);
					_t = _retTree;
					_t = __t331;
					_t = _t.getNextSibling();
					break;
				}
				case INC:
				{
					AST __t332 = _t;
					JavaAST tmp171_AST_in = (JavaAST)_t;
					match(_t,INC);
					_t = _t.getFirstChild();
					expressionType(_t);
					_t = _retTree;
					_t = __t332;
					_t = _t.getNextSibling();
					break;
				}
				case DEC:
				{
					AST __t333 = _t;
					JavaAST tmp172_AST_in = (JavaAST)_t;
					match(_t,DEC);
					_t = _t.getFirstChild();
					expressionType(_t);
					_t = _retTree;
					_t = __t333;
					_t = _t.getNextSibling();
					break;
				}
				case POST_INC:
				{
					AST __t334 = _t;
					JavaAST tmp173_AST_in = (JavaAST)_t;
					match(_t,POST_INC);
					_t = _t.getFirstChild();
					expressionType(_t);
					_t = _retTree;
					_t = __t334;
					_t = _t.getNextSibling();
					break;
				}
				case POST_DEC:
				{
					AST __t335 = _t;
					JavaAST tmp174_AST_in = (JavaAST)_t;
					match(_t,POST_DEC);
					_t = _t.getFirstChild();
					expressionType(_t);
					_t = _retTree;
					_t = __t335;
					_t = _t.getNextSibling();
					break;
				}
				case BNOT:
				{
					AST __t336 = _t;
					JavaAST tmp175_AST_in = (JavaAST)_t;
					match(_t,BNOT);
					_t = _t.getFirstChild();
					expressionType(_t);
					_t = _retTree;
					_t = __t336;
					_t = _t.getNextSibling();
					break;
				}
				case LNOT:
				{
					AST __t337 = _t;
					JavaAST tmp176_AST_in = (JavaAST)_t;
					match(_t,LNOT);
					_t = _t.getFirstChild();
					expressionType(_t);
					_t = _retTree;
					_t = __t337;
					_t = _t.getNextSibling();
					break;
				}
				case LITERAL_instanceof:
				{
					AST __t338 = _t;
					JavaAST tmp177_AST_in = (JavaAST)_t;
					match(_t,LITERAL_instanceof);
					_t = _t.getFirstChild();
					expressionType(_t);
					_t = _retTree;
					expressionType(_t);
					_t = _retTree;
					_t = __t338;
					_t = _t.getNextSibling();
					break;
				}
				case UNARY_MINUS:
				{
					AST __t339 = _t;
					JavaAST tmp178_AST_in = (JavaAST)_t;
					match(_t,UNARY_MINUS);
					_t = _t.getFirstChild();
					expressionType(_t);
					_t = _retTree;
					_t = __t339;
					_t = _t.getNextSibling();
					break;
				}
				case UNARY_PLUS:
				{
					AST __t340 = _t;
					JavaAST tmp179_AST_in = (JavaAST)_t;
					match(_t,UNARY_PLUS);
					_t = _t.getFirstChild();
					expressionType(_t);
					_t = _retTree;
					_t = __t340;
					_t = _t.getNextSibling();
					break;
				}
				default:
				{
					throw new NoViableAltException(_t);
				}
				}
				}
				expression(expressionType_AST_in); printType(expressionType_AST_in);
				break;
			}
			case TYPE:
			case TYPECAST:
			case INDEX_OP:
			case METHOD_CALL:
			case CONSTRUCTOR_CALL:
			case PAREN_EXPR:
			case IDENT:
			case DOT:
			case LITERAL_this:
			case LITERAL_super:
			case LITERAL_true:
			case LITERAL_false:
			case LITERAL_null:
			case LITERAL_new:
			case NUM_INT:
			case CHAR_LITERAL:
			case STRING_LITERAL:
			case NUM_FLOAT:
			{
				primaryExpressionType(_t);
				_t = _retTree;
				break;
			}
			default:
			{
				throw new NoViableAltException(_t);
			}
			}
		}
		catch (RecognitionException ex) {
			reportError(ex);
			if (_t!=null) {_t = _t.getNextSibling();}
		}
		_retTree = _t;
	}
	
	public final void arrayInitializerType(AST _t) throws RecognitionException {
		
		JavaAST arrayInitializerType_AST_in = (_t == ASTNULL) ? null : (JavaAST)_t;
		
		try {      // for error handling
			AST __t117 = _t;
			JavaAST tmp180_AST_in = (JavaAST)_t;
			match(_t,ARRAY_INIT);
			_t = _t.getFirstChild();
			{
			if (_t==null) _t=ASTNULL;
			switch ( _t.getType()) {
			case TYPE:
			case ARRAY_INIT:
			case CONCAT_ASSIGN:
			case CONCATENATION:
			case UNARY_MINUS:
			case UNARY_PLUS:
			case TYPECAST:
			case INDEX_OP:
			case METHOD_CALL:
			case CONSTRUCTOR_CALL:
			case POST_INC:
			case POST_DEC:
			case PAREN_EXPR:
			case IDENT:
			case DOT:
			case STAR:
			case ASSIGN:
			case PLUS_ASSIGN:
			case MINUS_ASSIGN:
			case STAR_ASSIGN:
			case DIV_ASSIGN:
			case MOD_ASSIGN:
			case SR_ASSIGN:
			case BSR_ASSIGN:
			case SL_ASSIGN:
			case BAND_ASSIGN:
			case BXOR_ASSIGN:
			case BOR_ASSIGN:
			case QUESTION:
			case LOR:
			case LAND:
			case BOR:
			case BXOR:
			case BAND:
			case NOT_EQUAL:
			case EQUAL:
			case LT:
			case GT:
			case LE:
			case GE:
			case LITERAL_instanceof:
			case SL:
			case SR:
			case BSR:
			case PLUS:
			case MINUS:
			case DIV:
			case MOD:
			case INC:
			case DEC:
			case BNOT:
			case LNOT:
			case LITERAL_this:
			case LITERAL_super:
			case LITERAL_true:
			case LITERAL_false:
			case LITERAL_null:
			case LITERAL_new:
			case NUM_INT:
			case CHAR_LITERAL:
			case STRING_LITERAL:
			case NUM_FLOAT:
			{
				initializerType(_t);
				_t = _retTree;
				{
				if (_t==null) _t=ASTNULL;
				switch ( _t.getType()) {
				case COMMA:
				{
					commaInitializerType(_t);
					_t = _retTree;
					break;
				}
				case RCURLY:
				{
					break;
				}
				default:
				{
					throw new NoViableAltException(_t);
				}
				}
				}
				break;
			}
			case RCURLY:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(_t);
			}
			}
			}
			JavaAST tmp181_AST_in = (JavaAST)_t;
			match(_t,RCURLY);
			_t = _t.getNextSibling();
			_t = __t117;
			_t = _t.getNextSibling();
			printType(arrayInitializerType_AST_in);
		}
		catch (RecognitionException ex) {
			reportError(ex);
			if (_t!=null) {_t = _t.getNextSibling();}
		}
		_retTree = _t;
	}
	
	public final void commaInitializer(AST _t) throws RecognitionException {
		
		JavaAST commaInitializer_AST_in = (_t == ASTNULL) ? null : (JavaAST)_t;
		JavaAST c = null;
		
		try {      // for error handling
			AST __t121 = _t;
			c = _t==ASTNULL ? null :(JavaAST)_t;
			match(_t,COMMA);
			_t = _t.getFirstChild();
			c.print(out);
			{
			if (_t==null) _t=ASTNULL;
			switch ( _t.getType()) {
			case TYPE:
			case ARRAY_INIT:
			case CONCAT_ASSIGN:
			case CONCATENATION:
			case UNARY_MINUS:
			case UNARY_PLUS:
			case TYPECAST:
			case INDEX_OP:
			case METHOD_CALL:
			case CONSTRUCTOR_CALL:
			case POST_INC:
			case POST_DEC:
			case PAREN_EXPR:
			case IDENT:
			case DOT:
			case STAR:
			case ASSIGN:
			case PLUS_ASSIGN:
			case MINUS_ASSIGN:
			case STAR_ASSIGN:
			case DIV_ASSIGN:
			case MOD_ASSIGN:
			case SR_ASSIGN:
			case BSR_ASSIGN:
			case SL_ASSIGN:
			case BAND_ASSIGN:
			case BXOR_ASSIGN:
			case BOR_ASSIGN:
			case QUESTION:
			case LOR:
			case LAND:
			case BOR:
			case BXOR:
			case BAND:
			case NOT_EQUAL:
			case EQUAL:
			case LT:
			case GT:
			case LE:
			case GE:
			case LITERAL_instanceof:
			case SL:
			case SR:
			case BSR:
			case PLUS:
			case MINUS:
			case DIV:
			case MOD:
			case INC:
			case DEC:
			case BNOT:
			case LNOT:
			case LITERAL_this:
			case LITERAL_super:
			case LITERAL_true:
			case LITERAL_false:
			case LITERAL_null:
			case LITERAL_new:
			case NUM_INT:
			case CHAR_LITERAL:
			case STRING_LITERAL:
			case NUM_FLOAT:
			{
				initializer(_t);
				_t = _retTree;
				{
				if (_t==null) _t=ASTNULL;
				switch ( _t.getType()) {
				case COMMA:
				{
					commaInitializer(_t);
					_t = _retTree;
					break;
				}
				case 3:
				{
					break;
				}
				default:
				{
					throw new NoViableAltException(_t);
				}
				}
				}
				break;
			}
			case 3:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(_t);
			}
			}
			}
			_t = __t121;
			_t = _t.getNextSibling();
		}
		catch (RecognitionException ex) {
			reportError(ex);
			if (_t!=null) {_t = _t.getNextSibling();}
		}
		_retTree = _t;
	}
	
	public final void commaInitializerType(AST _t) throws RecognitionException {
		
		JavaAST commaInitializerType_AST_in = (_t == ASTNULL) ? null : (JavaAST)_t;
		
		try {      // for error handling
			AST __t125 = _t;
			JavaAST tmp182_AST_in = (JavaAST)_t;
			match(_t,COMMA);
			_t = _t.getFirstChild();
			{
			if (_t==null) _t=ASTNULL;
			switch ( _t.getType()) {
			case TYPE:
			case ARRAY_INIT:
			case CONCAT_ASSIGN:
			case CONCATENATION:
			case UNARY_MINUS:
			case UNARY_PLUS:
			case TYPECAST:
			case INDEX_OP:
			case METHOD_CALL:
			case CONSTRUCTOR_CALL:
			case POST_INC:
			case POST_DEC:
			case PAREN_EXPR:
			case IDENT:
			case DOT:
			case STAR:
			case ASSIGN:
			case PLUS_ASSIGN:
			case MINUS_ASSIGN:
			case STAR_ASSIGN:
			case DIV_ASSIGN:
			case MOD_ASSIGN:
			case SR_ASSIGN:
			case BSR_ASSIGN:
			case SL_ASSIGN:
			case BAND_ASSIGN:
			case BXOR_ASSIGN:
			case BOR_ASSIGN:
			case QUESTION:
			case LOR:
			case LAND:
			case BOR:
			case BXOR:
			case BAND:
			case NOT_EQUAL:
			case EQUAL:
			case LT:
			case GT:
			case LE:
			case GE:
			case LITERAL_instanceof:
			case SL:
			case SR:
			case BSR:
			case PLUS:
			case MINUS:
			case DIV:
			case MOD:
			case INC:
			case DEC:
			case BNOT:
			case LNOT:
			case LITERAL_this:
			case LITERAL_super:
			case LITERAL_true:
			case LITERAL_false:
			case LITERAL_null:
			case LITERAL_new:
			case NUM_INT:
			case CHAR_LITERAL:
			case STRING_LITERAL:
			case NUM_FLOAT:
			{
				initializerType(_t);
				_t = _retTree;
				{
				if (_t==null) _t=ASTNULL;
				switch ( _t.getType()) {
				case COMMA:
				{
					commaInitializerType(_t);
					_t = _retTree;
					break;
				}
				case 3:
				{
					break;
				}
				default:
				{
					throw new NoViableAltException(_t);
				}
				}
				}
				break;
			}
			case 3:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(_t);
			}
			}
			}
			_t = __t125;
			_t = _t.getNextSibling();
		}
		catch (RecognitionException ex) {
			reportError(ex);
			if (_t!=null) {_t = _t.getNextSibling();}
		}
		_retTree = _t;
	}
	
	public final void throwsClause(AST _t) throws RecognitionException {
		
		JavaAST throwsClause_AST_in = (_t == ASTNULL) ? null : (JavaAST)_t;
		
		try {      // for error handling
			AST __t141 = _t;
			JavaAST tmp183_AST_in = (JavaAST)_t;
			match(_t,LITERAL_throws);
			_t = _t.getFirstChild();
			identifier(_t,false);
			_t = _retTree;
			{
			_loop143:
			do {
				if (_t==null) _t=ASTNULL;
				if ((_t.getType()==COMMA)) {
					JavaAST tmp184_AST_in = (JavaAST)_t;
					match(_t,COMMA);
					_t = _t.getNextSibling();
					identifier(_t,false);
					_t = _retTree;
				}
				else {
					break _loop143;
				}
				
			} while (true);
			}
			_t = __t141;
			_t = _t.getNextSibling();
		}
		catch (RecognitionException ex) {
			reportError(ex);
			if (_t!=null) {_t = _t.getNextSibling();}
		}
		_retTree = _t;
	}
	
	public final void stat(AST _t) throws RecognitionException {
		
		JavaAST stat_AST_in = (_t == ASTNULL) ? null : (JavaAST)_t;
		JavaAST sm1 = null;
		JavaAST c1 = null;
		JavaAST i = null;
		JavaAST l1 = null;
		JavaAST r1 = null;
		JavaAST e = null;
		JavaAST f = null;
		JavaAST l2 = null;
		JavaAST sm2 = null;
		JavaAST sm3 = null;
		JavaAST r2 = null;
		JavaAST w = null;
		JavaAST l3 = null;
		JavaAST r3 = null;
		JavaAST d = null;
		JavaAST wh = null;
		JavaAST l4 = null;
		JavaAST r4 = null;
		JavaAST sm4 = null;
		JavaAST b = null;
		JavaAST id1 = null;
		JavaAST sm5 = null;
		JavaAST c = null;
		JavaAST id2 = null;
		JavaAST sm6 = null;
		JavaAST r = null;
		JavaAST sm7 = null;
		JavaAST sw = null;
		JavaAST l5 = null;
		JavaAST r5 = null;
		JavaAST t = null;
		JavaAST sm8 = null;
		JavaAST sy = null;
		JavaAST l6 = null;
		JavaAST r6 = null;
		JavaAST a = null;
		JavaAST c2 = null;
		JavaAST sm9 = null;
		
		try {      // for error handling
			if (_t==null) _t=ASTNULL;
			switch ( _t.getType()) {
			case VARIABLE_DEFS:
			{
				variableDefs(_t);
				_t = _retTree;
				break;
			}
			case TYPE_STAT:
			{
				AST __t161 = _t;
				JavaAST tmp185_AST_in = (JavaAST)_t;
				match(_t,TYPE_STAT);
				_t = _t.getFirstChild();
				typeDefinition(_t);
				_t = _retTree;
				_t = __t161;
				_t = _t.getNextSibling();
				break;
			}
			case EXPRESSION_STAT:
			{
				AST __t162 = _t;
				JavaAST tmp186_AST_in = (JavaAST)_t;
				match(_t,EXPRESSION_STAT);
				_t = _t.getFirstChild();
				expression(_t);
				_t = _retTree;
				sm1 = (JavaAST)_t;
				match(_t,SEMI);
				_t = _t.getNextSibling();
				_t = __t162;
				_t = _t.getNextSibling();
				sm1.print(out);
				break;
			}
			case LABELED_STAT:
			{
				AST __t163 = _t;
				JavaAST tmp187_AST_in = (JavaAST)_t;
				match(_t,LABELED_STAT);
				_t = _t.getFirstChild();
				c1 = (JavaAST)_t;
				match(_t,COLON);
				_t = _t.getNextSibling();
				tmp187_AST_in.print(out); c1.print(out);
				stat(_t);
				_t = _retTree;
				_t = __t163;
				_t = _t.getNextSibling();
				break;
			}
			case LITERAL_if:
			{
				AST __t164 = _t;
				i = _t==ASTNULL ? null :(JavaAST)_t;
				match(_t,LITERAL_if);
				_t = _t.getFirstChild();
				l1 = (JavaAST)_t;
				match(_t,LPAREN);
				_t = _t.getNextSibling();
				i.print(out); l1.print(out);
				expression(_t);
				_t = _retTree;
				r1 = (JavaAST)_t;
				match(_t,RPAREN);
				_t = _t.getNextSibling();
				r1.print(out);
				stat(_t);
				_t = _retTree;
				{
				if (_t==null) _t=ASTNULL;
				switch ( _t.getType()) {
				case LITERAL_else:
				{
					e = (JavaAST)_t;
					match(_t,LITERAL_else);
					_t = _t.getNextSibling();
					e.print(out);
					stat(_t);
					_t = _retTree;
					break;
				}
				case 3:
				{
					break;
				}
				default:
				{
					throw new NoViableAltException(_t);
				}
				}
				}
				_t = __t164;
				_t = _t.getNextSibling();
				break;
			}
			case LITERAL_for:
			{
				AST __t166 = _t;
				f = _t==ASTNULL ? null :(JavaAST)_t;
				match(_t,LITERAL_for);
				_t = _t.getFirstChild();
				l2 = (JavaAST)_t;
				match(_t,LPAREN);
				_t = _t.getNextSibling();
				f.print(out); l2.print(out);
				AST __t167 = _t;
				JavaAST tmp188_AST_in = (JavaAST)_t;
				match(_t,FOR_INIT);
				_t = _t.getFirstChild();
				{
				if (_t==null) _t=ASTNULL;
				switch ( _t.getType()) {
				case VARIABLE_DEFS:
				{
					variableDefs(_t);
					_t = _retTree;
					break;
				}
				case ELIST:
				{
					elist(_t);
					_t = _retTree;
					sm2 = (JavaAST)_t;
					match(_t,SEMI);
					_t = _t.getNextSibling();
					sm2.print(out);
					break;
				}
				default:
				{
					throw new NoViableAltException(_t);
				}
				}
				}
				_t = __t167;
				_t = _t.getNextSibling();
				AST __t169 = _t;
				JavaAST tmp189_AST_in = (JavaAST)_t;
				match(_t,FOR_CONDITION);
				_t = _t.getFirstChild();
				{
				if (_t==null) _t=ASTNULL;
				switch ( _t.getType()) {
				case TYPE:
				case CONCAT_ASSIGN:
				case CONCATENATION:
				case UNARY_MINUS:
				case UNARY_PLUS:
				case TYPECAST:
				case INDEX_OP:
				case METHOD_CALL:
				case CONSTRUCTOR_CALL:
				case POST_INC:
				case POST_DEC:
				case PAREN_EXPR:
				case IDENT:
				case DOT:
				case STAR:
				case ASSIGN:
				case PLUS_ASSIGN:
				case MINUS_ASSIGN:
				case STAR_ASSIGN:
				case DIV_ASSIGN:
				case MOD_ASSIGN:
				case SR_ASSIGN:
				case BSR_ASSIGN:
				case SL_ASSIGN:
				case BAND_ASSIGN:
				case BXOR_ASSIGN:
				case BOR_ASSIGN:
				case QUESTION:
				case LOR:
				case LAND:
				case BOR:
				case BXOR:
				case BAND:
				case NOT_EQUAL:
				case EQUAL:
				case LT:
				case GT:
				case LE:
				case GE:
				case LITERAL_instanceof:
				case SL:
				case SR:
				case BSR:
				case PLUS:
				case MINUS:
				case DIV:
				case MOD:
				case INC:
				case DEC:
				case BNOT:
				case LNOT:
				case LITERAL_this:
				case LITERAL_super:
				case LITERAL_true:
				case LITERAL_false:
				case LITERAL_null:
				case LITERAL_new:
				case NUM_INT:
				case CHAR_LITERAL:
				case STRING_LITERAL:
				case NUM_FLOAT:
				{
					expression(_t);
					_t = _retTree;
					break;
				}
				case SEMI:
				{
					break;
				}
				default:
				{
					throw new NoViableAltException(_t);
				}
				}
				}
				sm3 = (JavaAST)_t;
				match(_t,SEMI);
				_t = _t.getNextSibling();
				sm3.print(out);
				_t = __t169;
				_t = _t.getNextSibling();
				AST __t171 = _t;
				JavaAST tmp190_AST_in = (JavaAST)_t;
				match(_t,FOR_ITERATOR);
				_t = _t.getFirstChild();
				elist(_t);
				_t = _retTree;
				_t = __t171;
				_t = _t.getNextSibling();
				r2 = (JavaAST)_t;
				match(_t,RPAREN);
				_t = _t.getNextSibling();
				r2.print(out);
				stat(_t);
				_t = _retTree;
				_t = __t166;
				_t = _t.getNextSibling();
				break;
			}
			case LITERAL_while:
			{
				AST __t172 = _t;
				w = _t==ASTNULL ? null :(JavaAST)_t;
				match(_t,LITERAL_while);
				_t = _t.getFirstChild();
				l3 = (JavaAST)_t;
				match(_t,LPAREN);
				_t = _t.getNextSibling();
				w.print(out); l3.print(out);
				expression(_t);
				_t = _retTree;
				r3 = (JavaAST)_t;
				match(_t,RPAREN);
				_t = _t.getNextSibling();
				r3.print(out);
				stat(_t);
				_t = _retTree;
				_t = __t172;
				_t = _t.getNextSibling();
				break;
			}
			case LITERAL_do:
			{
				AST __t173 = _t;
				d = _t==ASTNULL ? null :(JavaAST)_t;
				match(_t,LITERAL_do);
				_t = _t.getFirstChild();
				d.print(out);
				stat(_t);
				_t = _retTree;
				wh = (JavaAST)_t;
				match(_t,LITERAL_while);
				_t = _t.getNextSibling();
				l4 = (JavaAST)_t;
				match(_t,LPAREN);
				_t = _t.getNextSibling();
				wh.print(out); l4.print(out);
				expression(_t);
				_t = _retTree;
				r4 = (JavaAST)_t;
				match(_t,RPAREN);
				_t = _t.getNextSibling();
				sm4 = (JavaAST)_t;
				match(_t,SEMI);
				_t = _t.getNextSibling();
				r4.print(out); sm4.print(out);
				_t = __t173;
				_t = _t.getNextSibling();
				break;
			}
			case LITERAL_break:
			{
				AST __t174 = _t;
				b = _t==ASTNULL ? null :(JavaAST)_t;
				match(_t,LITERAL_break);
				_t = _t.getFirstChild();
				b.print(out);
				{
				if (_t==null) _t=ASTNULL;
				switch ( _t.getType()) {
				case IDENT:
				{
					id1 = (JavaAST)_t;
					match(_t,IDENT);
					_t = _t.getNextSibling();
					id1.print(out);
					break;
				}
				case SEMI:
				{
					break;
				}
				default:
				{
					throw new NoViableAltException(_t);
				}
				}
				}
				sm5 = (JavaAST)_t;
				match(_t,SEMI);
				_t = _t.getNextSibling();
				sm5.print(out);
				_t = __t174;
				_t = _t.getNextSibling();
				break;
			}
			case LITERAL_continue:
			{
				AST __t176 = _t;
				c = _t==ASTNULL ? null :(JavaAST)_t;
				match(_t,LITERAL_continue);
				_t = _t.getFirstChild();
				c.print(out);
				{
				if (_t==null) _t=ASTNULL;
				switch ( _t.getType()) {
				case IDENT:
				{
					id2 = (JavaAST)_t;
					match(_t,IDENT);
					_t = _t.getNextSibling();
					id2.print(out);
					break;
				}
				case SEMI:
				{
					break;
				}
				default:
				{
					throw new NoViableAltException(_t);
				}
				}
				}
				sm6 = (JavaAST)_t;
				match(_t,SEMI);
				_t = _t.getNextSibling();
				sm6.print(out);
				_t = __t176;
				_t = _t.getNextSibling();
				break;
			}
			case LITERAL_return:
			{
				AST __t178 = _t;
				r = _t==ASTNULL ? null :(JavaAST)_t;
				match(_t,LITERAL_return);
				_t = _t.getFirstChild();
				r.print(out);
				{
				if (_t==null) _t=ASTNULL;
				switch ( _t.getType()) {
				case TYPE:
				case CONCAT_ASSIGN:
				case CONCATENATION:
				case UNARY_MINUS:
				case UNARY_PLUS:
				case TYPECAST:
				case INDEX_OP:
				case METHOD_CALL:
				case CONSTRUCTOR_CALL:
				case POST_INC:
				case POST_DEC:
				case PAREN_EXPR:
				case IDENT:
				case DOT:
				case STAR:
				case ASSIGN:
				case PLUS_ASSIGN:
				case MINUS_ASSIGN:
				case STAR_ASSIGN:
				case DIV_ASSIGN:
				case MOD_ASSIGN:
				case SR_ASSIGN:
				case BSR_ASSIGN:
				case SL_ASSIGN:
				case BAND_ASSIGN:
				case BXOR_ASSIGN:
				case BOR_ASSIGN:
				case QUESTION:
				case LOR:
				case LAND:
				case BOR:
				case BXOR:
				case BAND:
				case NOT_EQUAL:
				case EQUAL:
				case LT:
				case GT:
				case LE:
				case GE:
				case LITERAL_instanceof:
				case SL:
				case SR:
				case BSR:
				case PLUS:
				case MINUS:
				case DIV:
				case MOD:
				case INC:
				case DEC:
				case BNOT:
				case LNOT:
				case LITERAL_this:
				case LITERAL_super:
				case LITERAL_true:
				case LITERAL_false:
				case LITERAL_null:
				case LITERAL_new:
				case NUM_INT:
				case CHAR_LITERAL:
				case STRING_LITERAL:
				case NUM_FLOAT:
				{
					expression(_t);
					_t = _retTree;
					break;
				}
				case SEMI:
				{
					break;
				}
				default:
				{
					throw new NoViableAltException(_t);
				}
				}
				}
				sm7 = (JavaAST)_t;
				match(_t,SEMI);
				_t = _t.getNextSibling();
				sm7.print(out);
				_t = __t178;
				_t = _t.getNextSibling();
				break;
			}
			case LITERAL_switch:
			{
				AST __t180 = _t;
				sw = _t==ASTNULL ? null :(JavaAST)_t;
				match(_t,LITERAL_switch);
				_t = _t.getFirstChild();
				l5 = (JavaAST)_t;
				match(_t,LPAREN);
				_t = _t.getNextSibling();
				sw.print(out); l5.print(out);
				expression(_t);
				_t = _retTree;
				r5 = (JavaAST)_t;
				match(_t,RPAREN);
				_t = _t.getNextSibling();
				JavaAST tmp191_AST_in = (JavaAST)_t;
				match(_t,LCURLY);
				_t = _t.getNextSibling();
				r5.print(out); tmp191_AST_in.print(out);
				{
				_loop182:
				do {
					if (_t==null) _t=ASTNULL;
					if ((_t.getType()==CASE_GROUP)) {
						caseGroup(_t);
						_t = _retTree;
					}
					else {
						break _loop182;
					}
					
				} while (true);
				}
				JavaAST tmp192_AST_in = (JavaAST)_t;
				match(_t,RCURLY);
				_t = _t.getNextSibling();
				tmp192_AST_in.print(out);
				_t = __t180;
				_t = _t.getNextSibling();
				break;
			}
			case LITERAL_throw:
			{
				AST __t183 = _t;
				t = _t==ASTNULL ? null :(JavaAST)_t;
				match(_t,LITERAL_throw);
				_t = _t.getFirstChild();
				t.print(out);
				expression(_t);
				_t = _retTree;
				sm8 = (JavaAST)_t;
				match(_t,SEMI);
				_t = _t.getNextSibling();
				sm8.print(out);
				_t = __t183;
				_t = _t.getNextSibling();
				break;
			}
			case LITERAL_synchronized:
			{
				AST __t184 = _t;
				sy = _t==ASTNULL ? null :(JavaAST)_t;
				match(_t,LITERAL_synchronized);
				_t = _t.getFirstChild();
				l6 = (JavaAST)_t;
				match(_t,LPAREN);
				_t = _t.getNextSibling();
				sy.print(out); l6.print(out);
				expression(_t);
				_t = _retTree;
				r6 = (JavaAST)_t;
				match(_t,RPAREN);
				_t = _t.getNextSibling();
				r6.print(out);
				stat(_t);
				_t = _retTree;
				_t = __t184;
				_t = _t.getNextSibling();
				break;
			}
			case LITERAL_assert:
			{
				AST __t185 = _t;
				a = _t==ASTNULL ? null :(JavaAST)_t;
				match(_t,LITERAL_assert);
				_t = _t.getFirstChild();
				a.print(out);
				expression(_t);
				_t = _retTree;
				{
				if (_t==null) _t=ASTNULL;
				switch ( _t.getType()) {
				case COLON:
				{
					c2 = (JavaAST)_t;
					match(_t,COLON);
					_t = _t.getNextSibling();
					c2.print(out);
					expression(_t);
					_t = _retTree;
					break;
				}
				case SEMI:
				{
					break;
				}
				default:
				{
					throw new NoViableAltException(_t);
				}
				}
				}
				sm9 = (JavaAST)_t;
				match(_t,SEMI);
				_t = _t.getNextSibling();
				sm9.print(out);
				_t = __t185;
				_t = _t.getNextSibling();
				break;
			}
			case LITERAL_try:
			{
				tryBlock(_t);
				_t = _retTree;
				break;
			}
			case SLIST:
			{
				slist(_t);
				_t = _retTree;
				break;
			}
			case EMPTY_STAT:
			{
				JavaAST tmp193_AST_in = (JavaAST)_t;
				match(_t,EMPTY_STAT);
				_t = _t.getNextSibling();
				tmp193_AST_in.print(out);
				break;
			}
			default:
			{
				throw new NoViableAltException(_t);
			}
			}
		}
		catch (RecognitionException ex) {
			reportError(ex);
			if (_t!=null) {_t = _t.getNextSibling();}
		}
		_retTree = _t;
	}
	
	public final void statExcept(AST _t) throws RecognitionException {
		
		JavaAST statExcept_AST_in = (_t == ASTNULL) ? null : (JavaAST)_t;
		
		try {      // for error handling
			if (_t==null) _t=ASTNULL;
			switch ( _t.getType()) {
			case VARIABLE_DEFS:
			{
				variableDefsExcept(_t);
				_t = _retTree;
				break;
			}
			case LITERAL_try:
			{
				tryBlockExcept(_t);
				_t = _retTree;
				break;
			}
			case SLIST:
			{
				slistExcept(_t);
				_t = _retTree;
				break;
			}
			case TYPE_STAT:
			case EXPRESSION_STAT:
			case LABELED_STAT:
			case EMPTY_STAT:
			case LITERAL_synchronized:
			case LITERAL_if:
			case LITERAL_for:
			case LITERAL_while:
			case LITERAL_do:
			case LITERAL_break:
			case LITERAL_continue:
			case LITERAL_return:
			case LITERAL_switch:
			case LITERAL_throw:
			{
				moreStatExcept(_t);
				_t = _retTree;
				break;
			}
			default:
			{
				throw new NoViableAltException(_t);
			}
			}
		}
		catch (RecognitionException ex) {
			reportError(ex);
			if (_t!=null) {_t = _t.getNextSibling();}
		}
		_retTree = _t;
	}
	
	public final void elist(AST _t) throws RecognitionException {
		
		JavaAST elist_AST_in = (_t == ASTNULL) ? null : (JavaAST)_t;
		
		try {      // for error handling
			AST __t243 = _t;
			JavaAST tmp194_AST_in = (JavaAST)_t;
			match(_t,ELIST);
			_t = _t.getFirstChild();
			{
			if (_t==null) _t=ASTNULL;
			switch ( _t.getType()) {
			case TYPE:
			case CONCAT_ASSIGN:
			case CONCATENATION:
			case UNARY_MINUS:
			case UNARY_PLUS:
			case TYPECAST:
			case INDEX_OP:
			case METHOD_CALL:
			case CONSTRUCTOR_CALL:
			case POST_INC:
			case POST_DEC:
			case PAREN_EXPR:
			case IDENT:
			case DOT:
			case STAR:
			case ASSIGN:
			case PLUS_ASSIGN:
			case MINUS_ASSIGN:
			case STAR_ASSIGN:
			case DIV_ASSIGN:
			case MOD_ASSIGN:
			case SR_ASSIGN:
			case BSR_ASSIGN:
			case SL_ASSIGN:
			case BAND_ASSIGN:
			case BXOR_ASSIGN:
			case BOR_ASSIGN:
			case QUESTION:
			case LOR:
			case LAND:
			case BOR:
			case BXOR:
			case BAND:
			case NOT_EQUAL:
			case EQUAL:
			case LT:
			case GT:
			case LE:
			case GE:
			case LITERAL_instanceof:
			case SL:
			case SR:
			case BSR:
			case PLUS:
			case MINUS:
			case DIV:
			case MOD:
			case INC:
			case DEC:
			case BNOT:
			case LNOT:
			case LITERAL_this:
			case LITERAL_super:
			case LITERAL_true:
			case LITERAL_false:
			case LITERAL_null:
			case LITERAL_new:
			case NUM_INT:
			case CHAR_LITERAL:
			case STRING_LITERAL:
			case NUM_FLOAT:
			{
				expression(_t);
				_t = _retTree;
				{
				_loop246:
				do {
					if (_t==null) _t=ASTNULL;
					if ((_t.getType()==COMMA)) {
						JavaAST tmp195_AST_in = (JavaAST)_t;
						match(_t,COMMA);
						_t = _t.getNextSibling();
						tmp195_AST_in.print(out);
						expression(_t);
						_t = _retTree;
					}
					else {
						break _loop246;
					}
					
				} while (true);
				}
				break;
			}
			case 3:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(_t);
			}
			}
			}
			_t = __t243;
			_t = _t.getNextSibling();
		}
		catch (RecognitionException ex) {
			reportError(ex);
			if (_t!=null) {_t = _t.getNextSibling();}
		}
		_retTree = _t;
	}
	
	public final void caseGroup(AST _t) throws RecognitionException {
		
		JavaAST caseGroup_AST_in = (_t == ASTNULL) ? null : (JavaAST)_t;
		JavaAST c = null;
		JavaAST d = null;
		
		try {      // for error handling
			AST __t215 = _t;
			JavaAST tmp196_AST_in = (JavaAST)_t;
			match(_t,CASE_GROUP);
			_t = _t.getFirstChild();
			{
			int _cnt218=0;
			_loop218:
			do {
				if (_t==null) _t=ASTNULL;
				if ((_t.getType()==LITERAL_case||_t.getType()==LITERAL_default)) {
					{
					if (_t==null) _t=ASTNULL;
					switch ( _t.getType()) {
					case LITERAL_case:
					{
						c = (JavaAST)_t;
						match(_t,LITERAL_case);
						_t = _t.getNextSibling();
						c.print(out);
						expression(_t);
						_t = _retTree;
						break;
					}
					case LITERAL_default:
					{
						d = (JavaAST)_t;
						match(_t,LITERAL_default);
						_t = _t.getNextSibling();
						d.print(out);
						break;
					}
					default:
					{
						throw new NoViableAltException(_t);
					}
					}
					}
					JavaAST tmp197_AST_in = (JavaAST)_t;
					match(_t,COLON);
					_t = _t.getNextSibling();
					tmp197_AST_in.print(out);
				}
				else {
					if ( _cnt218>=1 ) { break _loop218; } else {throw new NoViableAltException(_t);}
				}
				
				_cnt218++;
			} while (true);
			}
			{
			_loop220:
			do {
				if (_t==null) _t=ASTNULL;
				if ((_tokenSet_0.member(_t.getType()))) {
					stat(_t);
					_t = _retTree;
				}
				else {
					break _loop220;
				}
				
			} while (true);
			}
			_t = __t215;
			_t = _t.getNextSibling();
		}
		catch (RecognitionException ex) {
			reportError(ex);
			if (_t!=null) {_t = _t.getNextSibling();}
		}
		_retTree = _t;
	}
	
	public final void tryBlock(AST _t) throws RecognitionException {
		
		JavaAST tryBlock_AST_in = (_t == ASTNULL) ? null : (JavaAST)_t;
		JavaAST t = null;
		JavaAST f = null;
		
		try {      // for error handling
			AST __t229 = _t;
			t = _t==ASTNULL ? null :(JavaAST)_t;
			match(_t,LITERAL_try);
			_t = _t.getFirstChild();
			t.print(out);
			slist(_t);
			_t = _retTree;
			{
			_loop231:
			do {
				if (_t==null) _t=ASTNULL;
				if ((_t.getType()==LITERAL_catch)) {
					handler(_t);
					_t = _retTree;
				}
				else {
					break _loop231;
				}
				
			} while (true);
			}
			{
			if (_t==null) _t=ASTNULL;
			switch ( _t.getType()) {
			case LITERAL_finally:
			{
				f = (JavaAST)_t;
				match(_t,LITERAL_finally);
				_t = _t.getNextSibling();
				f.print(out);
				slist(_t);
				_t = _retTree;
				break;
			}
			case 3:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(_t);
			}
			}
			}
			_t = __t229;
			_t = _t.getNextSibling();
		}
		catch (RecognitionException ex) {
			reportError(ex);
			if (_t!=null) {_t = _t.getNextSibling();}
		}
		_retTree = _t;
	}
	
	public final void tryBlockExcept(AST _t) throws RecognitionException {
		
		JavaAST tryBlockExcept_AST_in = (_t == ASTNULL) ? null : (JavaAST)_t;
		
		try {      // for error handling
			AST __t234 = _t;
			JavaAST tmp198_AST_in = (JavaAST)_t;
			match(_t,LITERAL_try);
			_t = _t.getFirstChild();
			slistExcept(_t);
			_t = _retTree;
			{
			_loop236:
			do {
				if (_t==null) _t=ASTNULL;
				if ((_t.getType()==LITERAL_catch)) {
					handlerExcept(_t);
					_t = _retTree;
				}
				else {
					break _loop236;
				}
				
			} while (true);
			}
			{
			if (_t==null) _t=ASTNULL;
			switch ( _t.getType()) {
			case LITERAL_finally:
			{
				JavaAST tmp199_AST_in = (JavaAST)_t;
				match(_t,LITERAL_finally);
				_t = _t.getNextSibling();
				slistExcept(_t);
				_t = _retTree;
				break;
			}
			case 3:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(_t);
			}
			}
			}
			_t = __t234;
			_t = _t.getNextSibling();
			
						tryBlock(tryBlockExcept_AST_in);
						printExceptions((HasExceptions)tryBlockExcept_AST_in);
					
		}
		catch (RecognitionException ex) {
			reportError(ex);
			if (_t!=null) {_t = _t.getNextSibling();}
		}
		_retTree = _t;
	}
	
	public final void moreStatExcept(AST _t) throws RecognitionException {
		
		JavaAST moreStatExcept_AST_in = (_t == ASTNULL) ? null : (JavaAST)_t;
		
		try {      // for error handling
			{
			if (_t==null) _t=ASTNULL;
			switch ( _t.getType()) {
			case TYPE_STAT:
			{
				AST __t190 = _t;
				JavaAST tmp200_AST_in = (JavaAST)_t;
				match(_t,TYPE_STAT);
				_t = _t.getFirstChild();
				typeDefinitionExcept(_t,true);
				_t = _retTree;
				_t = __t190;
				_t = _t.getNextSibling();
				break;
			}
			case EXPRESSION_STAT:
			{
				AST __t191 = _t;
				JavaAST tmp201_AST_in = (JavaAST)_t;
				match(_t,EXPRESSION_STAT);
				_t = _t.getFirstChild();
				expressionType(_t);
				_t = _retTree;
				JavaAST tmp202_AST_in = (JavaAST)_t;
				match(_t,SEMI);
				_t = _t.getNextSibling();
				_t = __t191;
				_t = _t.getNextSibling();
				break;
			}
			case LABELED_STAT:
			{
				AST __t192 = _t;
				JavaAST tmp203_AST_in = (JavaAST)_t;
				match(_t,LABELED_STAT);
				_t = _t.getFirstChild();
				JavaAST tmp204_AST_in = (JavaAST)_t;
				match(_t,COLON);
				_t = _t.getNextSibling();
				statExcept(_t);
				_t = _retTree;
				_t = __t192;
				_t = _t.getNextSibling();
				break;
			}
			case LITERAL_if:
			{
				AST __t193 = _t;
				JavaAST tmp205_AST_in = (JavaAST)_t;
				match(_t,LITERAL_if);
				_t = _t.getFirstChild();
				JavaAST tmp206_AST_in = (JavaAST)_t;
				match(_t,LPAREN);
				_t = _t.getNextSibling();
				expressionType(_t);
				_t = _retTree;
				JavaAST tmp207_AST_in = (JavaAST)_t;
				match(_t,RPAREN);
				_t = _t.getNextSibling();
				statExcept(_t);
				_t = _retTree;
				{
				if (_t==null) _t=ASTNULL;
				switch ( _t.getType()) {
				case LITERAL_else:
				{
					JavaAST tmp208_AST_in = (JavaAST)_t;
					match(_t,LITERAL_else);
					_t = _t.getNextSibling();
					statExcept(_t);
					_t = _retTree;
					break;
				}
				case 3:
				{
					break;
				}
				default:
				{
					throw new NoViableAltException(_t);
				}
				}
				}
				_t = __t193;
				_t = _t.getNextSibling();
				break;
			}
			case LITERAL_for:
			{
				AST __t195 = _t;
				JavaAST tmp209_AST_in = (JavaAST)_t;
				match(_t,LITERAL_for);
				_t = _t.getFirstChild();
				JavaAST tmp210_AST_in = (JavaAST)_t;
				match(_t,LPAREN);
				_t = _t.getNextSibling();
				AST __t196 = _t;
				JavaAST tmp211_AST_in = (JavaAST)_t;
				match(_t,FOR_INIT);
				_t = _t.getFirstChild();
				{
				if (_t==null) _t=ASTNULL;
				switch ( _t.getType()) {
				case VARIABLE_DEFS:
				{
					variableDefsExcept(_t);
					_t = _retTree;
					break;
				}
				case ELIST:
				{
					elistType(_t);
					_t = _retTree;
					JavaAST tmp212_AST_in = (JavaAST)_t;
					match(_t,SEMI);
					_t = _t.getNextSibling();
					break;
				}
				default:
				{
					throw new NoViableAltException(_t);
				}
				}
				}
				_t = __t196;
				_t = _t.getNextSibling();
				AST __t198 = _t;
				JavaAST tmp213_AST_in = (JavaAST)_t;
				match(_t,FOR_CONDITION);
				_t = _t.getFirstChild();
				{
				if (_t==null) _t=ASTNULL;
				switch ( _t.getType()) {
				case TYPE:
				case CONCAT_ASSIGN:
				case CONCATENATION:
				case UNARY_MINUS:
				case UNARY_PLUS:
				case TYPECAST:
				case INDEX_OP:
				case METHOD_CALL:
				case CONSTRUCTOR_CALL:
				case POST_INC:
				case POST_DEC:
				case PAREN_EXPR:
				case IDENT:
				case DOT:
				case STAR:
				case ASSIGN:
				case PLUS_ASSIGN:
				case MINUS_ASSIGN:
				case STAR_ASSIGN:
				case DIV_ASSIGN:
				case MOD_ASSIGN:
				case SR_ASSIGN:
				case BSR_ASSIGN:
				case SL_ASSIGN:
				case BAND_ASSIGN:
				case BXOR_ASSIGN:
				case BOR_ASSIGN:
				case QUESTION:
				case LOR:
				case LAND:
				case BOR:
				case BXOR:
				case BAND:
				case NOT_EQUAL:
				case EQUAL:
				case LT:
				case GT:
				case LE:
				case GE:
				case LITERAL_instanceof:
				case SL:
				case SR:
				case BSR:
				case PLUS:
				case MINUS:
				case DIV:
				case MOD:
				case INC:
				case DEC:
				case BNOT:
				case LNOT:
				case LITERAL_this:
				case LITERAL_super:
				case LITERAL_true:
				case LITERAL_false:
				case LITERAL_null:
				case LITERAL_new:
				case NUM_INT:
				case CHAR_LITERAL:
				case STRING_LITERAL:
				case NUM_FLOAT:
				{
					expressionType(_t);
					_t = _retTree;
					break;
				}
				case SEMI:
				{
					break;
				}
				default:
				{
					throw new NoViableAltException(_t);
				}
				}
				}
				JavaAST tmp214_AST_in = (JavaAST)_t;
				match(_t,SEMI);
				_t = _t.getNextSibling();
				_t = __t198;
				_t = _t.getNextSibling();
				AST __t200 = _t;
				JavaAST tmp215_AST_in = (JavaAST)_t;
				match(_t,FOR_ITERATOR);
				_t = _t.getFirstChild();
				elistType(_t);
				_t = _retTree;
				_t = __t200;
				_t = _t.getNextSibling();
				JavaAST tmp216_AST_in = (JavaAST)_t;
				match(_t,RPAREN);
				_t = _t.getNextSibling();
				statExcept(_t);
				_t = _retTree;
				_t = __t195;
				_t = _t.getNextSibling();
				break;
			}
			case LITERAL_while:
			{
				AST __t201 = _t;
				JavaAST tmp217_AST_in = (JavaAST)_t;
				match(_t,LITERAL_while);
				_t = _t.getFirstChild();
				JavaAST tmp218_AST_in = (JavaAST)_t;
				match(_t,LPAREN);
				_t = _t.getNextSibling();
				expressionType(_t);
				_t = _retTree;
				JavaAST tmp219_AST_in = (JavaAST)_t;
				match(_t,RPAREN);
				_t = _t.getNextSibling();
				statExcept(_t);
				_t = _retTree;
				_t = __t201;
				_t = _t.getNextSibling();
				break;
			}
			case LITERAL_do:
			{
				AST __t202 = _t;
				JavaAST tmp220_AST_in = (JavaAST)_t;
				match(_t,LITERAL_do);
				_t = _t.getFirstChild();
				statExcept(_t);
				_t = _retTree;
				JavaAST tmp221_AST_in = (JavaAST)_t;
				match(_t,LITERAL_while);
				_t = _t.getNextSibling();
				JavaAST tmp222_AST_in = (JavaAST)_t;
				match(_t,LPAREN);
				_t = _t.getNextSibling();
				expressionType(_t);
				_t = _retTree;
				JavaAST tmp223_AST_in = (JavaAST)_t;
				match(_t,RPAREN);
				_t = _t.getNextSibling();
				JavaAST tmp224_AST_in = (JavaAST)_t;
				match(_t,SEMI);
				_t = _t.getNextSibling();
				_t = __t202;
				_t = _t.getNextSibling();
				break;
			}
			case LITERAL_break:
			{
				AST __t203 = _t;
				JavaAST tmp225_AST_in = (JavaAST)_t;
				match(_t,LITERAL_break);
				_t = _t.getFirstChild();
				{
				if (_t==null) _t=ASTNULL;
				switch ( _t.getType()) {
				case IDENT:
				{
					JavaAST tmp226_AST_in = (JavaAST)_t;
					match(_t,IDENT);
					_t = _t.getNextSibling();
					break;
				}
				case SEMI:
				{
					break;
				}
				default:
				{
					throw new NoViableAltException(_t);
				}
				}
				}
				JavaAST tmp227_AST_in = (JavaAST)_t;
				match(_t,SEMI);
				_t = _t.getNextSibling();
				_t = __t203;
				_t = _t.getNextSibling();
				break;
			}
			case LITERAL_continue:
			{
				AST __t205 = _t;
				JavaAST tmp228_AST_in = (JavaAST)_t;
				match(_t,LITERAL_continue);
				_t = _t.getFirstChild();
				{
				if (_t==null) _t=ASTNULL;
				switch ( _t.getType()) {
				case IDENT:
				{
					JavaAST tmp229_AST_in = (JavaAST)_t;
					match(_t,IDENT);
					_t = _t.getNextSibling();
					break;
				}
				case SEMI:
				{
					break;
				}
				default:
				{
					throw new NoViableAltException(_t);
				}
				}
				}
				JavaAST tmp230_AST_in = (JavaAST)_t;
				match(_t,SEMI);
				_t = _t.getNextSibling();
				_t = __t205;
				_t = _t.getNextSibling();
				break;
			}
			case LITERAL_return:
			{
				AST __t207 = _t;
				JavaAST tmp231_AST_in = (JavaAST)_t;
				match(_t,LITERAL_return);
				_t = _t.getFirstChild();
				{
				if (_t==null) _t=ASTNULL;
				switch ( _t.getType()) {
				case TYPE:
				case CONCAT_ASSIGN:
				case CONCATENATION:
				case UNARY_MINUS:
				case UNARY_PLUS:
				case TYPECAST:
				case INDEX_OP:
				case METHOD_CALL:
				case CONSTRUCTOR_CALL:
				case POST_INC:
				case POST_DEC:
				case PAREN_EXPR:
				case IDENT:
				case DOT:
				case STAR:
				case ASSIGN:
				case PLUS_ASSIGN:
				case MINUS_ASSIGN:
				case STAR_ASSIGN:
				case DIV_ASSIGN:
				case MOD_ASSIGN:
				case SR_ASSIGN:
				case BSR_ASSIGN:
				case SL_ASSIGN:
				case BAND_ASSIGN:
				case BXOR_ASSIGN:
				case BOR_ASSIGN:
				case QUESTION:
				case LOR:
				case LAND:
				case BOR:
				case BXOR:
				case BAND:
				case NOT_EQUAL:
				case EQUAL:
				case LT:
				case GT:
				case LE:
				case GE:
				case LITERAL_instanceof:
				case SL:
				case SR:
				case BSR:
				case PLUS:
				case MINUS:
				case DIV:
				case MOD:
				case INC:
				case DEC:
				case BNOT:
				case LNOT:
				case LITERAL_this:
				case LITERAL_super:
				case LITERAL_true:
				case LITERAL_false:
				case LITERAL_null:
				case LITERAL_new:
				case NUM_INT:
				case CHAR_LITERAL:
				case STRING_LITERAL:
				case NUM_FLOAT:
				{
					expressionType(_t);
					_t = _retTree;
					break;
				}
				case SEMI:
				{
					break;
				}
				default:
				{
					throw new NoViableAltException(_t);
				}
				}
				}
				JavaAST tmp232_AST_in = (JavaAST)_t;
				match(_t,SEMI);
				_t = _t.getNextSibling();
				_t = __t207;
				_t = _t.getNextSibling();
				break;
			}
			case LITERAL_switch:
			{
				AST __t209 = _t;
				JavaAST tmp233_AST_in = (JavaAST)_t;
				match(_t,LITERAL_switch);
				_t = _t.getFirstChild();
				JavaAST tmp234_AST_in = (JavaAST)_t;
				match(_t,LPAREN);
				_t = _t.getNextSibling();
				expressionType(_t);
				_t = _retTree;
				JavaAST tmp235_AST_in = (JavaAST)_t;
				match(_t,RPAREN);
				_t = _t.getNextSibling();
				JavaAST tmp236_AST_in = (JavaAST)_t;
				match(_t,LCURLY);
				_t = _t.getNextSibling();
				{
				_loop211:
				do {
					if (_t==null) _t=ASTNULL;
					if ((_t.getType()==CASE_GROUP)) {
						caseGroupExcept(_t);
						_t = _retTree;
					}
					else {
						break _loop211;
					}
					
				} while (true);
				}
				JavaAST tmp237_AST_in = (JavaAST)_t;
				match(_t,RCURLY);
				_t = _t.getNextSibling();
				_t = __t209;
				_t = _t.getNextSibling();
				break;
			}
			case LITERAL_throw:
			{
				AST __t212 = _t;
				JavaAST tmp238_AST_in = (JavaAST)_t;
				match(_t,LITERAL_throw);
				_t = _t.getFirstChild();
				expressionType(_t);
				_t = _retTree;
				JavaAST tmp239_AST_in = (JavaAST)_t;
				match(_t,SEMI);
				_t = _t.getNextSibling();
				_t = __t212;
				_t = _t.getNextSibling();
				break;
			}
			case LITERAL_synchronized:
			{
				AST __t213 = _t;
				JavaAST tmp240_AST_in = (JavaAST)_t;
				match(_t,LITERAL_synchronized);
				_t = _t.getFirstChild();
				JavaAST tmp241_AST_in = (JavaAST)_t;
				match(_t,LPAREN);
				_t = _t.getNextSibling();
				expressionType(_t);
				_t = _retTree;
				JavaAST tmp242_AST_in = (JavaAST)_t;
				match(_t,RPAREN);
				_t = _t.getNextSibling();
				statExcept(_t);
				_t = _retTree;
				_t = __t213;
				_t = _t.getNextSibling();
				break;
			}
			case EMPTY_STAT:
			{
				JavaAST tmp243_AST_in = (JavaAST)_t;
				match(_t,EMPTY_STAT);
				_t = _t.getNextSibling();
				break;
			}
			default:
			{
				throw new NoViableAltException(_t);
			}
			}
			}
			
						stat(moreStatExcept_AST_in);
						printExceptions((HasExceptions)moreStatExcept_AST_in);
					
		}
		catch (RecognitionException ex) {
			reportError(ex);
			if (_t!=null) {_t = _t.getNextSibling();}
		}
		_retTree = _t;
	}
	
	public final void elistType(AST _t) throws RecognitionException {
		
		JavaAST elistType_AST_in = (_t == ASTNULL) ? null : (JavaAST)_t;
		
		try {      // for error handling
			AST __t248 = _t;
			JavaAST tmp244_AST_in = (JavaAST)_t;
			match(_t,ELIST);
			_t = _t.getFirstChild();
			{
			if (_t==null) _t=ASTNULL;
			switch ( _t.getType()) {
			case TYPE:
			case CONCAT_ASSIGN:
			case CONCATENATION:
			case UNARY_MINUS:
			case UNARY_PLUS:
			case TYPECAST:
			case INDEX_OP:
			case METHOD_CALL:
			case CONSTRUCTOR_CALL:
			case POST_INC:
			case POST_DEC:
			case PAREN_EXPR:
			case IDENT:
			case DOT:
			case STAR:
			case ASSIGN:
			case PLUS_ASSIGN:
			case MINUS_ASSIGN:
			case STAR_ASSIGN:
			case DIV_ASSIGN:
			case MOD_ASSIGN:
			case SR_ASSIGN:
			case BSR_ASSIGN:
			case SL_ASSIGN:
			case BAND_ASSIGN:
			case BXOR_ASSIGN:
			case BOR_ASSIGN:
			case QUESTION:
			case LOR:
			case LAND:
			case BOR:
			case BXOR:
			case BAND:
			case NOT_EQUAL:
			case EQUAL:
			case LT:
			case GT:
			case LE:
			case GE:
			case LITERAL_instanceof:
			case SL:
			case SR:
			case BSR:
			case PLUS:
			case MINUS:
			case DIV:
			case MOD:
			case INC:
			case DEC:
			case BNOT:
			case LNOT:
			case LITERAL_this:
			case LITERAL_super:
			case LITERAL_true:
			case LITERAL_false:
			case LITERAL_null:
			case LITERAL_new:
			case NUM_INT:
			case CHAR_LITERAL:
			case STRING_LITERAL:
			case NUM_FLOAT:
			{
				expressionType(_t);
				_t = _retTree;
				{
				_loop251:
				do {
					if (_t==null) _t=ASTNULL;
					if ((_t.getType()==COMMA)) {
						JavaAST tmp245_AST_in = (JavaAST)_t;
						match(_t,COMMA);
						_t = _t.getNextSibling();
						expressionType(_t);
						_t = _retTree;
					}
					else {
						break _loop251;
					}
					
				} while (true);
				}
				break;
			}
			case 3:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(_t);
			}
			}
			}
			_t = __t248;
			_t = _t.getNextSibling();
		}
		catch (RecognitionException ex) {
			reportError(ex);
			if (_t!=null) {_t = _t.getNextSibling();}
		}
		_retTree = _t;
	}
	
	public final void caseGroupExcept(AST _t) throws RecognitionException {
		
		JavaAST caseGroupExcept_AST_in = (_t == ASTNULL) ? null : (JavaAST)_t;
		
		try {      // for error handling
			AST __t222 = _t;
			JavaAST tmp246_AST_in = (JavaAST)_t;
			match(_t,CASE_GROUP);
			_t = _t.getFirstChild();
			{
			int _cnt225=0;
			_loop225:
			do {
				if (_t==null) _t=ASTNULL;
				if ((_t.getType()==LITERAL_case||_t.getType()==LITERAL_default)) {
					{
					if (_t==null) _t=ASTNULL;
					switch ( _t.getType()) {
					case LITERAL_case:
					{
						JavaAST tmp247_AST_in = (JavaAST)_t;
						match(_t,LITERAL_case);
						_t = _t.getNextSibling();
						expressionType(_t);
						_t = _retTree;
						break;
					}
					case LITERAL_default:
					{
						JavaAST tmp248_AST_in = (JavaAST)_t;
						match(_t,LITERAL_default);
						_t = _t.getNextSibling();
						break;
					}
					default:
					{
						throw new NoViableAltException(_t);
					}
					}
					}
					JavaAST tmp249_AST_in = (JavaAST)_t;
					match(_t,COLON);
					_t = _t.getNextSibling();
				}
				else {
					if ( _cnt225>=1 ) { break _loop225; } else {throw new NoViableAltException(_t);}
				}
				
				_cnt225++;
			} while (true);
			}
			{
			_loop227:
			do {
				if (_t==null) _t=ASTNULL;
				if ((_tokenSet_1.member(_t.getType()))) {
					statExcept(_t);
					_t = _retTree;
				}
				else {
					break _loop227;
				}
				
			} while (true);
			}
			_t = __t222;
			_t = _t.getNextSibling();
				caseGroup(caseGroupExcept_AST_in);
		}
		catch (RecognitionException ex) {
			reportError(ex);
			if (_t!=null) {_t = _t.getNextSibling();}
		}
		_retTree = _t;
	}
	
	public final void handler(AST _t) throws RecognitionException {
		
		JavaAST handler_AST_in = (_t == ASTNULL) ? null : (JavaAST)_t;
		JavaAST c = null;
		
		try {      // for error handling
			AST __t239 = _t;
			c = _t==ASTNULL ? null :(JavaAST)_t;
			match(_t,LITERAL_catch);
			_t = _t.getFirstChild();
			JavaAST tmp250_AST_in = (JavaAST)_t;
			match(_t,LPAREN);
			_t = _t.getNextSibling();
			c.print(out); tmp250_AST_in.print(out);
			parameterDef(_t);
			_t = _retTree;
			JavaAST tmp251_AST_in = (JavaAST)_t;
			match(_t,RPAREN);
			_t = _t.getNextSibling();
			tmp251_AST_in.print(out);
			slist(_t);
			_t = _retTree;
			_t = __t239;
			_t = _t.getNextSibling();
		}
		catch (RecognitionException ex) {
			reportError(ex);
			if (_t!=null) {_t = _t.getNextSibling();}
		}
		_retTree = _t;
	}
	
	public final void handlerExcept(AST _t) throws RecognitionException {
		
		JavaAST handlerExcept_AST_in = (_t == ASTNULL) ? null : (JavaAST)_t;
		
		try {      // for error handling
			AST __t241 = _t;
			JavaAST tmp252_AST_in = (JavaAST)_t;
			match(_t,LITERAL_catch);
			_t = _t.getFirstChild();
			JavaAST tmp253_AST_in = (JavaAST)_t;
			match(_t,LPAREN);
			_t = _t.getNextSibling();
			parameterDefExcept(_t);
			_t = _retTree;
			JavaAST tmp254_AST_in = (JavaAST)_t;
			match(_t,RPAREN);
			_t = _t.getNextSibling();
			slistExcept(_t);
			_t = _retTree;
			_t = __t241;
			_t = _t.getNextSibling();
			
						handler(handlerExcept_AST_in);
						printExceptions((HasExceptions)handlerExcept_AST_in);
					
		}
		catch (RecognitionException ex) {
			reportError(ex);
			if (_t!=null) {_t = _t.getNextSibling();}
		}
		_retTree = _t;
	}
	
	public final void primaryExpression(AST _t) throws RecognitionException {
		
		JavaAST primaryExpression_AST_in = (_t == ASTNULL) ? null : (JavaAST)_t;
		JavaAST d = null;
		JavaAST th = null;
		JavaAST c = null;
		JavaAST ne = null;
		JavaAST lp = null;
		JavaAST rp = null;
		JavaAST su = null;
		JavaAST cl = null;
		JavaAST cl2 = null;
		JavaAST call1 = null;
		JavaAST r2 = null;
		JavaAST call2 = null;
		JavaAST r3 = null;
		JavaAST t = null;
		JavaAST r4 = null;
		JavaAST p = null;
		JavaAST r5 = null;
		JavaAST s = null;
		JavaAST tr = null;
		JavaAST f = null;
		JavaAST thi = null;
		JavaAST nu = null;
		
		try {      // for error handling
			if (_t==null) _t=ASTNULL;
			switch ( _t.getType()) {
			case IDENT:
			{
				JavaAST tmp255_AST_in = (JavaAST)_t;
				match(_t,IDENT);
				_t = _t.getNextSibling();
				tmp255_AST_in.print(out);
				break;
			}
			case DOT:
			{
				AST __t342 = _t;
				d = _t==ASTNULL ? null :(JavaAST)_t;
				match(_t,DOT);
				_t = _t.getFirstChild();
				{
				if (_t==null) _t=ASTNULL;
				switch ( _t.getType()) {
				case TYPE:
				case CONCAT_ASSIGN:
				case CONCATENATION:
				case UNARY_MINUS:
				case UNARY_PLUS:
				case TYPECAST:
				case INDEX_OP:
				case METHOD_CALL:
				case CONSTRUCTOR_CALL:
				case POST_INC:
				case POST_DEC:
				case PAREN_EXPR:
				case IDENT:
				case DOT:
				case STAR:
				case ASSIGN:
				case PLUS_ASSIGN:
				case MINUS_ASSIGN:
				case STAR_ASSIGN:
				case DIV_ASSIGN:
				case MOD_ASSIGN:
				case SR_ASSIGN:
				case BSR_ASSIGN:
				case SL_ASSIGN:
				case BAND_ASSIGN:
				case BXOR_ASSIGN:
				case BOR_ASSIGN:
				case QUESTION:
				case LOR:
				case LAND:
				case BOR:
				case BXOR:
				case BAND:
				case NOT_EQUAL:
				case EQUAL:
				case LT:
				case GT:
				case LE:
				case GE:
				case LITERAL_instanceof:
				case SL:
				case SR:
				case BSR:
				case PLUS:
				case MINUS:
				case DIV:
				case MOD:
				case INC:
				case DEC:
				case BNOT:
				case LNOT:
				case LITERAL_this:
				case LITERAL_super:
				case LITERAL_true:
				case LITERAL_false:
				case LITERAL_null:
				case LITERAL_new:
				case NUM_INT:
				case CHAR_LITERAL:
				case STRING_LITERAL:
				case NUM_FLOAT:
				{
					expression(_t);
					_t = _retTree;
					d.print(out);
					{
					if (_t==null) _t=ASTNULL;
					switch ( _t.getType()) {
					case IDENT:
					{
						JavaAST tmp256_AST_in = (JavaAST)_t;
						match(_t,IDENT);
						_t = _t.getNextSibling();
						tmp256_AST_in.print(out);
						break;
					}
					case INDEX_OP:
					{
						arrayIndex(_t);
						_t = _retTree;
						break;
					}
					case LITERAL_this:
					{
						th = (JavaAST)_t;
						match(_t,LITERAL_this);
						_t = _t.getNextSibling();
						th.print(out);
						break;
					}
					case LITERAL_class:
					{
						c = (JavaAST)_t;
						match(_t,LITERAL_class);
						_t = _t.getNextSibling();
						c.print(out);
						break;
					}
					case LITERAL_new:
					{
						AST __t345 = _t;
						ne = _t==ASTNULL ? null :(JavaAST)_t;
						match(_t,LITERAL_new);
						_t = _t.getFirstChild();
						JavaAST tmp257_AST_in = (JavaAST)_t;
						match(_t,IDENT);
						_t = _t.getNextSibling();
						ne.print(out); tmp257_AST_in.print(out);
						lp = (JavaAST)_t;
						match(_t,LPAREN);
						_t = _t.getNextSibling();
						lp.print(out);
						elist(_t);
						_t = _retTree;
						rp = (JavaAST)_t;
						match(_t,RPAREN);
						_t = _t.getNextSibling();
						rp.print(out);
						_t = __t345;
						_t = _t.getNextSibling();
						break;
					}
					case LITERAL_super:
					{
						su = (JavaAST)_t;
						match(_t,LITERAL_super);
						_t = _t.getNextSibling();
						su.print(out);
						break;
					}
					default:
					{
						throw new NoViableAltException(_t);
					}
					}
					}
					break;
				}
				case ARRAY_DECLARATOR:
				{
					AST __t346 = _t;
					JavaAST tmp258_AST_in = (JavaAST)_t;
					match(_t,ARRAY_DECLARATOR);
					_t = _t.getFirstChild();
					type(_t,true);
					_t = _retTree;
					JavaAST tmp259_AST_in = (JavaAST)_t;
					match(_t,RBRACK);
					_t = _t.getNextSibling();
					_t = __t346;
					_t = _t.getNextSibling();
					tmp258_AST_in.print(out); tmp259_AST_in.print(out);
					{
					if (_t==null) _t=ASTNULL;
					switch ( _t.getType()) {
					case LITERAL_class:
					{
						cl = (JavaAST)_t;
						match(_t,LITERAL_class);
						_t = _t.getNextSibling();
						d.print(out); cl.print(out);
						break;
					}
					case 3:
					{
						break;
					}
					default:
					{
						throw new NoViableAltException(_t);
					}
					}
					}
					break;
				}
				case LITERAL_void:
				case LITERAL_boolean:
				case LITERAL_byte:
				case LITERAL_char:
				case LITERAL_short:
				case LITERAL_int:
				case LITERAL_float:
				case LITERAL_long:
				case LITERAL_double:
				{
					builtInType(_t,true);
					_t = _retTree;
					{
					if (_t==null) _t=ASTNULL;
					switch ( _t.getType()) {
					case LITERAL_class:
					{
						cl2 = (JavaAST)_t;
						match(_t,LITERAL_class);
						_t = _t.getNextSibling();
						d.print(out); cl2.print(out);
						break;
					}
					case 3:
					{
						break;
					}
					default:
					{
						throw new NoViableAltException(_t);
					}
					}
					}
					break;
				}
				default:
				{
					throw new NoViableAltException(_t);
				}
				}
				}
				_t = __t342;
				_t = _t.getNextSibling();
				break;
			}
			case INDEX_OP:
			{
				arrayIndex(_t);
				_t = _retTree;
				break;
			}
			case METHOD_CALL:
			{
				AST __t349 = _t;
				call1 = _t==ASTNULL ? null :(JavaAST)_t;
				match(_t,METHOD_CALL);
				_t = _t.getFirstChild();
				primaryExpression(_t);
				_t = _retTree;
				call1.print(out);
				elist(_t);
				_t = _retTree;
				r2 = (JavaAST)_t;
				match(_t,RPAREN);
				_t = _t.getNextSibling();
				r2.print(out);
				_t = __t349;
				_t = _t.getNextSibling();
				break;
			}
			case CONSTRUCTOR_CALL:
			{
				AST __t350 = _t;
				call2 = _t==ASTNULL ? null :(JavaAST)_t;
				match(_t,CONSTRUCTOR_CALL);
				_t = _t.getFirstChild();
				primaryExpression(_t);
				_t = _retTree;
				call2.print(out);
				elist(_t);
				_t = _retTree;
				r3 = (JavaAST)_t;
				match(_t,RPAREN);
				_t = _t.getNextSibling();
				r3.print(out);
				_t = __t350;
				_t = _t.getNextSibling();
				break;
			}
			case TYPECAST:
			{
				AST __t351 = _t;
				t = _t==ASTNULL ? null :(JavaAST)_t;
				match(_t,TYPECAST);
				_t = _t.getFirstChild();
				t.print(out);
				typeSpec(_t,true);
				_t = _retTree;
				r4 = (JavaAST)_t;
				match(_t,RPAREN);
				_t = _t.getNextSibling();
				r4.print(out);
				expression(_t);
				_t = _retTree;
				_t = __t351;
				_t = _t.getNextSibling();
				break;
			}
			case PAREN_EXPR:
			{
				AST __t352 = _t;
				p = _t==ASTNULL ? null :(JavaAST)_t;
				match(_t,PAREN_EXPR);
				_t = _t.getFirstChild();
				p.print(out);
				expression(_t);
				_t = _retTree;
				r5 = (JavaAST)_t;
				match(_t,RPAREN);
				_t = _t.getNextSibling();
				r5.print(out);
				_t = __t352;
				_t = _t.getNextSibling();
				break;
			}
			case LITERAL_new:
			{
				newExpression(_t);
				_t = _retTree;
				break;
			}
			case NUM_INT:
			case CHAR_LITERAL:
			case STRING_LITERAL:
			case NUM_FLOAT:
			{
				constant(_t);
				_t = _retTree;
				break;
			}
			case LITERAL_super:
			{
				s = (JavaAST)_t;
				match(_t,LITERAL_super);
				_t = _t.getNextSibling();
				s.print(out);
				break;
			}
			case LITERAL_true:
			{
				tr = (JavaAST)_t;
				match(_t,LITERAL_true);
				_t = _t.getNextSibling();
				tr.print(out);
				break;
			}
			case LITERAL_false:
			{
				f = (JavaAST)_t;
				match(_t,LITERAL_false);
				_t = _t.getNextSibling();
				f.print(out);
				break;
			}
			case LITERAL_this:
			{
				thi = (JavaAST)_t;
				match(_t,LITERAL_this);
				_t = _t.getNextSibling();
				thi.print(out);
				break;
			}
			case LITERAL_null:
			{
				nu = (JavaAST)_t;
				match(_t,LITERAL_null);
				_t = _t.getNextSibling();
				nu.print(out);
				break;
			}
			case TYPE:
			{
				typeSpec(_t,true);
				_t = _retTree;
				break;
			}
			default:
			{
				throw new NoViableAltException(_t);
			}
			}
		}
		catch (RecognitionException ex) {
			reportError(ex);
			if (_t!=null) {_t = _t.getNextSibling();}
		}
		_retTree = _t;
	}
	
	public final void primaryExpressionType(AST _t) throws RecognitionException {
		
		JavaAST primaryExpressionType_AST_in = (_t == ASTNULL) ? null : (JavaAST)_t;
		
		try {      // for error handling
			if (_t==null) _t=ASTNULL;
			switch ( _t.getType()) {
			case TYPECAST:
			case METHOD_CALL:
			case CONSTRUCTOR_CALL:
			case PAREN_EXPR:
			case IDENT:
			case DOT:
			case LITERAL_this:
			case LITERAL_super:
			case LITERAL_true:
			case LITERAL_false:
			case LITERAL_null:
			{
				{
				if (_t==null) _t=ASTNULL;
				switch ( _t.getType()) {
				case IDENT:
				{
					JavaAST tmp260_AST_in = (JavaAST)_t;
					match(_t,IDENT);
					_t = _t.getNextSibling();
					break;
				}
				case DOT:
				{
					AST __t355 = _t;
					JavaAST tmp261_AST_in = (JavaAST)_t;
					match(_t,DOT);
					_t = _t.getFirstChild();
					{
					if (_t==null) _t=ASTNULL;
					switch ( _t.getType()) {
					case TYPE:
					case CONCAT_ASSIGN:
					case CONCATENATION:
					case UNARY_MINUS:
					case UNARY_PLUS:
					case TYPECAST:
					case INDEX_OP:
					case METHOD_CALL:
					case CONSTRUCTOR_CALL:
					case POST_INC:
					case POST_DEC:
					case PAREN_EXPR:
					case IDENT:
					case DOT:
					case STAR:
					case ASSIGN:
					case PLUS_ASSIGN:
					case MINUS_ASSIGN:
					case STAR_ASSIGN:
					case DIV_ASSIGN:
					case MOD_ASSIGN:
					case SR_ASSIGN:
					case BSR_ASSIGN:
					case SL_ASSIGN:
					case BAND_ASSIGN:
					case BXOR_ASSIGN:
					case BOR_ASSIGN:
					case QUESTION:
					case LOR:
					case LAND:
					case BOR:
					case BXOR:
					case BAND:
					case NOT_EQUAL:
					case EQUAL:
					case LT:
					case GT:
					case LE:
					case GE:
					case LITERAL_instanceof:
					case SL:
					case SR:
					case BSR:
					case PLUS:
					case MINUS:
					case DIV:
					case MOD:
					case INC:
					case DEC:
					case BNOT:
					case LNOT:
					case LITERAL_this:
					case LITERAL_super:
					case LITERAL_true:
					case LITERAL_false:
					case LITERAL_null:
					case LITERAL_new:
					case NUM_INT:
					case CHAR_LITERAL:
					case STRING_LITERAL:
					case NUM_FLOAT:
					{
						expressionType(_t);
						_t = _retTree;
						{
						if (_t==null) _t=ASTNULL;
						switch ( _t.getType()) {
						case IDENT:
						{
							JavaAST tmp262_AST_in = (JavaAST)_t;
							match(_t,IDENT);
							_t = _t.getNextSibling();
							break;
						}
						case INDEX_OP:
						{
							arrayIndexType(_t);
							_t = _retTree;
							break;
						}
						case LITERAL_this:
						{
							JavaAST tmp263_AST_in = (JavaAST)_t;
							match(_t,LITERAL_this);
							_t = _t.getNextSibling();
							break;
						}
						case LITERAL_class:
						{
							JavaAST tmp264_AST_in = (JavaAST)_t;
							match(_t,LITERAL_class);
							_t = _t.getNextSibling();
							break;
						}
						case LITERAL_new:
						{
							AST __t358 = _t;
							JavaAST tmp265_AST_in = (JavaAST)_t;
							match(_t,LITERAL_new);
							_t = _t.getFirstChild();
							JavaAST tmp266_AST_in = (JavaAST)_t;
							match(_t,IDENT);
							_t = _t.getNextSibling();
							JavaAST tmp267_AST_in = (JavaAST)_t;
							match(_t,LPAREN);
							_t = _t.getNextSibling();
							elistType(_t);
							_t = _retTree;
							JavaAST tmp268_AST_in = (JavaAST)_t;
							match(_t,RPAREN);
							_t = _t.getNextSibling();
							_t = __t358;
							_t = _t.getNextSibling();
							break;
						}
						case LITERAL_super:
						{
							JavaAST tmp269_AST_in = (JavaAST)_t;
							match(_t,LITERAL_super);
							_t = _t.getNextSibling();
							break;
						}
						default:
						{
							throw new NoViableAltException(_t);
						}
						}
						}
						break;
					}
					case ARRAY_DECLARATOR:
					{
						AST __t359 = _t;
						JavaAST tmp270_AST_in = (JavaAST)_t;
						match(_t,ARRAY_DECLARATOR);
						_t = _t.getFirstChild();
						typeType(_t);
						_t = _retTree;
						JavaAST tmp271_AST_in = (JavaAST)_t;
						match(_t,RBRACK);
						_t = _t.getNextSibling();
						_t = __t359;
						_t = _t.getNextSibling();
						{
						if (_t==null) _t=ASTNULL;
						switch ( _t.getType()) {
						case LITERAL_class:
						{
							JavaAST tmp272_AST_in = (JavaAST)_t;
							match(_t,LITERAL_class);
							_t = _t.getNextSibling();
							break;
						}
						case 3:
						{
							break;
						}
						default:
						{
							throw new NoViableAltException(_t);
						}
						}
						}
						break;
					}
					case LITERAL_void:
					case LITERAL_boolean:
					case LITERAL_byte:
					case LITERAL_char:
					case LITERAL_short:
					case LITERAL_int:
					case LITERAL_float:
					case LITERAL_long:
					case LITERAL_double:
					{
						builtInTypeType(_t);
						_t = _retTree;
						{
						if (_t==null) _t=ASTNULL;
						switch ( _t.getType()) {
						case LITERAL_class:
						{
							JavaAST tmp273_AST_in = (JavaAST)_t;
							match(_t,LITERAL_class);
							_t = _t.getNextSibling();
							break;
						}
						case 3:
						{
							break;
						}
						default:
						{
							throw new NoViableAltException(_t);
						}
						}
						}
						break;
					}
					default:
					{
						throw new NoViableAltException(_t);
					}
					}
					}
					_t = __t355;
					_t = _t.getNextSibling();
					break;
				}
				case METHOD_CALL:
				{
					AST __t362 = _t;
					JavaAST tmp274_AST_in = (JavaAST)_t;
					match(_t,METHOD_CALL);
					_t = _t.getFirstChild();
					primaryExpressionType(_t);
					_t = _retTree;
					elistType(_t);
					_t = _retTree;
					JavaAST tmp275_AST_in = (JavaAST)_t;
					match(_t,RPAREN);
					_t = _t.getNextSibling();
					_t = __t362;
					_t = _t.getNextSibling();
					break;
				}
				case CONSTRUCTOR_CALL:
				{
					AST __t363 = _t;
					JavaAST tmp276_AST_in = (JavaAST)_t;
					match(_t,CONSTRUCTOR_CALL);
					_t = _t.getFirstChild();
					primaryExpressionType(_t);
					_t = _retTree;
					elistType(_t);
					_t = _retTree;
					JavaAST tmp277_AST_in = (JavaAST)_t;
					match(_t,RPAREN);
					_t = _t.getNextSibling();
					_t = __t363;
					_t = _t.getNextSibling();
					break;
				}
				case TYPECAST:
				{
					AST __t364 = _t;
					JavaAST tmp278_AST_in = (JavaAST)_t;
					match(_t,TYPECAST);
					_t = _t.getFirstChild();
					typeSpecType(_t);
					_t = _retTree;
					JavaAST tmp279_AST_in = (JavaAST)_t;
					match(_t,RPAREN);
					_t = _t.getNextSibling();
					expressionType(_t);
					_t = _retTree;
					_t = __t364;
					_t = _t.getNextSibling();
					break;
				}
				case PAREN_EXPR:
				{
					AST __t365 = _t;
					JavaAST tmp280_AST_in = (JavaAST)_t;
					match(_t,PAREN_EXPR);
					_t = _t.getFirstChild();
					expressionType(_t);
					_t = _retTree;
					JavaAST tmp281_AST_in = (JavaAST)_t;
					match(_t,RPAREN);
					_t = _t.getNextSibling();
					_t = __t365;
					_t = _t.getNextSibling();
					break;
				}
				case LITERAL_super:
				{
					JavaAST tmp282_AST_in = (JavaAST)_t;
					match(_t,LITERAL_super);
					_t = _t.getNextSibling();
					break;
				}
				case LITERAL_true:
				{
					JavaAST tmp283_AST_in = (JavaAST)_t;
					match(_t,LITERAL_true);
					_t = _t.getNextSibling();
					break;
				}
				case LITERAL_false:
				{
					JavaAST tmp284_AST_in = (JavaAST)_t;
					match(_t,LITERAL_false);
					_t = _t.getNextSibling();
					break;
				}
				case LITERAL_this:
				{
					JavaAST tmp285_AST_in = (JavaAST)_t;
					match(_t,LITERAL_this);
					_t = _t.getNextSibling();
					break;
				}
				case LITERAL_null:
				{
					JavaAST tmp286_AST_in = (JavaAST)_t;
					match(_t,LITERAL_null);
					_t = _t.getNextSibling();
					break;
				}
				default:
				{
					throw new NoViableAltException(_t);
				}
				}
				}
				
							primaryExpression(primaryExpressionType_AST_in);
							printType(primaryExpressionType_AST_in);
						
				break;
			}
			case INDEX_OP:
			{
				arrayIndexType(_t);
				_t = _retTree;
				break;
			}
			case LITERAL_new:
			{
				newExpressionType(_t);
				_t = _retTree;
				break;
			}
			case NUM_INT:
			case CHAR_LITERAL:
			case STRING_LITERAL:
			case NUM_FLOAT:
			{
				constantType(_t);
				_t = _retTree;
				break;
			}
			case TYPE:
			{
				typeSpecType(_t);
				_t = _retTree;
				break;
			}
			default:
			{
				throw new NoViableAltException(_t);
			}
			}
		}
		catch (RecognitionException ex) {
			reportError(ex);
			if (_t!=null) {_t = _t.getNextSibling();}
		}
		_retTree = _t;
	}
	
	public final void arrayIndex(AST _t) throws RecognitionException {
		
		JavaAST arrayIndex_AST_in = (_t == ASTNULL) ? null : (JavaAST)_t;
		
		try {      // for error handling
			AST __t367 = _t;
			JavaAST tmp287_AST_in = (JavaAST)_t;
			match(_t,INDEX_OP);
			_t = _t.getFirstChild();
			primaryExpression(_t);
			_t = _retTree;
			tmp287_AST_in.print(out);
			expression(_t);
			_t = _retTree;
			JavaAST tmp288_AST_in = (JavaAST)_t;
			match(_t,RBRACK);
			_t = _t.getNextSibling();
			tmp288_AST_in.print(out);
			_t = __t367;
			_t = _t.getNextSibling();
		}
		catch (RecognitionException ex) {
			reportError(ex);
			if (_t!=null) {_t = _t.getNextSibling();}
		}
		_retTree = _t;
	}
	
	public final void newExpression(AST _t) throws RecognitionException {
		
		JavaAST newExpression_AST_in = (_t == ASTNULL) ? null : (JavaAST)_t;
		JavaAST n = null;
		
		try {      // for error handling
			AST __t373 = _t;
			n = _t==ASTNULL ? null :(JavaAST)_t;
			match(_t,LITERAL_new);
			_t = _t.getFirstChild();
			n.print(out);
			type(_t,true);
			_t = _retTree;
			{
			if (_t==null) _t=ASTNULL;
			switch ( _t.getType()) {
			case ARRAY_DECLARATOR:
			{
				newArrayDeclarator(_t);
				_t = _retTree;
				{
				if (_t==null) _t=ASTNULL;
				switch ( _t.getType()) {
				case ARRAY_INIT:
				{
					arrayInitializer(_t);
					_t = _retTree;
					break;
				}
				case 3:
				{
					break;
				}
				default:
				{
					throw new NoViableAltException(_t);
				}
				}
				}
				break;
			}
			case LPAREN:
			{
				JavaAST tmp289_AST_in = (JavaAST)_t;
				match(_t,LPAREN);
				_t = _t.getNextSibling();
				tmp289_AST_in.print(out);
				elist(_t);
				_t = _retTree;
				JavaAST tmp290_AST_in = (JavaAST)_t;
				match(_t,RPAREN);
				_t = _t.getNextSibling();
				tmp290_AST_in.print(out);
				{
				if (_t==null) _t=ASTNULL;
				switch ( _t.getType()) {
				case LITERAL_class:
				{
					AST __t377 = _t;
					JavaAST tmp291_AST_in = (JavaAST)_t;
					match(_t,LITERAL_class);
					_t = _t.getFirstChild();
					objBlock(_t);
					_t = _retTree;
					_t = __t377;
					_t = _t.getNextSibling();
					break;
				}
				case 3:
				{
					break;
				}
				default:
				{
					throw new NoViableAltException(_t);
				}
				}
				}
				break;
			}
			default:
			{
				throw new NoViableAltException(_t);
			}
			}
			}
			_t = __t373;
			_t = _t.getNextSibling();
		}
		catch (RecognitionException ex) {
			reportError(ex);
			if (_t!=null) {_t = _t.getNextSibling();}
		}
		_retTree = _t;
	}
	
	public final void constant(AST _t) throws RecognitionException {
		
		JavaAST constant_AST_in = (_t == ASTNULL) ? null : (JavaAST)_t;
		
		try {      // for error handling
			if (_t==null) _t=ASTNULL;
			switch ( _t.getType()) {
			case NUM_INT:
			{
				JavaAST tmp292_AST_in = (JavaAST)_t;
				match(_t,NUM_INT);
				_t = _t.getNextSibling();
				tmp292_AST_in.print(out);
				break;
			}
			case CHAR_LITERAL:
			{
				JavaAST tmp293_AST_in = (JavaAST)_t;
				match(_t,CHAR_LITERAL);
				_t = _t.getNextSibling();
				tmp293_AST_in.print(out);
				break;
			}
			case STRING_LITERAL:
			{
				JavaAST tmp294_AST_in = (JavaAST)_t;
				match(_t,STRING_LITERAL);
				_t = _t.getNextSibling();
				tmp294_AST_in.print(out);
				break;
			}
			case NUM_FLOAT:
			{
				JavaAST tmp295_AST_in = (JavaAST)_t;
				match(_t,NUM_FLOAT);
				_t = _t.getNextSibling();
				tmp295_AST_in.print(out);
				break;
			}
			default:
			{
				throw new NoViableAltException(_t);
			}
			}
		}
		catch (RecognitionException ex) {
			reportError(ex);
			if (_t!=null) {_t = _t.getNextSibling();}
		}
		_retTree = _t;
	}
	
	public final void arrayIndexType(AST _t) throws RecognitionException {
		
		JavaAST arrayIndexType_AST_in = (_t == ASTNULL) ? null : (JavaAST)_t;
		
		try {      // for error handling
			AST __t369 = _t;
			JavaAST tmp296_AST_in = (JavaAST)_t;
			match(_t,INDEX_OP);
			_t = _t.getFirstChild();
			primaryExpressionType(_t);
			_t = _retTree;
			expressionType(_t);
			_t = _retTree;
			JavaAST tmp297_AST_in = (JavaAST)_t;
			match(_t,RBRACK);
			_t = _t.getNextSibling();
			_t = __t369;
			_t = _t.getNextSibling();
			arrayIndex(arrayIndexType_AST_in); printType(arrayIndexType_AST_in);
		}
		catch (RecognitionException ex) {
			reportError(ex);
			if (_t!=null) {_t = _t.getNextSibling();}
		}
		_retTree = _t;
	}
	
	public final void newExpressionType(AST _t) throws RecognitionException {
		
		JavaAST newExpressionType_AST_in = (_t == ASTNULL) ? null : (JavaAST)_t;
		JavaAST c = null;
		
		try {      // for error handling
			AST __t379 = _t;
			JavaAST tmp298_AST_in = (JavaAST)_t;
			match(_t,LITERAL_new);
			_t = _t.getFirstChild();
			typeType(_t);
			_t = _retTree;
			{
			if (_t==null) _t=ASTNULL;
			switch ( _t.getType()) {
			case ARRAY_DECLARATOR:
			{
				newArrayDeclaratorType(_t);
				_t = _retTree;
				{
				if (_t==null) _t=ASTNULL;
				switch ( _t.getType()) {
				case ARRAY_INIT:
				{
					arrayInitializerType(_t);
					_t = _retTree;
					break;
				}
				case 3:
				{
					break;
				}
				default:
				{
					throw new NoViableAltException(_t);
				}
				}
				}
				break;
			}
			case LPAREN:
			{
				JavaAST tmp299_AST_in = (JavaAST)_t;
				match(_t,LPAREN);
				_t = _t.getNextSibling();
				elistType(_t);
				_t = _retTree;
				JavaAST tmp300_AST_in = (JavaAST)_t;
				match(_t,RPAREN);
				_t = _t.getNextSibling();
				{
				if (_t==null) _t=ASTNULL;
				switch ( _t.getType()) {
				case LITERAL_class:
				{
					AST __t383 = _t;
					c = _t==ASTNULL ? null :(JavaAST)_t;
					match(_t,LITERAL_class);
					_t = _t.getFirstChild();
					objBlockExcept(_t,true);
					_t = _retTree;
					_t = __t383;
					_t = _t.getNextSibling();
					break;
				}
				case 3:
				{
					break;
				}
				default:
				{
					throw new NoViableAltException(_t);
				}
				}
				}
				break;
			}
			default:
			{
				throw new NoViableAltException(_t);
			}
			}
			}
			_t = __t379;
			_t = _t.getNextSibling();
			newExpression(newExpressionType_AST_in); printType(newExpressionType_AST_in);
		}
		catch (RecognitionException ex) {
			reportError(ex);
			if (_t!=null) {_t = _t.getNextSibling();}
		}
		_retTree = _t;
	}
	
	public final void constantType(AST _t) throws RecognitionException {
		
		JavaAST constantType_AST_in = (_t == ASTNULL) ? null : (JavaAST)_t;
		
		try {      // for error handling
			constant(_t);
			_t = _retTree;
			printType(constantType_AST_in);
		}
		catch (RecognitionException ex) {
			reportError(ex);
			if (_t!=null) {_t = _t.getNextSibling();}
		}
		_retTree = _t;
	}
	
	public final void newArrayDeclarator(AST _t) throws RecognitionException {
		
		JavaAST newArrayDeclarator_AST_in = (_t == ASTNULL) ? null : (JavaAST)_t;
		
		try {      // for error handling
			AST __t385 = _t;
			JavaAST tmp301_AST_in = (JavaAST)_t;
			match(_t,ARRAY_DECLARATOR);
			_t = _t.getFirstChild();
			{
			if (_t==null) _t=ASTNULL;
			switch ( _t.getType()) {
			case ARRAY_DECLARATOR:
			{
				newArrayDeclarator(_t);
				_t = _retTree;
				break;
			}
			case TYPE:
			case CONCAT_ASSIGN:
			case CONCATENATION:
			case UNARY_MINUS:
			case UNARY_PLUS:
			case TYPECAST:
			case INDEX_OP:
			case METHOD_CALL:
			case CONSTRUCTOR_CALL:
			case POST_INC:
			case POST_DEC:
			case PAREN_EXPR:
			case IDENT:
			case DOT:
			case STAR:
			case RBRACK:
			case ASSIGN:
			case PLUS_ASSIGN:
			case MINUS_ASSIGN:
			case STAR_ASSIGN:
			case DIV_ASSIGN:
			case MOD_ASSIGN:
			case SR_ASSIGN:
			case BSR_ASSIGN:
			case SL_ASSIGN:
			case BAND_ASSIGN:
			case BXOR_ASSIGN:
			case BOR_ASSIGN:
			case QUESTION:
			case LOR:
			case LAND:
			case BOR:
			case BXOR:
			case BAND:
			case NOT_EQUAL:
			case EQUAL:
			case LT:
			case GT:
			case LE:
			case GE:
			case LITERAL_instanceof:
			case SL:
			case SR:
			case BSR:
			case PLUS:
			case MINUS:
			case DIV:
			case MOD:
			case INC:
			case DEC:
			case BNOT:
			case LNOT:
			case LITERAL_this:
			case LITERAL_super:
			case LITERAL_true:
			case LITERAL_false:
			case LITERAL_null:
			case LITERAL_new:
			case NUM_INT:
			case CHAR_LITERAL:
			case STRING_LITERAL:
			case NUM_FLOAT:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(_t);
			}
			}
			}
			tmp301_AST_in.print(out);
			{
			if (_t==null) _t=ASTNULL;
			switch ( _t.getType()) {
			case TYPE:
			case CONCAT_ASSIGN:
			case CONCATENATION:
			case UNARY_MINUS:
			case UNARY_PLUS:
			case TYPECAST:
			case INDEX_OP:
			case METHOD_CALL:
			case CONSTRUCTOR_CALL:
			case POST_INC:
			case POST_DEC:
			case PAREN_EXPR:
			case IDENT:
			case DOT:
			case STAR:
			case ASSIGN:
			case PLUS_ASSIGN:
			case MINUS_ASSIGN:
			case STAR_ASSIGN:
			case DIV_ASSIGN:
			case MOD_ASSIGN:
			case SR_ASSIGN:
			case BSR_ASSIGN:
			case SL_ASSIGN:
			case BAND_ASSIGN:
			case BXOR_ASSIGN:
			case BOR_ASSIGN:
			case QUESTION:
			case LOR:
			case LAND:
			case BOR:
			case BXOR:
			case BAND:
			case NOT_EQUAL:
			case EQUAL:
			case LT:
			case GT:
			case LE:
			case GE:
			case LITERAL_instanceof:
			case SL:
			case SR:
			case BSR:
			case PLUS:
			case MINUS:
			case DIV:
			case MOD:
			case INC:
			case DEC:
			case BNOT:
			case LNOT:
			case LITERAL_this:
			case LITERAL_super:
			case LITERAL_true:
			case LITERAL_false:
			case LITERAL_null:
			case LITERAL_new:
			case NUM_INT:
			case CHAR_LITERAL:
			case STRING_LITERAL:
			case NUM_FLOAT:
			{
				expression(_t);
				_t = _retTree;
				break;
			}
			case RBRACK:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(_t);
			}
			}
			}
			JavaAST tmp302_AST_in = (JavaAST)_t;
			match(_t,RBRACK);
			_t = _t.getNextSibling();
			tmp302_AST_in.print(out);
			_t = __t385;
			_t = _t.getNextSibling();
		}
		catch (RecognitionException ex) {
			reportError(ex);
			if (_t!=null) {_t = _t.getNextSibling();}
		}
		_retTree = _t;
	}
	
	public final void newArrayDeclaratorType(AST _t) throws RecognitionException {
		
		JavaAST newArrayDeclaratorType_AST_in = (_t == ASTNULL) ? null : (JavaAST)_t;
		
		try {      // for error handling
			AST __t389 = _t;
			JavaAST tmp303_AST_in = (JavaAST)_t;
			match(_t,ARRAY_DECLARATOR);
			_t = _t.getFirstChild();
			{
			if (_t==null) _t=ASTNULL;
			switch ( _t.getType()) {
			case ARRAY_DECLARATOR:
			{
				newArrayDeclaratorType(_t);
				_t = _retTree;
				break;
			}
			case TYPE:
			case CONCAT_ASSIGN:
			case CONCATENATION:
			case UNARY_MINUS:
			case UNARY_PLUS:
			case TYPECAST:
			case INDEX_OP:
			case METHOD_CALL:
			case CONSTRUCTOR_CALL:
			case POST_INC:
			case POST_DEC:
			case PAREN_EXPR:
			case IDENT:
			case DOT:
			case STAR:
			case RBRACK:
			case ASSIGN:
			case PLUS_ASSIGN:
			case MINUS_ASSIGN:
			case STAR_ASSIGN:
			case DIV_ASSIGN:
			case MOD_ASSIGN:
			case SR_ASSIGN:
			case BSR_ASSIGN:
			case SL_ASSIGN:
			case BAND_ASSIGN:
			case BXOR_ASSIGN:
			case BOR_ASSIGN:
			case QUESTION:
			case LOR:
			case LAND:
			case BOR:
			case BXOR:
			case BAND:
			case NOT_EQUAL:
			case EQUAL:
			case LT:
			case GT:
			case LE:
			case GE:
			case LITERAL_instanceof:
			case SL:
			case SR:
			case BSR:
			case PLUS:
			case MINUS:
			case DIV:
			case MOD:
			case INC:
			case DEC:
			case BNOT:
			case LNOT:
			case LITERAL_this:
			case LITERAL_super:
			case LITERAL_true:
			case LITERAL_false:
			case LITERAL_null:
			case LITERAL_new:
			case NUM_INT:
			case CHAR_LITERAL:
			case STRING_LITERAL:
			case NUM_FLOAT:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(_t);
			}
			}
			}
			{
			if (_t==null) _t=ASTNULL;
			switch ( _t.getType()) {
			case TYPE:
			case CONCAT_ASSIGN:
			case CONCATENATION:
			case UNARY_MINUS:
			case UNARY_PLUS:
			case TYPECAST:
			case INDEX_OP:
			case METHOD_CALL:
			case CONSTRUCTOR_CALL:
			case POST_INC:
			case POST_DEC:
			case PAREN_EXPR:
			case IDENT:
			case DOT:
			case STAR:
			case ASSIGN:
			case PLUS_ASSIGN:
			case MINUS_ASSIGN:
			case STAR_ASSIGN:
			case DIV_ASSIGN:
			case MOD_ASSIGN:
			case SR_ASSIGN:
			case BSR_ASSIGN:
			case SL_ASSIGN:
			case BAND_ASSIGN:
			case BXOR_ASSIGN:
			case BOR_ASSIGN:
			case QUESTION:
			case LOR:
			case LAND:
			case BOR:
			case BXOR:
			case BAND:
			case NOT_EQUAL:
			case EQUAL:
			case LT:
			case GT:
			case LE:
			case GE:
			case LITERAL_instanceof:
			case SL:
			case SR:
			case BSR:
			case PLUS:
			case MINUS:
			case DIV:
			case MOD:
			case INC:
			case DEC:
			case BNOT:
			case LNOT:
			case LITERAL_this:
			case LITERAL_super:
			case LITERAL_true:
			case LITERAL_false:
			case LITERAL_null:
			case LITERAL_new:
			case NUM_INT:
			case CHAR_LITERAL:
			case STRING_LITERAL:
			case NUM_FLOAT:
			{
				expressionType(_t);
				_t = _retTree;
				break;
			}
			case RBRACK:
			{
				break;
			}
			default:
			{
				throw new NoViableAltException(_t);
			}
			}
			}
			JavaAST tmp304_AST_in = (JavaAST)_t;
			match(_t,RBRACK);
			_t = _t.getNextSibling();
			_t = __t389;
			_t = _t.getNextSibling();
		}
		catch (RecognitionException ex) {
			reportError(ex);
			if (_t!=null) {_t = _t.getNextSibling();}
		}
		_retTree = _t;
	}
	
	
	public static final String[] _tokenNames = {
		"<0>",
		"EOF",
		"<2>",
		"NULL_TREE_LOOKAHEAD",
		"FILE",
		"VARIABLE_DEFS",
		"MODIFIERS",
		"ARRAY_DECLARATOR",
		"TYPE",
		"EXTENDS_CLAUSE",
		"OBJBLOCK",
		"IMPLEMENTS_CLAUSE",
		"CTOR_DEF",
		"METHOD_DEF",
		"INSTANCE_INIT",
		"VARIABLE_DEF",
		"ARRAY_INIT",
		"PARAMETERS",
		"PARAMETER_DEF",
		"SLIST",
		"TYPE_STAT",
		"EXPRESSION_STAT",
		"LABELED_STAT",
		"EMPTY_STAT",
		"CASE_GROUP",
		"FOR_INIT",
		"FOR_CONDITION",
		"FOR_ITERATOR",
		"ELIST",
		"CONCAT_ASSIGN",
		"CONCATENATION",
		"UNARY_MINUS",
		"UNARY_PLUS",
		"TYPECAST",
		"INDEX_OP",
		"METHOD_CALL",
		"CONSTRUCTOR_CALL",
		"POST_INC",
		"POST_DEC",
		"PAREN_EXPR",
		"\"package\"",
		"SEMI",
		"\"import\"",
		"IDENT",
		"DOT",
		"STAR",
		"\"public\"",
		"\"private\"",
		"\"protected\"",
		"\"static\"",
		"\"final\"",
		"\"synchronized\"",
		"\"volatile\"",
		"\"transient\"",
		"\"native\"",
		"\"abstract\"",
		"\"strictfp\"",
		"\"class\"",
		"\"extends\"",
		"\"implements\"",
		"COMMA",
		"\"interface\"",
		"LCURLY",
		"RCURLY",
		"LPAREN",
		"RPAREN",
		"\"throws\"",
		"LBRACK",
		"RBRACK",
		"\"void\"",
		"\"boolean\"",
		"\"byte\"",
		"\"char\"",
		"\"short\"",
		"\"int\"",
		"\"float\"",
		"\"long\"",
		"\"double\"",
		"ASSIGN",
		"COLON",
		"\"if\"",
		"\"else\"",
		"\"for\"",
		"\"while\"",
		"\"do\"",
		"\"break\"",
		"\"continue\"",
		"\"return\"",
		"\"switch\"",
		"\"throw\"",
		"\"assert\"",
		"\"case\"",
		"\"default\"",
		"\"try\"",
		"\"finally\"",
		"\"catch\"",
		"PLUS_ASSIGN",
		"MINUS_ASSIGN",
		"STAR_ASSIGN",
		"DIV_ASSIGN",
		"MOD_ASSIGN",
		"SR_ASSIGN",
		"BSR_ASSIGN",
		"SL_ASSIGN",
		"BAND_ASSIGN",
		"BXOR_ASSIGN",
		"BOR_ASSIGN",
		"QUESTION",
		"LOR",
		"LAND",
		"BOR",
		"BXOR",
		"BAND",
		"NOT_EQUAL",
		"EQUAL",
		"LT",
		"GT",
		"LE",
		"GE",
		"\"instanceof\"",
		"SL",
		"SR",
		"BSR",
		"PLUS",
		"MINUS",
		"DIV",
		"MOD",
		"INC",
		"DEC",
		"BNOT",
		"LNOT",
		"\"this\"",
		"\"super\"",
		"\"true\"",
		"\"false\"",
		"\"null\"",
		"\"new\"",
		"NUM_INT",
		"CHAR_LITERAL",
		"STRING_LITERAL",
		"NUM_FLOAT",
		"\"const\"",
		"\"goto\"",
		"WS",
		"SL_COMMENT",
		"ML_COMMENT",
		"ESC",
		"HEX_DIGIT",
		"EXPONENT",
		"FLOAT_SUFFIX"
	};
	
	private static final long[] mk_tokenSet_0() {
		long[] data = { 2251799829938208L, 670892032L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_0 = new BitSet(mk_tokenSet_0());
	private static final long[] mk_tokenSet_1() {
		long[] data = { 2251799829938208L, 603783168L, 0L, 0L};
		return data;
	}
	public static final BitSet _tokenSet_1 = new BitSet(mk_tokenSet_1());
	}
	
