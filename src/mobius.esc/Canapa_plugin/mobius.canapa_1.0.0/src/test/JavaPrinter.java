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
public class JavaPrinter extends antlr.TreeParser       implements JavaPrinterTokenTypes
 {

	/**
	 * Where to send the output of the tree walker
	 */
	protected OutputStreamWriter out;
public JavaPrinter() {
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
			tmp1_AST_in.print(output);
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
					typeDefinition(_t);
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
		JavaAST p = null;
		
		try {      // for error handling
			AST __t9 = _t;
			p = _t==ASTNULL ? null :(JavaAST)_t;
			match(_t,LITERAL_package);
			_t = _t.getFirstChild();
			p.print(out);
			identifier(_t);
			_t = _retTree;
			JavaAST tmp2_AST_in = (JavaAST)_t;
			match(_t,SEMI);
			_t = _t.getNextSibling();
			tmp2_AST_in.print(out);
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
		JavaAST i = null;
		
		try {      // for error handling
			AST __t11 = _t;
			i = _t==ASTNULL ? null :(JavaAST)_t;
			match(_t,LITERAL_import);
			_t = _t.getFirstChild();
			i.print(out);
			identifierStar(_t);
			_t = _retTree;
			JavaAST tmp3_AST_in = (JavaAST)_t;
			match(_t,SEMI);
			_t = _t.getNextSibling();
			tmp3_AST_in.print(out);
			_t = __t11;
			_t = _t.getNextSibling();
		}
		catch (RecognitionException ex) {
			reportError(ex);
			if (_t!=null) {_t = _t.getNextSibling();}
		}
		_retTree = _t;
	}
	
	public final void typeDefinition(AST _t) throws RecognitionException {
		
		JavaAST typeDefinition_AST_in = (_t == ASTNULL) ? null : (JavaAST)_t;
		JavaAST cl = null;
		JavaAST id1 = null;
		JavaAST in = null;
		JavaAST id2 = null;
		
		try {      // for error handling
			if (_t==null) _t=ASTNULL;
			switch ( _t.getType()) {
			case LITERAL_class:
			{
				AST __t13 = _t;
				cl = _t==ASTNULL ? null :(JavaAST)_t;
				match(_t,LITERAL_class);
				_t = _t.getFirstChild();
				modifiers(_t);
				_t = _retTree;
				id1 = (JavaAST)_t;
				match(_t,IDENT);
				_t = _t.getNextSibling();
				cl.print(out); id1.print(out);
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
				in = _t==ASTNULL ? null :(JavaAST)_t;
				match(_t,LITERAL_interface);
				_t = _t.getFirstChild();
				modifiers(_t);
				_t = _retTree;
				id2 = (JavaAST)_t;
				match(_t,IDENT);
				_t = _t.getNextSibling();
				in.print(out); id2.print(out);
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
				interfaceBlock(_t);
				_t = _retTree;
				_t = __t16;
				_t = _t.getNextSibling();
				break;
			}
			case SEMI:
			{
				JavaAST tmp4_AST_in = (JavaAST)_t;
				match(_t,SEMI);
				_t = _t.getNextSibling();
				tmp4_AST_in.print(out);
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
	
	public final void identifier(AST _t) throws RecognitionException {
		
		JavaAST identifier_AST_in = (_t == ASTNULL) ? null : (JavaAST)_t;
		
		try {      // for error handling
			if (_t==null) _t=ASTNULL;
			switch ( _t.getType()) {
			case IDENT:
			{
				JavaAST tmp5_AST_in = (JavaAST)_t;
				match(_t,IDENT);
				_t = _t.getNextSibling();
				tmp5_AST_in.print(out);
				break;
			}
			case DOT:
			{
				AST __t90 = _t;
				JavaAST tmp6_AST_in = (JavaAST)_t;
				match(_t,DOT);
				_t = _t.getFirstChild();
				identifier(_t);
				_t = _retTree;
				JavaAST tmp7_AST_in = (JavaAST)_t;
				match(_t,IDENT);
				_t = _t.getNextSibling();
				tmp6_AST_in.print(out); tmp7_AST_in.print(out);
				_t = __t90;
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
				JavaAST tmp8_AST_in = (JavaAST)_t;
				match(_t,IDENT);
				_t = _t.getNextSibling();
				tmp8_AST_in.print(out);
				break;
			}
			case DOT:
			{
				AST __t92 = _t;
				JavaAST tmp9_AST_in = (JavaAST)_t;
				match(_t,DOT);
				_t = _t.getFirstChild();
				identifier(_t);
				_t = _retTree;
				tmp9_AST_in.print(out);
				{
				if (_t==null) _t=ASTNULL;
				switch ( _t.getType()) {
				case STAR:
				{
					JavaAST tmp10_AST_in = (JavaAST)_t;
					match(_t,STAR);
					_t = _t.getNextSibling();
					tmp10_AST_in.print(out);
					break;
				}
				case IDENT:
				{
					JavaAST tmp11_AST_in = (JavaAST)_t;
					match(_t,IDENT);
					_t = _t.getNextSibling();
					tmp11_AST_in.print(out);
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
	
	public final void modifiers(AST _t) throws RecognitionException {
		
		JavaAST modifiers_AST_in = (_t == ASTNULL) ? null : (JavaAST)_t;
		
		try {      // for error handling
			AST __t26 = _t;
			JavaAST tmp12_AST_in = (JavaAST)_t;
			match(_t,MODIFIERS);
			_t = _t.getFirstChild();
			{
			_loop28:
			do {
				if (_t==null) _t=ASTNULL;
				if (((_t.getType() >= LITERAL_public && _t.getType() <= LITERAL_strictfp))) {
					modifier(_t);
					_t = _retTree;
				}
				else {
					break _loop28;
				}
				
			} while (true);
			}
			_t = __t26;
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
		JavaAST e = null;
		
		try {      // for error handling
			AST __t31 = _t;
			e = _t==ASTNULL ? null :(JavaAST)_t;
			match(_t,LITERAL_extends);
			_t = _t.getFirstChild();
			e.print(out);
			identifier(_t);
			_t = _retTree;
			{
			_loop33:
			do {
				if (_t==null) _t=ASTNULL;
				if ((_t.getType()==COMMA)) {
					JavaAST tmp13_AST_in = (JavaAST)_t;
					match(_t,COMMA);
					_t = _t.getNextSibling();
					tmp13_AST_in.print(out);
					identifier(_t);
					_t = _retTree;
				}
				else {
					break _loop33;
				}
				
			} while (true);
			}
			_t = __t31;
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
		JavaAST i = null;
		
		try {      // for error handling
			AST __t35 = _t;
			i = _t==ASTNULL ? null :(JavaAST)_t;
			match(_t,LITERAL_implements);
			_t = _t.getFirstChild();
			i.print(out);
			identifier(_t);
			_t = _retTree;
			{
			_loop37:
			do {
				if (_t==null) _t=ASTNULL;
				if ((_t.getType()==COMMA)) {
					JavaAST tmp14_AST_in = (JavaAST)_t;
					match(_t,COMMA);
					_t = _t.getNextSibling();
					tmp14_AST_in.print(out);
					identifier(_t);
					_t = _retTree;
				}
				else {
					break _loop37;
				}
				
			} while (true);
			}
			_t = __t35;
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
			AST __t43 = _t;
			JavaAST tmp15_AST_in = (JavaAST)_t;
			match(_t,OBJBLOCK);
			_t = _t.getFirstChild();
			tmp15_AST_in.print(out);
			{
			_loop47:
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
					AST __t45 = _t;
					s = _t==ASTNULL ? null :(JavaAST)_t;
					match(_t,LITERAL_static);
					_t = _t.getFirstChild();
					s.print(out);
					slist(_t);
					_t = _retTree;
					_t = __t45;
					_t = _t.getNextSibling();
					break;
				}
				case INSTANCE_INIT:
				{
					AST __t46 = _t;
					JavaAST tmp16_AST_in = (JavaAST)_t;
					match(_t,INSTANCE_INIT);
					_t = _t.getFirstChild();
					slist(_t);
					_t = _retTree;
					_t = __t46;
					_t = _t.getNextSibling();
					break;
				}
				default:
				{
					break _loop47;
				}
				}
			} while (true);
			}
			JavaAST tmp17_AST_in = (JavaAST)_t;
			match(_t,RCURLY);
			_t = _t.getNextSibling();
			tmp17_AST_in.print(out);
			_t = __t43;
			_t = _t.getNextSibling();
		}
		catch (RecognitionException ex) {
			reportError(ex);
			if (_t!=null) {_t = _t.getNextSibling();}
		}
		_retTree = _t;
	}
	
	public final void interfaceBlock(AST _t) throws RecognitionException {
		
		JavaAST interfaceBlock_AST_in = (_t == ASTNULL) ? null : (JavaAST)_t;
		
		try {      // for error handling
			AST __t39 = _t;
			JavaAST tmp18_AST_in = (JavaAST)_t;
			match(_t,OBJBLOCK);
			_t = _t.getFirstChild();
			tmp18_AST_in.print(out);
			{
			_loop41:
			do {
				if (_t==null) _t=ASTNULL;
				switch ( _t.getType()) {
				case METHOD_DEF:
				{
					methodDecl(_t);
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
					break _loop41;
				}
				}
			} while (true);
			}
			JavaAST tmp19_AST_in = (JavaAST)_t;
			match(_t,RCURLY);
			_t = _t.getNextSibling();
			tmp19_AST_in.print(out);
			_t = __t39;
			_t = _t.getNextSibling();
		}
		catch (RecognitionException ex) {
			reportError(ex);
			if (_t!=null) {_t = _t.getNextSibling();}
		}
		_retTree = _t;
	}
	
	public final void typeSpec(AST _t) throws RecognitionException {
		
		JavaAST typeSpec_AST_in = (_t == ASTNULL) ? null : (JavaAST)_t;
		
		try {      // for error handling
			AST __t19 = _t;
			JavaAST tmp20_AST_in = (JavaAST)_t;
			match(_t,TYPE);
			_t = _t.getFirstChild();
			typeSpecArray(_t);
			_t = _retTree;
			_t = __t19;
			_t = _t.getNextSibling();
		}
		catch (RecognitionException ex) {
			reportError(ex);
			if (_t!=null) {_t = _t.getNextSibling();}
		}
		_retTree = _t;
	}
	
	public final void typeSpecArray(AST _t) throws RecognitionException {
		
		JavaAST typeSpecArray_AST_in = (_t == ASTNULL) ? null : (JavaAST)_t;
		
		try {      // for error handling
			if (_t==null) _t=ASTNULL;
			switch ( _t.getType()) {
			case ARRAY_DECLARATOR:
			{
				AST __t21 = _t;
				JavaAST tmp21_AST_in = (JavaAST)_t;
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
					typeSpecArray(_t);
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
				JavaAST tmp22_AST_in = (JavaAST)_t;
				match(_t,RBRACK);
				_t = _t.getNextSibling();
				tmp21_AST_in.print(out); tmp22_AST_in.print(out);
				_t = __t21;
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
				type(_t);
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
	
	public final void type(AST _t) throws RecognitionException {
		
		JavaAST type_AST_in = (_t == ASTNULL) ? null : (JavaAST)_t;
		
		try {      // for error handling
			if (_t==null) _t=ASTNULL;
			switch ( _t.getType()) {
			case IDENT:
			case DOT:
			{
				identifier(_t);
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
				builtInType(_t);
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
	
	public final void builtInType(AST _t) throws RecognitionException {
		
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
				v.print(out);
				break;
			}
			case LITERAL_boolean:
			{
				b = (JavaAST)_t;
				match(_t,LITERAL_boolean);
				_t = _t.getNextSibling();
				b.print(out);
				break;
			}
			case LITERAL_byte:
			{
				y = (JavaAST)_t;
				match(_t,LITERAL_byte);
				_t = _t.getNextSibling();
				y.print(out);
				break;
			}
			case LITERAL_char:
			{
				c = (JavaAST)_t;
				match(_t,LITERAL_char);
				_t = _t.getNextSibling();
				c.print(out);
				break;
			}
			case LITERAL_short:
			{
				s = (JavaAST)_t;
				match(_t,LITERAL_short);
				_t = _t.getNextSibling();
				s.print(out);
				break;
			}
			case LITERAL_int:
			{
				i = (JavaAST)_t;
				match(_t,LITERAL_int);
				_t = _t.getNextSibling();
				i.print(out);
				break;
			}
			case LITERAL_float:
			{
				f = (JavaAST)_t;
				match(_t,LITERAL_float);
				_t = _t.getNextSibling();
				f.print(out);
				break;
			}
			case LITERAL_long:
			{
				l = (JavaAST)_t;
				match(_t,LITERAL_long);
				_t = _t.getNextSibling();
				l.print(out);
				break;
			}
			case LITERAL_double:
			{
				d = (JavaAST)_t;
				match(_t,LITERAL_double);
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
		catch (RecognitionException ex) {
			reportError(ex);
			if (_t!=null) {_t = _t.getNextSibling();}
		}
		_retTree = _t;
	}
	
	public final void modifier(AST _t) throws RecognitionException {
		
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
				u.print(out);
				break;
			}
			case LITERAL_private:
			{
				p = (JavaAST)_t;
				match(_t,LITERAL_private);
				_t = _t.getNextSibling();
				p.print(out);
				break;
			}
			case LITERAL_protected:
			{
				r = (JavaAST)_t;
				match(_t,LITERAL_protected);
				_t = _t.getNextSibling();
				r.print(out);
				break;
			}
			case LITERAL_static:
			{
				s = (JavaAST)_t;
				match(_t,LITERAL_static);
				_t = _t.getNextSibling();
				s.print(out);
				break;
			}
			case LITERAL_final:
			{
				f = (JavaAST)_t;
				match(_t,LITERAL_final);
				_t = _t.getNextSibling();
				f.print(out);
				break;
			}
			case LITERAL_synchronized:
			{
				y = (JavaAST)_t;
				match(_t,LITERAL_synchronized);
				_t = _t.getNextSibling();
				y.print(out);
				break;
			}
			case LITERAL_volatile:
			{
				v = (JavaAST)_t;
				match(_t,LITERAL_volatile);
				_t = _t.getNextSibling();
				v.print(out);
				break;
			}
			case LITERAL_transient:
			{
				t = (JavaAST)_t;
				match(_t,LITERAL_transient);
				_t = _t.getNextSibling();
				t.print(out);
				break;
			}
			case LITERAL_native:
			{
				n = (JavaAST)_t;
				match(_t,LITERAL_native);
				_t = _t.getNextSibling();
				n.print(out);
				break;
			}
			case LITERAL_abstract:
			{
				a = (JavaAST)_t;
				match(_t,LITERAL_abstract);
				_t = _t.getNextSibling();
				a.print(out);
				break;
			}
			case LITERAL_strictfp:
			{
				i = (JavaAST)_t;
				match(_t,LITERAL_strictfp);
				_t = _t.getNextSibling();
				i.print(out);
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
	
	public final void methodDecl(AST _t) throws RecognitionException {
		
		JavaAST methodDecl_AST_in = (_t == ASTNULL) ? null : (JavaAST)_t;
		
		try {      // for error handling
			AST __t51 = _t;
			JavaAST tmp23_AST_in = (JavaAST)_t;
			match(_t,METHOD_DEF);
			_t = _t.getFirstChild();
			modifiers(_t);
			_t = _retTree;
			typeSpec(_t);
			_t = _retTree;
			methodHead(_t);
			_t = _retTree;
			JavaAST tmp24_AST_in = (JavaAST)_t;
			match(_t,SEMI);
			_t = _t.getNextSibling();
			tmp24_AST_in.print(out);
			_t = __t51;
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
			AST __t56 = _t;
			JavaAST tmp25_AST_in = (JavaAST)_t;
			match(_t,VARIABLE_DEFS);
			_t = _t.getFirstChild();
			modifiers(_t);
			_t = _retTree;
			typeSpec(_t);
			_t = _retTree;
			variableDef(_t);
			_t = _retTree;
			{
			_loop58:
			do {
				if (_t==null) _t=ASTNULL;
				if ((_t.getType()==COMMA)) {
					JavaAST tmp26_AST_in = (JavaAST)_t;
					match(_t,COMMA);
					_t = _t.getNextSibling();
					tmp26_AST_in.print(out);
					variableDef(_t);
					_t = _retTree;
				}
				else {
					break _loop58;
				}
				
			} while (true);
			}
			JavaAST tmp27_AST_in = (JavaAST)_t;
			match(_t,SEMI);
			_t = _t.getNextSibling();
			tmp27_AST_in.print(out);
			_t = __t56;
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
			AST __t49 = _t;
			JavaAST tmp28_AST_in = (JavaAST)_t;
			match(_t,CTOR_DEF);
			_t = _t.getFirstChild();
			modifiers(_t);
			_t = _retTree;
			methodHead(_t);
			_t = _retTree;
			slist(_t);
			_t = _retTree;
			_t = __t49;
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
			AST __t53 = _t;
			JavaAST tmp29_AST_in = (JavaAST)_t;
			match(_t,METHOD_DEF);
			_t = _t.getFirstChild();
			modifiers(_t);
			_t = _retTree;
			typeSpec(_t);
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
				JavaAST tmp30_AST_in = (JavaAST)_t;
				match(_t,SEMI);
				_t = _t.getNextSibling();
				tmp30_AST_in.print(out);
				break;
			}
			default:
			{
				throw new NoViableAltException(_t);
			}
			}
			}
			_t = __t53;
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
			AST __t95 = _t;
			JavaAST tmp31_AST_in = (JavaAST)_t;
			match(_t,SLIST);
			_t = _t.getFirstChild();
			tmp31_AST_in.print(out);
			{
			_loop97:
			do {
				if (_t==null) _t=ASTNULL;
				if ((_tokenSet_0.member(_t.getType()))) {
					stat(_t);
					_t = _retTree;
				}
				else {
					break _loop97;
				}
				
			} while (true);
			}
			JavaAST tmp32_AST_in = (JavaAST)_t;
			match(_t,RCURLY);
			_t = _t.getNextSibling();
			tmp32_AST_in.print(out);
			_t = __t95;
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
			JavaAST tmp33_AST_in = (JavaAST)_t;
			match(_t,IDENT);
			_t = _t.getNextSibling();
			JavaAST tmp34_AST_in = (JavaAST)_t;
			match(_t,LPAREN);
			_t = _t.getNextSibling();
			tmp33_AST_in.print(out); tmp34_AST_in.print(out);
			AST __t80 = _t;
			JavaAST tmp35_AST_in = (JavaAST)_t;
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
				_loop83:
				do {
					if (_t==null) _t=ASTNULL;
					if ((_t.getType()==COMMA)) {
						JavaAST tmp36_AST_in = (JavaAST)_t;
						match(_t,COMMA);
						_t = _t.getNextSibling();
						tmp36_AST_in.print(out);
						parameterDef(_t);
						_t = _retTree;
					}
					else {
						break _loop83;
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
			_t = __t80;
			_t = _t.getNextSibling();
			JavaAST tmp37_AST_in = (JavaAST)_t;
			match(_t,RPAREN);
			_t = _t.getNextSibling();
			tmp37_AST_in.print(out);
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
			AST __t60 = _t;
			JavaAST tmp38_AST_in = (JavaAST)_t;
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
			_t = __t60;
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
			JavaAST tmp39_AST_in = (JavaAST)_t;
			match(_t,IDENT);
			_t = _t.getNextSibling();
			tmp39_AST_in.print(out);
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
			AST __t67 = _t;
			JavaAST tmp40_AST_in = (JavaAST)_t;
			match(_t,ASSIGN);
			_t = _t.getFirstChild();
			tmp40_AST_in.print(out);
			initializer(_t);
			_t = _retTree;
			_t = __t67;
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
			_loop65:
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
					break _loop65;
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
	
	public final void parameterDef(AST _t) throws RecognitionException {
		
		JavaAST parameterDef_AST_in = (_t == ASTNULL) ? null : (JavaAST)_t;
		
		try {      // for error handling
			AST __t69 = _t;
			JavaAST tmp41_AST_in = (JavaAST)_t;
			match(_t,PARAMETER_DEF);
			_t = _t.getFirstChild();
			modifiers(_t);
			_t = _retTree;
			typeSpec(_t);
			_t = _retTree;
			JavaAST tmp42_AST_in = (JavaAST)_t;
			match(_t,IDENT);
			_t = _t.getNextSibling();
			tmp42_AST_in.print(out);
			declaratorBrackets(_t);
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
	
	public final void expression(AST _t) throws RecognitionException {
		
		JavaAST expression_AST_in = (_t == ASTNULL) ? null : (JavaAST)_t;
		JavaAST i = null;
		
		try {      // for error handling
			if (_t==null) _t=ASTNULL;
			switch ( _t.getType()) {
			case QUESTION:
			{
				AST __t145 = _t;
				JavaAST tmp43_AST_in = (JavaAST)_t;
				match(_t,QUESTION);
				_t = _t.getFirstChild();
				expression(_t);
				_t = _retTree;
				tmp43_AST_in.print(out);
				expression(_t);
				_t = _retTree;
				JavaAST tmp44_AST_in = (JavaAST)_t;
				match(_t,COLON);
				_t = _t.getNextSibling();
				tmp44_AST_in.print(out);
				expression(_t);
				_t = _retTree;
				_t = __t145;
				_t = _t.getNextSibling();
				break;
			}
			case ASSIGN:
			{
				AST __t146 = _t;
				JavaAST tmp45_AST_in = (JavaAST)_t;
				match(_t,ASSIGN);
				_t = _t.getFirstChild();
				expression(_t);
				_t = _retTree;
				tmp45_AST_in.print(out);
				expression(_t);
				_t = _retTree;
				_t = __t146;
				_t = _t.getNextSibling();
				break;
			}
			case PLUS_ASSIGN:
			{
				AST __t147 = _t;
				JavaAST tmp46_AST_in = (JavaAST)_t;
				match(_t,PLUS_ASSIGN);
				_t = _t.getFirstChild();
				expression(_t);
				_t = _retTree;
				tmp46_AST_in.print(out);
				expression(_t);
				_t = _retTree;
				_t = __t147;
				_t = _t.getNextSibling();
				break;
			}
			case CONCAT_ASSIGN:
			{
				AST __t148 = _t;
				JavaAST tmp47_AST_in = (JavaAST)_t;
				match(_t,CONCAT_ASSIGN);
				_t = _t.getFirstChild();
				expression(_t);
				_t = _retTree;
				tmp47_AST_in.print(out);
				expression(_t);
				_t = _retTree;
				_t = __t148;
				_t = _t.getNextSibling();
				break;
			}
			case MINUS_ASSIGN:
			{
				AST __t149 = _t;
				JavaAST tmp48_AST_in = (JavaAST)_t;
				match(_t,MINUS_ASSIGN);
				_t = _t.getFirstChild();
				expression(_t);
				_t = _retTree;
				tmp48_AST_in.print(out);
				expression(_t);
				_t = _retTree;
				_t = __t149;
				_t = _t.getNextSibling();
				break;
			}
			case STAR_ASSIGN:
			{
				AST __t150 = _t;
				JavaAST tmp49_AST_in = (JavaAST)_t;
				match(_t,STAR_ASSIGN);
				_t = _t.getFirstChild();
				expression(_t);
				_t = _retTree;
				tmp49_AST_in.print(out);
				expression(_t);
				_t = _retTree;
				_t = __t150;
				_t = _t.getNextSibling();
				break;
			}
			case DIV_ASSIGN:
			{
				AST __t151 = _t;
				JavaAST tmp50_AST_in = (JavaAST)_t;
				match(_t,DIV_ASSIGN);
				_t = _t.getFirstChild();
				expression(_t);
				_t = _retTree;
				tmp50_AST_in.print(out);
				expression(_t);
				_t = _retTree;
				_t = __t151;
				_t = _t.getNextSibling();
				break;
			}
			case MOD_ASSIGN:
			{
				AST __t152 = _t;
				JavaAST tmp51_AST_in = (JavaAST)_t;
				match(_t,MOD_ASSIGN);
				_t = _t.getFirstChild();
				expression(_t);
				_t = _retTree;
				tmp51_AST_in.print(out);
				expression(_t);
				_t = _retTree;
				_t = __t152;
				_t = _t.getNextSibling();
				break;
			}
			case SR_ASSIGN:
			{
				AST __t153 = _t;
				JavaAST tmp52_AST_in = (JavaAST)_t;
				match(_t,SR_ASSIGN);
				_t = _t.getFirstChild();
				expression(_t);
				_t = _retTree;
				tmp52_AST_in.print(out);
				expression(_t);
				_t = _retTree;
				_t = __t153;
				_t = _t.getNextSibling();
				break;
			}
			case BSR_ASSIGN:
			{
				AST __t154 = _t;
				JavaAST tmp53_AST_in = (JavaAST)_t;
				match(_t,BSR_ASSIGN);
				_t = _t.getFirstChild();
				expression(_t);
				_t = _retTree;
				tmp53_AST_in.print(out);
				expression(_t);
				_t = _retTree;
				_t = __t154;
				_t = _t.getNextSibling();
				break;
			}
			case SL_ASSIGN:
			{
				AST __t155 = _t;
				JavaAST tmp54_AST_in = (JavaAST)_t;
				match(_t,SL_ASSIGN);
				_t = _t.getFirstChild();
				expression(_t);
				_t = _retTree;
				tmp54_AST_in.print(out);
				expression(_t);
				_t = _retTree;
				_t = __t155;
				_t = _t.getNextSibling();
				break;
			}
			case BAND_ASSIGN:
			{
				AST __t156 = _t;
				JavaAST tmp55_AST_in = (JavaAST)_t;
				match(_t,BAND_ASSIGN);
				_t = _t.getFirstChild();
				expression(_t);
				_t = _retTree;
				tmp55_AST_in.print(out);
				expression(_t);
				_t = _retTree;
				_t = __t156;
				_t = _t.getNextSibling();
				break;
			}
			case BXOR_ASSIGN:
			{
				AST __t157 = _t;
				JavaAST tmp56_AST_in = (JavaAST)_t;
				match(_t,BXOR_ASSIGN);
				_t = _t.getFirstChild();
				expression(_t);
				_t = _retTree;
				tmp56_AST_in.print(out);
				expression(_t);
				_t = _retTree;
				_t = __t157;
				_t = _t.getNextSibling();
				break;
			}
			case BOR_ASSIGN:
			{
				AST __t158 = _t;
				JavaAST tmp57_AST_in = (JavaAST)_t;
				match(_t,BOR_ASSIGN);
				_t = _t.getFirstChild();
				expression(_t);
				_t = _retTree;
				tmp57_AST_in.print(out);
				expression(_t);
				_t = _retTree;
				_t = __t158;
				_t = _t.getNextSibling();
				break;
			}
			case LOR:
			{
				AST __t159 = _t;
				JavaAST tmp58_AST_in = (JavaAST)_t;
				match(_t,LOR);
				_t = _t.getFirstChild();
				expression(_t);
				_t = _retTree;
				tmp58_AST_in.print(out);
				expression(_t);
				_t = _retTree;
				_t = __t159;
				_t = _t.getNextSibling();
				break;
			}
			case LAND:
			{
				AST __t160 = _t;
				JavaAST tmp59_AST_in = (JavaAST)_t;
				match(_t,LAND);
				_t = _t.getFirstChild();
				expression(_t);
				_t = _retTree;
				tmp59_AST_in.print(out);
				expression(_t);
				_t = _retTree;
				_t = __t160;
				_t = _t.getNextSibling();
				break;
			}
			case BOR:
			{
				AST __t161 = _t;
				JavaAST tmp60_AST_in = (JavaAST)_t;
				match(_t,BOR);
				_t = _t.getFirstChild();
				expression(_t);
				_t = _retTree;
				tmp60_AST_in.print(out);
				expression(_t);
				_t = _retTree;
				_t = __t161;
				_t = _t.getNextSibling();
				break;
			}
			case BXOR:
			{
				AST __t162 = _t;
				JavaAST tmp61_AST_in = (JavaAST)_t;
				match(_t,BXOR);
				_t = _t.getFirstChild();
				expression(_t);
				_t = _retTree;
				tmp61_AST_in.print(out);
				expression(_t);
				_t = _retTree;
				_t = __t162;
				_t = _t.getNextSibling();
				break;
			}
			case BAND:
			{
				AST __t163 = _t;
				JavaAST tmp62_AST_in = (JavaAST)_t;
				match(_t,BAND);
				_t = _t.getFirstChild();
				expression(_t);
				_t = _retTree;
				tmp62_AST_in.print(out);
				expression(_t);
				_t = _retTree;
				_t = __t163;
				_t = _t.getNextSibling();
				break;
			}
			case NOT_EQUAL:
			{
				AST __t164 = _t;
				JavaAST tmp63_AST_in = (JavaAST)_t;
				match(_t,NOT_EQUAL);
				_t = _t.getFirstChild();
				expression(_t);
				_t = _retTree;
				tmp63_AST_in.print(out);
				expression(_t);
				_t = _retTree;
				_t = __t164;
				_t = _t.getNextSibling();
				break;
			}
			case EQUAL:
			{
				AST __t165 = _t;
				JavaAST tmp64_AST_in = (JavaAST)_t;
				match(_t,EQUAL);
				_t = _t.getFirstChild();
				expression(_t);
				_t = _retTree;
				tmp64_AST_in.print(out);
				expression(_t);
				_t = _retTree;
				_t = __t165;
				_t = _t.getNextSibling();
				break;
			}
			case LT:
			{
				AST __t166 = _t;
				JavaAST tmp65_AST_in = (JavaAST)_t;
				match(_t,LT);
				_t = _t.getFirstChild();
				expression(_t);
				_t = _retTree;
				tmp65_AST_in.print(out);
				expression(_t);
				_t = _retTree;
				_t = __t166;
				_t = _t.getNextSibling();
				break;
			}
			case GT:
			{
				AST __t167 = _t;
				JavaAST tmp66_AST_in = (JavaAST)_t;
				match(_t,GT);
				_t = _t.getFirstChild();
				expression(_t);
				_t = _retTree;
				tmp66_AST_in.print(out);
				expression(_t);
				_t = _retTree;
				_t = __t167;
				_t = _t.getNextSibling();
				break;
			}
			case LE:
			{
				AST __t168 = _t;
				JavaAST tmp67_AST_in = (JavaAST)_t;
				match(_t,LE);
				_t = _t.getFirstChild();
				expression(_t);
				_t = _retTree;
				tmp67_AST_in.print(out);
				expression(_t);
				_t = _retTree;
				_t = __t168;
				_t = _t.getNextSibling();
				break;
			}
			case GE:
			{
				AST __t169 = _t;
				JavaAST tmp68_AST_in = (JavaAST)_t;
				match(_t,GE);
				_t = _t.getFirstChild();
				expression(_t);
				_t = _retTree;
				tmp68_AST_in.print(out);
				expression(_t);
				_t = _retTree;
				_t = __t169;
				_t = _t.getNextSibling();
				break;
			}
			case SL:
			{
				AST __t170 = _t;
				JavaAST tmp69_AST_in = (JavaAST)_t;
				match(_t,SL);
				_t = _t.getFirstChild();
				expression(_t);
				_t = _retTree;
				tmp69_AST_in.print(out);
				expression(_t);
				_t = _retTree;
				_t = __t170;
				_t = _t.getNextSibling();
				break;
			}
			case SR:
			{
				AST __t171 = _t;
				JavaAST tmp70_AST_in = (JavaAST)_t;
				match(_t,SR);
				_t = _t.getFirstChild();
				expression(_t);
				_t = _retTree;
				tmp70_AST_in.print(out);
				expression(_t);
				_t = _retTree;
				_t = __t171;
				_t = _t.getNextSibling();
				break;
			}
			case BSR:
			{
				AST __t172 = _t;
				JavaAST tmp71_AST_in = (JavaAST)_t;
				match(_t,BSR);
				_t = _t.getFirstChild();
				expression(_t);
				_t = _retTree;
				tmp71_AST_in.print(out);
				expression(_t);
				_t = _retTree;
				_t = __t172;
				_t = _t.getNextSibling();
				break;
			}
			case PLUS:
			{
				AST __t173 = _t;
				JavaAST tmp72_AST_in = (JavaAST)_t;
				match(_t,PLUS);
				_t = _t.getFirstChild();
				expression(_t);
				_t = _retTree;
				tmp72_AST_in.print(out);
				expression(_t);
				_t = _retTree;
				_t = __t173;
				_t = _t.getNextSibling();
				break;
			}
			case CONCATENATION:
			{
				AST __t174 = _t;
				JavaAST tmp73_AST_in = (JavaAST)_t;
				match(_t,CONCATENATION);
				_t = _t.getFirstChild();
				expression(_t);
				_t = _retTree;
				tmp73_AST_in.print(out);
				expression(_t);
				_t = _retTree;
				_t = __t174;
				_t = _t.getNextSibling();
				break;
			}
			case MINUS:
			{
				AST __t175 = _t;
				JavaAST tmp74_AST_in = (JavaAST)_t;
				match(_t,MINUS);
				_t = _t.getFirstChild();
				expression(_t);
				_t = _retTree;
				tmp74_AST_in.print(out);
				expression(_t);
				_t = _retTree;
				_t = __t175;
				_t = _t.getNextSibling();
				break;
			}
			case DIV:
			{
				AST __t176 = _t;
				JavaAST tmp75_AST_in = (JavaAST)_t;
				match(_t,DIV);
				_t = _t.getFirstChild();
				expression(_t);
				_t = _retTree;
				tmp75_AST_in.print(out);
				expression(_t);
				_t = _retTree;
				_t = __t176;
				_t = _t.getNextSibling();
				break;
			}
			case MOD:
			{
				AST __t177 = _t;
				JavaAST tmp76_AST_in = (JavaAST)_t;
				match(_t,MOD);
				_t = _t.getFirstChild();
				expression(_t);
				_t = _retTree;
				tmp76_AST_in.print(out);
				expression(_t);
				_t = _retTree;
				_t = __t177;
				_t = _t.getNextSibling();
				break;
			}
			case STAR:
			{
				AST __t178 = _t;
				JavaAST tmp77_AST_in = (JavaAST)_t;
				match(_t,STAR);
				_t = _t.getFirstChild();
				expression(_t);
				_t = _retTree;
				tmp77_AST_in.print(out);
				expression(_t);
				_t = _retTree;
				_t = __t178;
				_t = _t.getNextSibling();
				break;
			}
			case INC:
			{
				AST __t179 = _t;
				JavaAST tmp78_AST_in = (JavaAST)_t;
				match(_t,INC);
				_t = _t.getFirstChild();
				tmp78_AST_in.print(out);
				expression(_t);
				_t = _retTree;
				_t = __t179;
				_t = _t.getNextSibling();
				break;
			}
			case DEC:
			{
				AST __t180 = _t;
				JavaAST tmp79_AST_in = (JavaAST)_t;
				match(_t,DEC);
				_t = _t.getFirstChild();
				tmp79_AST_in.print(out);
				expression(_t);
				_t = _retTree;
				_t = __t180;
				_t = _t.getNextSibling();
				break;
			}
			case POST_INC:
			{
				AST __t181 = _t;
				JavaAST tmp80_AST_in = (JavaAST)_t;
				match(_t,POST_INC);
				_t = _t.getFirstChild();
				expression(_t);
				_t = _retTree;
				tmp80_AST_in.print(out);
				_t = __t181;
				_t = _t.getNextSibling();
				break;
			}
			case POST_DEC:
			{
				AST __t182 = _t;
				JavaAST tmp81_AST_in = (JavaAST)_t;
				match(_t,POST_DEC);
				_t = _t.getFirstChild();
				expression(_t);
				_t = _retTree;
				tmp81_AST_in.print(out);
				_t = __t182;
				_t = _t.getNextSibling();
				break;
			}
			case BNOT:
			{
				AST __t183 = _t;
				JavaAST tmp82_AST_in = (JavaAST)_t;
				match(_t,BNOT);
				_t = _t.getFirstChild();
				tmp82_AST_in.print(out);
				expression(_t);
				_t = _retTree;
				_t = __t183;
				_t = _t.getNextSibling();
				break;
			}
			case LNOT:
			{
				AST __t184 = _t;
				JavaAST tmp83_AST_in = (JavaAST)_t;
				match(_t,LNOT);
				_t = _t.getFirstChild();
				tmp83_AST_in.print(out);
				expression(_t);
				_t = _retTree;
				_t = __t184;
				_t = _t.getNextSibling();
				break;
			}
			case LITERAL_instanceof:
			{
				AST __t185 = _t;
				i = _t==ASTNULL ? null :(JavaAST)_t;
				match(_t,LITERAL_instanceof);
				_t = _t.getFirstChild();
				expression(_t);
				_t = _retTree;
				i.print(out);
				expression(_t);
				_t = _retTree;
				_t = __t185;
				_t = _t.getNextSibling();
				break;
			}
			case UNARY_MINUS:
			{
				AST __t186 = _t;
				JavaAST tmp84_AST_in = (JavaAST)_t;
				match(_t,UNARY_MINUS);
				_t = _t.getFirstChild();
				tmp84_AST_in.print(out);
				expression(_t);
				_t = _retTree;
				_t = __t186;
				_t = _t.getNextSibling();
				break;
			}
			case UNARY_PLUS:
			{
				AST __t187 = _t;
				JavaAST tmp85_AST_in = (JavaAST)_t;
				match(_t,UNARY_PLUS);
				_t = _t.getFirstChild();
				tmp85_AST_in.print(out);
				expression(_t);
				_t = _retTree;
				_t = __t187;
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
		
		try {      // for error handling
			AST __t72 = _t;
			JavaAST tmp86_AST_in = (JavaAST)_t;
			match(_t,ARRAY_INIT);
			_t = _t.getFirstChild();
			tmp86_AST_in.print(out);
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
			JavaAST tmp87_AST_in = (JavaAST)_t;
			match(_t,RCURLY);
			_t = _t.getNextSibling();
			tmp87_AST_in.print(out);
			_t = __t72;
			_t = _t.getNextSibling();
		}
		catch (RecognitionException ex) {
			reportError(ex);
			if (_t!=null) {_t = _t.getNextSibling();}
		}
		_retTree = _t;
	}
	
	public final void commaInitializer(AST _t) throws RecognitionException {
		
		JavaAST commaInitializer_AST_in = (_t == ASTNULL) ? null : (JavaAST)_t;
		
		try {      // for error handling
			AST __t76 = _t;
			JavaAST tmp88_AST_in = (JavaAST)_t;
			match(_t,COMMA);
			_t = _t.getFirstChild();
			tmp88_AST_in.print(out);
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
			_t = __t76;
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
		JavaAST t = null;
		
		try {      // for error handling
			AST __t86 = _t;
			t = _t==ASTNULL ? null :(JavaAST)_t;
			match(_t,LITERAL_throws);
			_t = _t.getFirstChild();
			t.print(out);
			identifier(_t);
			_t = _retTree;
			{
			_loop88:
			do {
				if (_t==null) _t=ASTNULL;
				if ((_t.getType()==COMMA)) {
					JavaAST tmp89_AST_in = (JavaAST)_t;
					match(_t,COMMA);
					_t = _t.getNextSibling();
					tmp89_AST_in.print(out);
					identifier(_t);
					_t = _retTree;
				}
				else {
					break _loop88;
				}
				
			} while (true);
			}
			_t = __t86;
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
				AST __t99 = _t;
				JavaAST tmp90_AST_in = (JavaAST)_t;
				match(_t,TYPE_STAT);
				_t = _t.getFirstChild();
				typeDefinition(_t);
				_t = _retTree;
				_t = __t99;
				_t = _t.getNextSibling();
				break;
			}
			case EXPRESSION_STAT:
			{
				AST __t100 = _t;
				JavaAST tmp91_AST_in = (JavaAST)_t;
				match(_t,EXPRESSION_STAT);
				_t = _t.getFirstChild();
				expression(_t);
				_t = _retTree;
				sm1 = (JavaAST)_t;
				match(_t,SEMI);
				_t = _t.getNextSibling();
				_t = __t100;
				_t = _t.getNextSibling();
				sm1.print(out);
				break;
			}
			case LABELED_STAT:
			{
				AST __t101 = _t;
				JavaAST tmp92_AST_in = (JavaAST)_t;
				match(_t,LABELED_STAT);
				_t = _t.getFirstChild();
				c1 = (JavaAST)_t;
				match(_t,COLON);
				_t = _t.getNextSibling();
				tmp92_AST_in.print(out); c1.print(out);
				stat(_t);
				_t = _retTree;
				_t = __t101;
				_t = _t.getNextSibling();
				break;
			}
			case LITERAL_if:
			{
				AST __t102 = _t;
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
				_t = __t102;
				_t = _t.getNextSibling();
				break;
			}
			case LITERAL_for:
			{
				AST __t104 = _t;
				f = _t==ASTNULL ? null :(JavaAST)_t;
				match(_t,LITERAL_for);
				_t = _t.getFirstChild();
				l2 = (JavaAST)_t;
				match(_t,LPAREN);
				_t = _t.getNextSibling();
				f.print(out); l2.print(out);
				AST __t105 = _t;
				JavaAST tmp93_AST_in = (JavaAST)_t;
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
				_t = __t105;
				_t = _t.getNextSibling();
				AST __t107 = _t;
				JavaAST tmp94_AST_in = (JavaAST)_t;
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
				_t = __t107;
				_t = _t.getNextSibling();
				AST __t109 = _t;
				JavaAST tmp95_AST_in = (JavaAST)_t;
				match(_t,FOR_ITERATOR);
				_t = _t.getFirstChild();
				elist(_t);
				_t = _retTree;
				_t = __t109;
				_t = _t.getNextSibling();
				r2 = (JavaAST)_t;
				match(_t,RPAREN);
				_t = _t.getNextSibling();
				r2.print(out);
				stat(_t);
				_t = _retTree;
				_t = __t104;
				_t = _t.getNextSibling();
				break;
			}
			case LITERAL_while:
			{
				AST __t110 = _t;
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
				_t = __t110;
				_t = _t.getNextSibling();
				break;
			}
			case LITERAL_do:
			{
				AST __t111 = _t;
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
				_t = __t111;
				_t = _t.getNextSibling();
				break;
			}
			case LITERAL_break:
			{
				AST __t112 = _t;
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
				_t = __t112;
				_t = _t.getNextSibling();
				break;
			}
			case LITERAL_continue:
			{
				AST __t114 = _t;
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
				_t = __t114;
				_t = _t.getNextSibling();
				break;
			}
			case LITERAL_return:
			{
				AST __t116 = _t;
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
				_t = __t116;
				_t = _t.getNextSibling();
				break;
			}
			case LITERAL_switch:
			{
				AST __t118 = _t;
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
				JavaAST tmp96_AST_in = (JavaAST)_t;
				match(_t,LCURLY);
				_t = _t.getNextSibling();
				r5.print(out); tmp96_AST_in.print(out);
				{
				_loop120:
				do {
					if (_t==null) _t=ASTNULL;
					if ((_t.getType()==CASE_GROUP)) {
						caseGroup(_t);
						_t = _retTree;
					}
					else {
						break _loop120;
					}
					
				} while (true);
				}
				JavaAST tmp97_AST_in = (JavaAST)_t;
				match(_t,RCURLY);
				_t = _t.getNextSibling();
				tmp97_AST_in.print(out);
				_t = __t118;
				_t = _t.getNextSibling();
				break;
			}
			case LITERAL_throw:
			{
				AST __t121 = _t;
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
				_t = __t121;
				_t = _t.getNextSibling();
				break;
			}
			case LITERAL_synchronized:
			{
				AST __t122 = _t;
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
				_t = __t122;
				_t = _t.getNextSibling();
				break;
			}
			case LITERAL_assert:
			{
				AST __t123 = _t;
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
				_t = __t123;
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
				JavaAST tmp98_AST_in = (JavaAST)_t;
				match(_t,EMPTY_STAT);
				_t = _t.getNextSibling();
				tmp98_AST_in.print(out);
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
			AST __t140 = _t;
			JavaAST tmp99_AST_in = (JavaAST)_t;
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
				_loop143:
				do {
					if (_t==null) _t=ASTNULL;
					if ((_t.getType()==COMMA)) {
						JavaAST tmp100_AST_in = (JavaAST)_t;
						match(_t,COMMA);
						_t = _t.getNextSibling();
						tmp100_AST_in.print(out);
						expression(_t);
						_t = _retTree;
					}
					else {
						break _loop143;
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
			_t = __t140;
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
			AST __t126 = _t;
			JavaAST tmp101_AST_in = (JavaAST)_t;
			match(_t,CASE_GROUP);
			_t = _t.getFirstChild();
			{
			int _cnt129=0;
			_loop129:
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
					JavaAST tmp102_AST_in = (JavaAST)_t;
					match(_t,COLON);
					_t = _t.getNextSibling();
					tmp102_AST_in.print(out);
				}
				else {
					if ( _cnt129>=1 ) { break _loop129; } else {throw new NoViableAltException(_t);}
				}
				
				_cnt129++;
			} while (true);
			}
			{
			_loop131:
			do {
				if (_t==null) _t=ASTNULL;
				if ((_tokenSet_0.member(_t.getType()))) {
					stat(_t);
					_t = _retTree;
				}
				else {
					break _loop131;
				}
				
			} while (true);
			}
			_t = __t126;
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
			AST __t133 = _t;
			t = _t==ASTNULL ? null :(JavaAST)_t;
			match(_t,LITERAL_try);
			_t = _t.getFirstChild();
			t.print(out);
			slist(_t);
			_t = _retTree;
			{
			_loop135:
			do {
				if (_t==null) _t=ASTNULL;
				if ((_t.getType()==LITERAL_catch)) {
					handler(_t);
					_t = _retTree;
				}
				else {
					break _loop135;
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
			_t = __t133;
			_t = _t.getNextSibling();
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
			AST __t138 = _t;
			c = _t==ASTNULL ? null :(JavaAST)_t;
			match(_t,LITERAL_catch);
			_t = _t.getFirstChild();
			JavaAST tmp103_AST_in = (JavaAST)_t;
			match(_t,LPAREN);
			_t = _t.getNextSibling();
			c.print(out); tmp103_AST_in.print(out);
			parameterDef(_t);
			_t = _retTree;
			JavaAST tmp104_AST_in = (JavaAST)_t;
			match(_t,RPAREN);
			_t = _t.getNextSibling();
			tmp104_AST_in.print(out);
			slist(_t);
			_t = _retTree;
			_t = __t138;
			_t = _t.getNextSibling();
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
				JavaAST tmp105_AST_in = (JavaAST)_t;
				match(_t,IDENT);
				_t = _t.getNextSibling();
				tmp105_AST_in.print(out);
				break;
			}
			case DOT:
			{
				AST __t189 = _t;
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
						JavaAST tmp106_AST_in = (JavaAST)_t;
						match(_t,IDENT);
						_t = _t.getNextSibling();
						tmp106_AST_in.print(out);
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
						AST __t192 = _t;
						ne = _t==ASTNULL ? null :(JavaAST)_t;
						match(_t,LITERAL_new);
						_t = _t.getFirstChild();
						JavaAST tmp107_AST_in = (JavaAST)_t;
						match(_t,IDENT);
						_t = _t.getNextSibling();
						ne.print(out); tmp107_AST_in.print(out);
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
						_t = __t192;
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
					AST __t193 = _t;
					JavaAST tmp108_AST_in = (JavaAST)_t;
					match(_t,ARRAY_DECLARATOR);
					_t = _t.getFirstChild();
					type(_t);
					_t = _retTree;
					JavaAST tmp109_AST_in = (JavaAST)_t;
					match(_t,RBRACK);
					_t = _t.getNextSibling();
					_t = __t193;
					_t = _t.getNextSibling();
					tmp108_AST_in.print(out); tmp109_AST_in.print(out);
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
					builtInType(_t);
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
				_t = __t189;
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
				AST __t196 = _t;
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
				_t = __t196;
				_t = _t.getNextSibling();
				break;
			}
			case CONSTRUCTOR_CALL:
			{
				AST __t197 = _t;
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
				_t = __t197;
				_t = _t.getNextSibling();
				break;
			}
			case TYPECAST:
			{
				AST __t198 = _t;
				t = _t==ASTNULL ? null :(JavaAST)_t;
				match(_t,TYPECAST);
				_t = _t.getFirstChild();
				t.print(out);
				typeSpec(_t);
				_t = _retTree;
				r4 = (JavaAST)_t;
				match(_t,RPAREN);
				_t = _t.getNextSibling();
				r4.print(out);
				expression(_t);
				_t = _retTree;
				_t = __t198;
				_t = _t.getNextSibling();
				break;
			}
			case PAREN_EXPR:
			{
				AST __t199 = _t;
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
				_t = __t199;
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
				typeSpec(_t);
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
			AST __t201 = _t;
			JavaAST tmp110_AST_in = (JavaAST)_t;
			match(_t,INDEX_OP);
			_t = _t.getFirstChild();
			primaryExpression(_t);
			_t = _retTree;
			tmp110_AST_in.print(out);
			expression(_t);
			_t = _retTree;
			JavaAST tmp111_AST_in = (JavaAST)_t;
			match(_t,RBRACK);
			_t = _t.getNextSibling();
			tmp111_AST_in.print(out);
			_t = __t201;
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
			AST __t204 = _t;
			n = _t==ASTNULL ? null :(JavaAST)_t;
			match(_t,LITERAL_new);
			_t = _t.getFirstChild();
			n.print(out);
			type(_t);
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
				JavaAST tmp112_AST_in = (JavaAST)_t;
				match(_t,LPAREN);
				_t = _t.getNextSibling();
				tmp112_AST_in.print(out);
				elist(_t);
				_t = _retTree;
				JavaAST tmp113_AST_in = (JavaAST)_t;
				match(_t,RPAREN);
				_t = _t.getNextSibling();
				tmp113_AST_in.print(out);
				{
				if (_t==null) _t=ASTNULL;
				switch ( _t.getType()) {
				case LITERAL_class:
				{
					AST __t208 = _t;
					JavaAST tmp114_AST_in = (JavaAST)_t;
					match(_t,LITERAL_class);
					_t = _t.getFirstChild();
					objBlock(_t);
					_t = _retTree;
					_t = __t208;
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
			_t = __t204;
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
				JavaAST tmp115_AST_in = (JavaAST)_t;
				match(_t,NUM_INT);
				_t = _t.getNextSibling();
				tmp115_AST_in.print(out);
				break;
			}
			case CHAR_LITERAL:
			{
				JavaAST tmp116_AST_in = (JavaAST)_t;
				match(_t,CHAR_LITERAL);
				_t = _t.getNextSibling();
				tmp116_AST_in.print(out);
				break;
			}
			case STRING_LITERAL:
			{
				JavaAST tmp117_AST_in = (JavaAST)_t;
				match(_t,STRING_LITERAL);
				_t = _t.getNextSibling();
				tmp117_AST_in.print(out);
				break;
			}
			case NUM_FLOAT:
			{
				JavaAST tmp118_AST_in = (JavaAST)_t;
				match(_t,NUM_FLOAT);
				_t = _t.getNextSibling();
				tmp118_AST_in.print(out);
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
	
	public final void newArrayDeclarator(AST _t) throws RecognitionException {
		
		JavaAST newArrayDeclarator_AST_in = (_t == ASTNULL) ? null : (JavaAST)_t;
		
		try {      // for error handling
			AST __t210 = _t;
			JavaAST tmp119_AST_in = (JavaAST)_t;
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
			tmp119_AST_in.print(out);
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
			JavaAST tmp120_AST_in = (JavaAST)_t;
			match(_t,RBRACK);
			_t = _t.getNextSibling();
			tmp120_AST_in.print(out);
			_t = __t210;
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
	}
	
