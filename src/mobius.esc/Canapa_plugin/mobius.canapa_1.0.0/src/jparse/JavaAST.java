/*
 * @(#)$Id: JavaAST.java,v 1.3 2004/07/08 18:03:54 bdg534 Exp $
 *
 * JParse: a freely available Java parser
 * Copyright (C) 2000,2004 Jeremiah W. James
 *
 * This library is free software; you can redistribute it and/or modify it
 * under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation; either version 2.1 of the License, or (at
 * your option) any later version.
 *
 * This library is distributed in the hope that it will be useful, but
 * WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.
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
package jparse;

import java.io.IOException;
import java.io.OutputStreamWriter;

import antlr.BaseAST;
import antlr.CommonASTWithHiddenTokens;
import antlr.CommonHiddenStreamToken;
import antlr.Token;
import antlr.collections.AST;

/**
 * An AST node that is a superclass for all Java AST types.
 * 
 * @version $Revision: 1.3 $, $Date: 2004/07/08 18:03:54 $
 * @author Jerry James
 */
public class JavaAST extends CommonASTWithHiddenTokens {

	/**
	 * An empty array of types, for use in parameter and exception lists when
	 * there are none; avoids creating new arrays when it is unnecessary without
	 * resorting to lots of <code>null</code> checks
	 */
	protected static final Type[] noTypes = new Type[0];

	/**
	 * The current symbol table under construction
	 */
	protected static SymbolTable currSymTable;

	/**
	 * The current compilation context
	 */
	protected static CompileContext context;

	/**
	 * The symbols in the context of this AST node
	 */
	public final SymbolTable symTable;

	/**
	 * The top-level node for this file
	 */
	public final FileAST topLevel;

	/**
	 * The type (class or interface) containing this AST node
	 */
	public final TypeAST typeAST;

	/**
	 * Create a new Java AST
	 */
	public JavaAST() {
		super();
		symTable = currSymTable;
		topLevel = FileAST.currFile;
		typeAST = TypeAST.currType;
	}

	/**
	 * Create a new Java AST with an existing symbol table
	 * 
	 * @param table
	 *            the symbol table to use
	 */
	public JavaAST(final SymbolTable table) {
		super();
		symTable = currSymTable = table;
		topLevel = FileAST.currFile;
		typeAST = TypeAST.currType;
	}

	/**
	 * Create a new Java AST from a token
	 * 
	 * @param token
	 *            the token represented by this AST node
	 */
	public JavaAST(final Token token) {
		super(token);
		symTable = currSymTable;
		topLevel = FileAST.currFile;
		typeAST = TypeAST.currType;
	}

	/**
	 * Create a new Java AST from a token, with an existing symbol table
	 * 
	 * @param token
	 *            the token represented by this AST node
	 * @param table
	 *            the symbol table to use
	 */
	public JavaAST(final Token token, final SymbolTable table) {
		super(token);
		symTable = currSymTable = table;
		topLevel = FileAST.currFile;
		typeAST = TypeAST.currType;
	}

	/**
	 * Print a representation of this AST node, and its following hidden tokens
	 * 
	 * @param output
	 *            the output stream on which to print
	 */
	public final void print(final OutputStreamWriter output) {

		try {
			String o1 = "", o2 = "";
			o1 = getText();
			//o1 = "<"+ this.getClass().getName() + ": " + o1 + ">";
			output.write(o1);
			//output.write("<" + getText() + ">");
			
			for (CommonHiddenStreamToken t = getHiddenAfter(); t != null; t = t
					.getHiddenAfter()) {
				o2 = t.getText();
				//o2 = "[" + o2 + "]";
				output.write(o2);
			}
		} catch (IOException ioex) {
			//Should not happen
		}
	}
	
	/**
	 * Print any hidden tokens after this AST node
	 * 
	 * @param output
	 *            the output stream on which to print
	 */
	public final void printHiddenAfter(final OutputStreamWriter output) {
		try {
			for (CommonHiddenStreamToken t = getHiddenAfter(); t != null; t = t
					.getHiddenAfter())
				output.write(t.getText());
		} catch (IOException ioex) {
			//Should not happen
		}
	}

	/**
	 * Print any hidden tokens before this AST node
	 * 
	 * @param output
	 *            the output stream on which to print
	 */
	public final void printHiddenBefore(final OutputStreamWriter output) {
		CommonHiddenStreamToken tok = getHiddenBefore();
		CommonHiddenStreamToken last = null;
		while (tok != null) {
			last = tok;
			tok = tok.getHiddenBefore();
		}
		try {
			for (CommonHiddenStreamToken t = last; t != null; t = t
					.getHiddenAfter())
				output.write(t.getText());
		} catch (IOException ioex) {
			//Should not happen
		}
	}

	/**
	 * Compute any derived attributes that must be evaluated <em>after</em>
	 * the initial parse. The default action is to just tell your children that
	 * the parse is complete.
	 */
	public void parseComplete() {
		for (JavaAST a = (JavaAST) getFirstChild(); a != null; a = (JavaAST) a
				.getNextSibling()) {
			a.parseComplete();
		}
	}
	/**
	 * @param out
	 */
	public void wypiszSie(OutputStreamWriter out) {
		try {
			out.write("ELLO\n");
			// TODO Auto-generated method stub
			wypiszSieZWcieciem(this, out, 0);
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}

	/**
	 * @param i
	 * @throws IOException
	 */
	private void wypiszSieZWcieciem(AST cosss, OutputStreamWriter out, int wciecie) throws IOException {
		JavaAST cos = (JavaAST) cosss;
		out.write(wciecia(wciecie) + cos.getClass().getName() +": "+ cos.getText() + "\n");
		if (cos.getHiddenBefore() != null) {
			for (CommonHiddenStreamToken t = cos.getHiddenBefore(); t != null; t = t
			.getHiddenBefore()) {
				out.write(wciecia(wciecie+1) + "BEFORE ("+t.getLine()+"/"+t.getColumn()+"): #" + t.getText()+ "#\n");
			}
		}
		if (cos.getFirstChild() != null) {
			wypiszSieZWcieciem(cos.getFirstChild(), out, wciecie+1);
		}
		if (cos.getHiddenAfter() != null) {
			for (CommonHiddenStreamToken t = cos.getHiddenAfter(); t != null; t = t
			.getHiddenAfter()) {
				out.write(wciecia(wciecie+1) + "AFTER ("+t.getLine()+"/"+t.getColumn()+"): #" + t.getText()+ "#\n");
			}
		}
		if (cos.getNextSibling() != null) {
			wypiszSieZWcieciem(cos.getNextSibling(), out, wciecie);
		}


	}
	
	public JavaAST getSon() {
		return (JavaAST)this.down;
	}
	
	public JavaAST getBrother() {
		return (JavaAST)this.right;
	}
	
	private String wciecia(int w) {
		if (w == 0)
			return "";
		return "\t" + wciecia(w-1);
	}

	/**
	 * @param annotation
	 * @return
	 */
	public CommonHiddenStreamToken addHiddenBefore(String annotation) {
		CommonHiddenStreamToken x;
		if (this.hiddenBefore == null) {
			x = new CommonHiddenStreamToken(annotation);
		} else {
			x = this.hiddenBefore;
			x.setText(x.getText() + annotation);
		}
		return x;
	}

	/**
	 * @param x
	 */
	public void setHiddenAfter(CommonHiddenStreamToken x) {
		this.hiddenAfter = x;
	}
}
