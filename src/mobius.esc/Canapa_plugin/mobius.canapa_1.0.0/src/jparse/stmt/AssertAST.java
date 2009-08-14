/*
 * @(#)$Id: AssertAST.java,v 1.1 2004/06/22 18:16:25 james Exp $
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
package jparse.stmt;

import antlr.Token;
import antlr.collections.AST;
import jparse.JavaTokenTypes;
import jparse.Type;
import jparse.VarList;

/**
 * An AST node that represents an assertion statement
 *
 * @version $Revision: 1.1 $, $Date: 2004/06/22 18:16:25 $
 * @author Jerry James
 */
public final class AssertAST extends StatementAST {

    // FIXME: Figure out what expr1 and expr2 should really be named

    /**
     * The first expression
     */
    private jparse.expr.ExpressionAST expr1;

    /**
     * The second expression
     */
    private jparse.expr.ExpressionAST expr2;

    /**
     * Create a new assertion statement AST
     *
     * @param token the token represented by this AST node
     */
    public AssertAST(final Token token) {
	super(token);
    }

    public void parseComplete() {
	super.parseComplete();
	expr1 = (jparse.expr.ExpressionAST)getFirstChild();
	expr1.parseComplete();
	final AST punctuation = expr1.getNextSibling();
	if (punctuation.getType() == JavaTokenTypes.COLON) {
	    expr2 = (jparse.expr.ExpressionAST)punctuation.getNextSibling();
	    expr2.parseComplete();
	}
    }

    protected Type[] computeExceptions() {
	return (expr2 == null)
	    ? expr1.getExceptionTypes()
	    : Type.mergeTypeLists(expr1.getExceptionTypes(),
				  expr2.getExceptionTypes());
    }

    protected StatementAST[] computeControl() {
	return new StatementAST[] { next };
    }

    public VarList getVarList() {
	return (expr2 == null)
	    ? expr1.getVarList()
	    : new VarList(expr1.getVarList(), expr2.getVarList());
    }

    /**
     * Get the first expression
     *
     * @return the first expression
     */
    public jparse.expr.ExpressionAST getFirstExpression() {
	return expr1;
    }

    /**
     * Get the second expression
     *
     * @return the second expression
     */
    public jparse.expr.ExpressionAST getSecondExpression() {
	return expr2;
    }
}
