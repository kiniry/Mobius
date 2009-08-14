/*
 * @(#)$Id: ShiftAST.java,v 1.2 2004/04/02 05:48:48 james Exp $
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
package jparse.expr;

import antlr.Token;
import jparse.JavaTokenTypes;
import jparse.Type;
import jparse.VarList;

/**
 * An AST node that represents a shift expression
 *
 * @version $Revision: 1.2 $, $Date: 2004/04/02 05:48:48 $
 * @author Jerry James
 */
public final class ShiftAST extends ExpressionAST implements JavaTokenTypes {

    /**
     * The left expression
     */
    private ExpressionAST left;

    /**
     * The right expression
     */
    private ExpressionAST right;

    /**
     * Create a new shift expression AST
     *
     * @param token the token represented by this AST node
     */
    public ShiftAST(final Token token) {
	super(token);
    }

    public void parseComplete() {
	left = (ExpressionAST)getFirstChild();
	right = (ExpressionAST)left.getNextSibling();
	left.parseComplete();
	right.parseComplete();
    }

    protected Type computeType() {
	// See JLS 15.19
	final Type leftType = left.retrieveType();
	return (leftType == Type.byteType || leftType == Type.shortType ||
		leftType == Type.charType)
	    ? Type.intType
	    : leftType;
    }

    protected Type[] computeExceptions() {
	return noTypes;
    }

    protected Object computeValue() {
	final Object leftObj = left.getValue();
	if (leftObj == nonconstant)
	    return nonconstant;

	final Object rightObj = right.getValue();
	if (rightObj == nonconstant)
	    return nonconstant;

	final Type myType = retrieveType();
	final int operator = getType();
	if (myType == Type.intType) {
	    final int leftVal = ((Number)leftObj).intValue();
	    final int rightVal = ((Number)rightObj).intValue();
	    return new Integer((operator == SL) ? leftVal << rightVal
			       : ((operator == SR) ? leftVal >> rightVal
				  : leftVal >>> rightVal));
	} else {	// long
	    final long leftVal = ((Number)leftObj).longValue();
	    final long rightVal = ((Number)rightObj).longValue();
	    return new Long((operator == SL) ? leftVal << rightVal
			    : ((operator == SR) ? leftVal >> rightVal
			       : leftVal >>> rightVal));
	}
    }

    public VarList getVarList() {
	return new VarList(left.getVarList(), right.getVarList());
    }

    /**
     * Get the left-hand-side of this shift expression
     *
     * @return the lhs of the expression
     */
    public ExpressionAST getLeft() {
	return left;
    }

    /**
     * Get the right-hand-side of this shift expression
     *
     * @return the rhs of the expression
     */
    public ExpressionAST getRight() {
	return right;
    }
}
