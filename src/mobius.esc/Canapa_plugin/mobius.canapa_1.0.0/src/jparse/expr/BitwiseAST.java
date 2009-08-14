/*
 * @(#)$Id: BitwiseAST.java,v 1.2 2004/04/02 05:48:47 james Exp $
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
 * An AST node that represents a bitwise expression
 *
 * @version $Revision: 1.2 $, $Date: 2004/04/02 05:48:47 $
 * @author Jerry James
 */
public final class BitwiseAST extends ExpressionAST implements JavaTokenTypes {

    /**
     * The left expression
     */
    private ExpressionAST left;

    /**
     * The right expression
     */
    private ExpressionAST right;

    /**
     * Create a new bitwise expression AST
     *
     * @param token the token represented by this AST node
     */
    public BitwiseAST(final Token token) {
	super(token);
    }

    public void parseComplete() {
	left = (ExpressionAST)getFirstChild();
	right = (ExpressionAST)left.getNextSibling();
	left.parseComplete();
	right.parseComplete();
    }

    protected Type computeType() {
	// See JLS 15.22
	final Type leftType = left.retrieveType();
	if (leftType == Type.booleanType)
	    return leftType;
	final Type rightType = right.retrieveType();
	return Type.arithType(leftType, rightType);
    }

    protected Type[] computeExceptions() {
	return Type.mergeTypeLists(left.getExceptionTypes(),
				   right.getExceptionTypes());
    }

    protected Object computeValue() {
	final Object leftObj = left.getValue();
	if (leftObj == nonconstant)
	    return nonconstant;
	final Object rightObj = right.getValue();
	if (rightObj == nonconstant)
	    return nonconstant;

	// Both constant!  We have a winner!
	final Type myType = retrieveType();
	if (myType == Type.booleanType) {
	    final boolean leftBool = ((Boolean)leftObj).booleanValue();
	    final boolean rightBool = ((Boolean)rightObj).booleanValue();
	    switch (getType()) {
	    case BOR:
		return new Boolean(leftBool | rightBool);
	    case BXOR:
		return new Boolean(leftBool ^ rightBool);
	    case BAND:
		return new Boolean(leftBool & rightBool);
	    }
	} else if (myType == Type.longType) {
	    final long leftLong = ((Number)leftObj).longValue();
	    final long rightLong = ((Number)rightObj).longValue();
	    switch (getType()) {
	    case BOR:
		return new Long(leftLong | rightLong);
	    case BXOR:
		return new Long(leftLong ^ rightLong);
	    case BAND:
		return new Long(leftLong & rightLong);
	    }
	} else /* if (myType == Type.intType) */ {
	    final int leftInt = ((Number)leftObj).intValue();
	    final int rightInt = ((Number)rightObj).intValue();
	    switch (getType()) {
	    case BOR:
		return new Integer(leftInt | rightInt);
	    case BXOR:
		return new Integer(leftInt ^ rightInt);
	    case BAND:
		return new Integer(leftInt & rightInt);
	    }
	}
	return nonconstant;
    }

    public VarList getVarList() {
	return new VarList(left.getVarList(), right.getVarList());
    }

    /**
     * Get the left-hand-side of this bitwise expression
     *
     * @return the lhs of the expression
     */
    public ExpressionAST getLeft() {
	return left;
    }

    /**
     * Get the right-hand-side of this bitwise expression
     *
     * @return the rhs of the expression
     */
    public ExpressionAST getRight() {
	return right;
    }
}
