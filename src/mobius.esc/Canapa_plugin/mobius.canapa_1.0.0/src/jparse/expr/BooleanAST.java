/*
 * @(#)$Id: BooleanAST.java,v 1.2 2004/04/02 05:48:47 james Exp $
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
 * An AST node that represents a boolean expression
 *
 * @version $Revision: 1.2 $, $Date: 2004/04/02 05:48:47 $
 * @author Jerry James
 */
public final class BooleanAST extends ExpressionAST implements JavaTokenTypes {

    /**
     * The left expression
     */
    private ExpressionAST left;

    /**
     * The right expression
     */
    private ExpressionAST right;

    /**
     * Create a new boolean expression AST
     *
     * @param token the token represented by this AST node
     */
    public BooleanAST(final Token token) {
	super(token);
    }

    public void parseComplete() {
	left = (ExpressionAST)getFirstChild();
	right = (ExpressionAST)left.getNextSibling();
	left.parseComplete();
	if (right != null)
	    right.parseComplete();
    }

    protected Type computeType() {
	return Type.booleanType;
    }

    protected Type[] computeExceptions() {
	return (right == null)
	    ? left.getExceptionTypes()	// Logical not (!) operator
	    : Type.mergeTypeLists(left.getExceptionTypes(),
				  right.getExceptionTypes());
    }

    protected Object computeValue() {
	final Object leftObj = left.getValue();
	if (leftObj == nonconstant)
	    return nonconstant;

	// Watch out for short-circuiting!
	final int operator = getType();
	if ((operator == LOR && ((Boolean)leftObj).booleanValue()) ||
	    (operator == LAND && !((Boolean)leftObj).booleanValue()))
	    return leftObj;
	// Don't do the same for rightObj if leftObj is (or contains) a method
	// call, since we can't predict things like program exit or
	// exceptions.  Without method calls, it is safe to do the same for
	// rightObj.

	if (operator == LNOT)
	    return new Boolean(!((Boolean)leftObj).booleanValue());

	if (right == null)
	    return leftObj;

	final Object rightObj = right.getValue();
	if (rightObj == nonconstant)
	    return nonconstant;

	// Both constant!  We have a winner!
	switch (operator) {
	case LOR:
	    return new Boolean(((Boolean)leftObj).booleanValue() ||
			       ((Boolean)rightObj).booleanValue());
	case LAND:
	    return new Boolean(((Boolean)leftObj).booleanValue() &&
			       ((Boolean)rightObj).booleanValue());
	case NOT_EQUAL:
	    return new Boolean(!leftObj.equals(rightObj));
	case EQUAL:
	    return new Boolean(leftObj.equals(rightObj));
	case LITERAL_instanceof:
	    return new Boolean
		(right.retrieveType() == Type.forClass(leftObj.getClass()));
	default:
	    break;
	}

	final Type compareType = Type.arithType(left.retrieveType(),
						right.retrieveType());
	if (compareType == Type.doubleType) {
	    final double leftDouble = ((Number)leftObj).doubleValue();
	    final double rightDouble = ((Number)rightObj).doubleValue();
	    switch (operator) {
	    case LT:
		return new Boolean(leftDouble < rightDouble);
	    case GT:
		return new Boolean(leftDouble > rightDouble);
	    case LE:
		return new Boolean(leftDouble <= rightDouble);
	    case GE:
		return new Boolean(leftDouble >= rightDouble);
	    }
	} else if (compareType == Type.floatType) {
	    final float leftFloat = ((Number)leftObj).floatValue();
	    final float rightFloat = ((Number)rightObj).floatValue();
	    switch (operator) {
	    case LT:
		return new Boolean(leftFloat < rightFloat);
	    case GT:
		return new Boolean(leftFloat > rightFloat);
	    case LE:
		return new Boolean(leftFloat <= rightFloat);
	    case GE:
		return new Boolean(leftFloat >= rightFloat);
	    }
	} else if (compareType == Type.longType) {
	    final long leftLong = ((Number)leftObj).longValue();
	    final long rightLong = ((Number)rightObj).longValue();
	    switch (operator) {
	    case LT:
		return new Boolean(leftLong < rightLong);
	    case GT:
		return new Boolean(leftLong > rightLong);
	    case LE:
		return new Boolean(leftLong <= rightLong);
	    case GE:
		return new Boolean(leftLong >= rightLong);
	    }
	} else /* if (compareType == Type.intType) */ {
	    final long leftLong = ((Number)leftObj).longValue();
	    final long rightLong = ((Number)rightObj).longValue();
	    switch (operator) {
	    case LT:
		return new Boolean(leftLong < rightLong);
	    case GT:
		return new Boolean(leftLong > rightLong);
	    case LE:
		return new Boolean(leftLong <= rightLong);
	    case GE:
		return new Boolean(leftLong >= rightLong);
	    }
	}
	return nonconstant;
    }

    public VarList getVarList() {
	return (right == null)
	    ? left.getVarList()
	    : new VarList(left.getVarList(), right.getVarList());
    }

    /**
     * Get the left-hand-side of this boolean expression
     *
     * @return the lhs of the expression
     */
    public ExpressionAST getLeft() {
	return left;
    }

    /**
     * Get the right-hand-side of this boolean expression
     *
     * @return the rhs of the expression
     */
    public ExpressionAST getRight() {
	return right;
    }
}
