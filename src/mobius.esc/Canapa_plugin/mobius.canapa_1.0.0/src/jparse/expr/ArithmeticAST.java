/*
 * @(#)$Id: ArithmeticAST.java,v 1.2 2004/04/02 05:48:47 james Exp $
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
 * An AST node that represents an arithmetic expression
 *
 * @version $Revision: 1.2 $, $Date: 2004/04/02 05:48:47 $
 * @author Jerry James
 */
public final class ArithmeticAST extends ExpressionAST
    implements JavaTokenTypes {

    /**
     * The left expression
     */
    private ExpressionAST left;

    /**
     * The right expression
     */
    private ExpressionAST right;

    /**
     * Create a new arithmetic expression AST
     *
     * @param token the token represented by this AST node
     */
    public ArithmeticAST(final Token token) {
	super(token);
    }

    public void parseComplete() {
	left = (ExpressionAST)getFirstChild();
	right = (ExpressionAST)left.getNextSibling();
	final int type = getType();
	if (type == STAR || type == DIV || type == MOD) {
	    context.negative = false;
	}
	left.parseComplete();
	if (type == STAR || type == DIV || type == MOD) {
	    context.negative = false;
	}
	right.parseComplete();
    }

    protected Type computeType() {
	// See JLS 15.17 - 15.18
	final Type leftType = left.retrieveType();
	final Type rightType = right.retrieveType();
	if (getType() == PLUS &&
	    (leftType == Type.stringType || rightType == Type.stringType)) {
	    setType(CONCATENATION);
	    return Type.stringType;
	}
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
	final int operator = getType();
	if (operator == CONCATENATION)
	    return leftObj.toString() + rightObj.toString();
	final Number leftNum = (Number)leftObj;
	final Number rightNum = (Number)rightObj;
	switch (operator) {
	case PLUS:
	    if (myType == Type.doubleType)
		return new Double(leftNum.doubleValue() +
				  rightNum.doubleValue());
	    else if (myType == Type.floatType)
		return new Float(leftNum.floatValue() + rightNum.floatValue());
	    else if (myType == Type.longType)
		return new Long(leftNum.longValue() + rightNum.longValue());
	    else // Type.intType
		return new Integer(leftNum.intValue() + rightNum.intValue());
	case MINUS:
	    if (myType == Type.doubleType)
		return new Double(leftNum.doubleValue() -
				  rightNum.doubleValue());
	    else if (myType == Type.floatType)
		return new Float(leftNum.floatValue() - rightNum.floatValue());
	    else if (myType == Type.longType)
		return new Long(leftNum.longValue() - rightNum.longValue());
	    else // Type.intType
		return new Integer(leftNum.intValue() - rightNum.intValue());
	case STAR:
	    if (myType == Type.doubleType)
		return new Double(leftNum.doubleValue() *
				  rightNum.doubleValue());
	    else if (myType == Type.floatType)
		return new Float(leftNum.floatValue() * rightNum.floatValue());
	    else if (myType == Type.longType)
		return new Long(leftNum.longValue() * rightNum.longValue());
	    else // Type.intType
		return new Integer(leftNum.intValue() * rightNum.intValue());
	case DIV:
	    if (myType == Type.doubleType)
		return new Double(leftNum.doubleValue() /
				  rightNum.doubleValue());
	    else if (myType == Type.floatType)
		return new Float(leftNum.floatValue() / rightNum.floatValue());
	    else if (myType == Type.longType)
		return new Long(leftNum.longValue() / rightNum.longValue());
	    else // Type.intType
		return new Integer(leftNum.intValue() / rightNum.intValue());
	case MOD:
	    if (myType == Type.longType)
		return new Long(leftNum.longValue() % rightNum.longValue());
	    else // Type.intType
		return new Integer(leftNum.intValue() % rightNum.intValue());
	default:
	    return nonconstant;
	}
    }

    public VarList getVarList() {
	return new VarList(left.getVarList(), right.getVarList());
    }

    /**
     * Get the left-hand-side of this arithmetic expression
     *
     * @return the lhs of the expression
     */
    public ExpressionAST getLeft() {
	return left;
    }

    /**
     * Get the right-hand-side of this arithmetic expression
     *
     * @return the rhs of the expression
     */
    public ExpressionAST getRight() {
	return right;
    }
}
