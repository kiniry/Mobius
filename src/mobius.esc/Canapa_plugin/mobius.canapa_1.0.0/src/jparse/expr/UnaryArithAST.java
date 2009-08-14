/*
 * @(#)$Id: UnaryArithAST.java,v 1.2 2004/04/02 05:48:48 james Exp $
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
 * An AST node that represents a unary arithmetic expression
 *
 * @version $Revision: 1.2 $, $Date: 2004/04/02 05:48:48 $
 * @author Jerry James
 */
public final class UnaryArithAST extends ExpressionAST
    implements JavaTokenTypes {

    /**
     * The expression on which to perform this unary operation
     */
    private ExpressionAST operand;

    /**
     * Create a new unary arithmetic expression AST
     *
     * @param token the token represented by this AST node
     */
    public UnaryArithAST(final Token token) {
	super(token);
    }

    public void parseComplete() {
	if (getType() == MINUS)
	    context.negative = !context.negative;
	operand = (ExpressionAST)getFirstChild();
	operand.parseComplete();
    }

    protected Type computeType() {
	// See JLS 15.15
	final int tokType = getType();
	final Type opType = operand.retrieveType();
	return tokType != INC && tokType != DEC &&
	    (opType == Type.byteType || opType == Type.shortType || 
	     opType == Type.charType)
	    ? Type.intType
	    : opType;
    }

    protected Type[] computeExceptions() {
	return operand.getExceptionTypes();
    }

    protected Object computeValue() {
	// Don't bother with operators that have to modify a variable
	final int operator = getType();
	if (operator == INC || operator == DEC || operator == POST_INC ||
	    operator == POST_DEC)
	    return nonconstant;

	final Object subval = operand.getValue();
	if (subval == nonconstant)
	    return nonconstant;

	// The operator is PLUS (no effect), MINUS (also no effect, since the
	// parser accounted for it already), or BNOT.
	if (operator == PLUS || operator == MINUS)
	    return subval;

	// It is a bitwise NOT operator, and the type is either int or long
	final Number num = (Number)subval;
	return (retrieveType() == Type.intType)
	    ? (Object)new Integer(~num.intValue())
	    : (Object)new Long(~num.longValue());
    }

    public VarList getVarList() {
	return operand.getVarList();
    }

    /**
     * Get the operand of this operator
     *
     * @return the operand
     */
    public ExpressionAST getOperand() {
	return operand;
    }
}
