/*
 * @(#)$Id: ConditionalAST.java,v 1.2 2004/04/02 05:48:47 james Exp $
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
import jparse.Type;
import jparse.VarList;

/**
 * An AST node that represents a conditional expression
 *
 * @version $Revision: 1.2 $, $Date: 2004/04/02 05:48:47 $
 * @author Jerry James
 */
public final class ConditionalAST extends ExpressionAST {

    /**
     * The "condition" part of the conditional
     */
    private ExpressionAST conditionPart;

    /**
     * The "then" part of the conditional
     */
    private ExpressionAST thenPart;

    /**
     * The "else" part of the conditional
     */
    private ExpressionAST elsePart;

    /**
     * Create a new conditional expression AST
     *
     * @param token the token represented by this AST node
     */
    public ConditionalAST(final Token token) {
	super(token);
    }

    public void parseComplete() {
	conditionPart = (ExpressionAST)getFirstChild();
	thenPart = (ExpressionAST)conditionPart.getNextSibling();
	elsePart = (ExpressionAST)thenPart.getNextSibling().getNextSibling();
	conditionPart.parseComplete();
	thenPart.parseComplete();
	elsePart.parseComplete();
    }

    protected Type computeType() {
	// The type of a conditional is the lowest common demoninator of its
	// "then" and "else" parts
	final Type thenType = thenPart.retrieveType();
	final Type elseType = elsePart.retrieveType();
	if (thenType == null)
	    return elseType;
	if (elseType == null)
	    return thenType;
	if (thenType == elseType)
	    return thenType;
	if (thenType.isAssignableFrom(elseType))
	    return thenType;
	if (elseType.isAssignableFrom(thenType))
	    return elseType;
	// FIXME: This is an error
	System.err.println("Couldn't compare " + thenType.getName() + " and "
			   + elseType.getName());
	return thenType;
    }

    protected Type[] computeExceptions() {
	// We have to merge all exceptions from the conditional, then part,
	// and else part
	final Type[] e1 = conditionPart.getExceptionTypes();
	final Type[] e2 = thenPart.getExceptionTypes();
	final Type[] e3 = elsePart.getExceptionTypes();

	return Type.mergeTypeLists(Type.mergeTypeLists(e1, e2), e3);
    }

    protected Object computeValue() {
	final Boolean cond = (Boolean)conditionPart.getValue();
	if (cond == nonconstant)
	    return nonconstant;

	// Isn't this ironic?  FIXME: Actually, this isn't safe, since we may
	// have to promote to a larger primitive type, depending on what
	// retrieveType() tells us.
	return cond.booleanValue()
	    ? thenPart.getValue()
	    : elsePart.getValue();
    }

    public VarList getVarList() {
	return new VarList(conditionPart.getVarList(), thenPart.getVarList(),
			   elsePart.getVarList());
    }

    /**
     * Get the condition part of this conditional expression
     *
     * @return the condition part of the expression
     */
    public ExpressionAST getCondition() {
	return conditionPart;
    }

    /**
     * Get the then part of this conditional expression
     *
     * @return the then of the expression
     */
    public ExpressionAST getThen() {
	return thenPart;
    }

    /**
     * Get the else part of this conditional expression
     *
     * @return the else part of the expression
     */
    public ExpressionAST getElse() {
	return elsePart;
    }
}
