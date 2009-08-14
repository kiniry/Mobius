/*
 * @(#)$Id: ExpressionAST.java,v 1.2 2004/04/02 05:48:48 james Exp $
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
import jparse.HasExceptions;
import jparse.JavaAST;
import jparse.Type;
import jparse.VarList;

/**
 * An AST node that represents an expression
 *
 * @version $Revision: 1.2 $, $Date: 2004/04/02 05:48:48 $
 * @author Jerry James
 */
public abstract class ExpressionAST extends JavaAST implements HasExceptions {

    /**
     * A dummy object used to determine when the value has been computed
     */
    private static final Object noVal = new Object();

    /**
     * A dummy object that indicates that an expression is not constant
     */
    public static final Object nonconstant = new Object();

    /**
     * The type of this expression
     */
    protected Type type;

    /**
     * The checked exceptions this expression might throw
     */
    protected Type[] exceptions;

    /**
     * The constant value of this expression (possibly wrapped), or
     * <code>null</code> if the expression is not constant
     */
    protected Object value = noVal;

    /**
     * Create a new expression AST
     */
    protected ExpressionAST() {
	super();
    }

    /**
     * Create a new expression AST
     *
     * @param token the token represented by this AST node
     */
    protected ExpressionAST(final Token token) {
	super(token);
    }

    /**
     * Retrieve the type of this expression
     *
     * @return the type of this expression
     */
    public final Type retrieveType() {
	if (type == null)
	    type = computeType();
	return type;
    }

    /**
     * Compute the type of this expression
     *
     * @return the type of this expression
     */
    protected abstract Type computeType();

    /**
     * Get the checked exception types that might be thrown by this expression
     *
     * @return an array of types representing the exceptions that this
     * expression might throw
     */
    public final Type[] getExceptionTypes() {
	if (exceptions == null)
	    exceptions = computeExceptions();
	return exceptions;
    }

    /**
     * Compute the checked exception types that might be thrown by this
     * expression
     *
     * @return an array of types representing the exceptions that this
     * expression might throw
     */
    protected abstract Type[] computeExceptions();

    /**
     * Get the constant value of this expression, if it has one, or
     * <code>null</code> if it does not
     *
     * @return the constant value (if any) of this expression, as a wrapped
     * primitive type or an object type
     */
    public final Object getValue() {
	if (value == noVal)
	    value = computeValue();
	return value;
    }

    /**
     * Compute the constant value of this expression, if any
     *
     * @return the constant value (if any) of this expression, as a wrapped
     * primitive type or an object type
     */
    protected abstract Object computeValue();

    /**
     * Get the list of variables read and written by this expression
     *
     * @return the list of variables read and written by this expression
     */
    public abstract VarList getVarList();
}
