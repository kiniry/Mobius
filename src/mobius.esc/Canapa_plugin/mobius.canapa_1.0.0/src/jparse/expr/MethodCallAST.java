/*
 * @(#)$Id: MethodCallAST.java,v 1.3 2004/04/02 05:48:48 james Exp $
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
import antlr.collections.AST;
import jparse.*;

/**
 * An AST node that represents a method call
 *
 * @version $Revision: 1.3 $, $Date: 2004/04/02 05:48:48 $
 * @author Jerry James
 */
public final class MethodCallAST extends ExpressionAST
    implements JavaTokenTypes {

    /**
     * The object on which to call
     */
    private ExpressionAST object;

    /**
     * The name of the method to call
     */
    private IdentifierAST method;

    /**
     * The parameters of the call
     */
    private ListAST parameters;

    /**
     * The method that this call is calling (for method calls)
     */
    private Method theMethod;

    /**
     * The constructor that this call is calling (for constructor calls)
     */
    private Constructor theConstructor;

    /**
     * Create a new method call AST
     *
     * @param token the token represented by this AST node
     */
    public MethodCallAST(final Token token) {
	super(token);
	setType(METHOD_CALL);
    }

    /**
     * Set the method call values
     */
    public void parseComplete() {
	AST last, a, m;
	for (last = a = getFirstChild(); !(a instanceof ListAST);
	     a = a.getNextSibling())
	    last = a;
	for (m = last.getFirstChild(); m != null; m = m.getNextSibling())
	    last = m;
	method = (IdentifierAST)last;
	parameters = (ListAST)a;
	object = (ExpressionAST)getFirstChild();
	if (object == method) {
	    object = null;
	} else if (object.getType() == DOT) {
	    object = (ExpressionAST)object.getFirstChild();
	    object.parseComplete();
	}
	parameters.parseComplete();

	// Is this really a method call, or is it a constructor call?
	final String name = method.getName();
	if (name.equals("super") || name.equals("this")) {
	    setType(CONSTRUCTOR_CALL);
	}
    }

    protected Type computeType() {
	final String name = method.getName();
	final Type objType = (object != null)
	    ? object.retrieveType()
	    : (name.equals("super")
	       ? method.retrieveType()
	       : typeAST.retrieveType());	// Implicit "this"

	if (getType() == CONSTRUCTOR_CALL) {
	    theConstructor = objType.getConstructor(parameters.getTypes(),
						    typeAST.retrieveType());
	    return null;
	}

	// If we reach this point, it is a regular method call
	theMethod = objType.getMethod(name, parameters.getTypes(),
				      typeAST.retrieveType());
	/*
	if (theMethod == null) {
	    System.err.println("**** Couldn't find a method for " + toString()
			       + " with type " + objType + '(' +
			       objType.getClass() + ')');
	    System.err.println("Candidates are:");
	    final Method[] meths =
		objType.getMeths(name, parameters.getTypes(),
				 typeAST.retrieveType());
	    for (int i = 0; i < meths.length; i++)
		System.err.println(meths[i]);
	    System.err.println(symTable);
	}
	*/
	return theMethod.getReturnType();
    }

    protected Type[] computeExceptions() {
	// Getting exceptions from the method or constructor means we have to
	// do type evaluation first
	retrieveType();		// but we don't need the return value
	final Type[] evalExcepts = (object == null)
	    ? parameters.getExceptionTypes()
	    : Type.mergeTypeLists(object.getExceptionTypes(),
				  parameters.getExceptionTypes());
	return Type.mergeTypeLists(evalExcepts,
				   (theMethod == null)
				   ? theConstructor.getExceptionTypes()
				   : theMethod.getExceptionTypes());
    }

    protected Object computeValue() {
	return nonconstant;
    }

    public VarList getVarList() {
	return (object == null)
	    ? parameters.getVarList()
	    : new VarList(object.getVarList(), parameters.getVarList());
    }

    /**
     * Get the object on which the method call will be made
     *
     * @return the object, or <code>null</code> if none was specified
     */
    public ExpressionAST getObject() {
	return object;
    }

    /**
     * Get the name of the method to call
     *
     * @return an identifier naming the method to call
     */
    public IdentifierAST getMethodName() {
	return method;
    }

    /**
     * Get the parameters to the method
     *
     * @return an expression containing the list of parameters
     */
    public ListAST getParameters() {
	return parameters;
    }

    /**
     * Get the method that will actually be called
     *
     * @return a <code>Method</code> object representing the method to call
     */
    public Method getMethod() {
	retrieveType();
	return theMethod;
    }

    /**
     * Get the constructor that will actually be called
     *
     * @return a <code>Constructor</code> object representing the constructor
     * to run
     */
    public Constructor getConstructor() {
	retrieveType();
	return theConstructor;
    }

    public String toString() {
	final StringBuffer buf = new StringBuffer();
	if (object != null) {
	    buf.append(object.toString());
	    buf.append('.');
	}
	buf.append(method.getName());
	buf.append('(');
	buf.append(parameters.toString());
	buf.append(')');
	return buf.toString();
    }
}
