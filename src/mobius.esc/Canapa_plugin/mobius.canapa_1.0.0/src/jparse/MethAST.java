/*
 * @(#)$Id: MethAST.java,v 1.2 2004/04/02 05:48:47 james Exp $
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

import antlr.Token;
import antlr.collections.AST;
import java.lang.reflect.Modifier;
import java.util.ArrayList;
import jparse.JavaTokenTypes;
import jparse.expr.IdentifierAST;
import jparse.expr.VarAST;
import jparse.stmt.CompoundAST;

/**
 * An AST node that represents a method definition
 *
 * @version $Revision: 1.2 $, $Date: 2004/04/02 05:48:47 $
 * @author Jerry James
 */
public final class MethAST extends JavaAST implements JavaTokenTypes, Method {

    /**
     * The modifiers for this method
     */
    private final ModifierAST modifiers;

    /**
     * The name of the return type for this method
     */
    private final jparse.expr.TypeAST returnName;

    /**
     * Any brackets to add onto the return type
     */
    private final JavaAST returnBrackets;

    /**
     * The return type for this method
     */
    private Type returnType;

    /**
     * The name of the method
     */
    private IdentifierAST methodName;

    /**
     * The names of the parameters for this method
     */
    private final ParameterAST[] paramNames;

    /**
     * The parameter types for this method
     */
    private Type[] paramTypes;

    /**
     * The names of the exception types thrown by this method
     */
    private final IdentifierAST[] exceptNames;

    /**
     * The checked exceptions this method might throw
     */
    private Type[] exceptions;

    /**
     * The body of the method
     */
    private final CompoundAST body;

    /**
     * Create a new method AST
     *
     * @param mods the modifiers for this method
     * @param retType the return type of the method
     * @param name the name of the method
     * @param parameters the parameters for this method
     * @param brackets any brackets that modify the return type
     * @param exceptions the exceptions thrown by this method
     * @param block the body of the method
     */
    MethAST(final ModifierAST mods, final jparse.expr.TypeAST retType,
	    final IdentifierAST name, final JavaAST parameters, 
	    final JavaAST brackets, final JavaAST exceptions,
	    final CompoundAST block) {
	setType(METHOD_DEF);
	modifiers = mods;
	returnName = retType;
	methodName = name;

	// Get the parameter type names; parameters is a PARAMETERS node with
	// a possibly empty list of PARAMETER_DEFs as its children.
	final ArrayList pTypes = new ArrayList();
	for (AST p = parameters.getFirstChild(); p != null;
	     p = p.getNextSibling()) {
	    pTypes.add(p);
	    p = p.getNextSibling();  // Skip the comma
	    if (p == null) {
		break;
	    }
	}
	paramNames = new ParameterAST[pTypes.size()];
	pTypes.toArray(paramNames);

	// Record the declarator brackets
	returnBrackets = brackets;

	// Get the exception type names; exception is a LITERAL_throws node
	// with at least one identifier child
	if (exceptions != null) {
	    final ArrayList eTypes = new ArrayList();
	    for (AST e = exceptions.getFirstChild(); e != null;
		 e = e.getNextSibling()) {
		eTypes.add(e);
		e = e.getNextSibling();  // Skip the comma
		if (e == null)
		    break;
	    }
	    exceptNames = new IdentifierAST[eTypes.size()];
	    eTypes.toArray(exceptNames);
	} else {
	    exceptNames = new IdentifierAST[0];
	}
	
	// Set the body of the method
	body = block;

	// Register the method
	symTable.addMeth(this);
    }

    public void parseComplete() {
	context.isField = false;
	for (int i = 0; i < paramNames.length; i++) {
	    paramNames[i].parseComplete();
	}
	if (body != null) {
	    context.nextStmt = null;
	    body.parseComplete();
	}
	context.isField = true;
    }

    /**
     * Returns the <code>Type</code> object representing the class or
     * interface that declares the method represented by this object.
     *
     * @return the <code>Type</code> of the declaring class
     */
    public Type getDeclaringClass() {
	return typeAST.retrieveType();
    }

    /**
     * Returns the name of the method represented by this <code>MethAST</code>
     * object, as a <code>String</code>.
     *
     * @return the name of this method
     */
    public String getName() {
	return methodName.getName();
    }

    /**
     * Returns the Java language modifiers for the method represented by this
     * object, as an integer.  The {@link java.lang.reflect.Modifier Modifier}
     * class should be used to decode the modifiers.
     *
     * @return the modifiers for this method
     */
    public int getModifiers() {
	return modifiers.mods;
    }

    /**
     * Returns a <code>Type</code> object that represents the formal return
     * type of this method.
     *
     * @return the return type of this method
     */
    public Type getReturnType() {
	if (returnType == null) {
	    if (returnBrackets == null) {
		returnType = returnName.retrieveType();
	    } else {
		final StringBuffer buf =
		    new StringBuffer(returnName.getName());
		for (AST b = returnBrackets;
		     b != null && b.getType() == ARRAY_DECLARATOR;
		     b = b.getNextSibling().getNextSibling())
		    buf.append("[]");
		try {
		    returnType = Type.forName(buf.toString());
		} catch (ClassNotFoundException classEx) {
		}
	    }
	}
	return returnType;
    }

    /**
     * Get the formal parameters of this method
     *
     * @return an array containing the formal parameters
     */
    public ParameterAST[] getParameters() {
	return paramNames;
    }

    /**
     * Returns an array of <code>Type</code> objects that represent the formal
     * parameter types, in declaration order, of this method.  Returns an
     * array of length 0 if the underlying method takes no parameters.
     *
     * @return the parameter types of this method
     */
    public Type[] getParameterTypes() {
	if (paramTypes == null) {
	    paramTypes = new Type[paramNames.length];
	    for (int i = 0; i < paramNames.length; i++) {
		paramTypes[i] = paramNames[i].getParamName().retrieveType();
	    }
	}
	return paramTypes;
    }

    public final Type[] getExceptionTypes() {
	if (exceptions == null)
	    exceptions = computeExceptions();
	return exceptions;
    }

    /**
     * Returns an array of <code>Type</code> objects that represent the types
     * of the exceptions declared to be thrown by this method.  Returns an
     * array of length 0 if the method declares no exceptions in its
     * <code>throws</code> clause.
     *
     * @return the exceptions declared by this method
     */
    protected Type[] computeExceptions() {
	final Type[] exceptTypes = new Type[exceptNames.length];
	for (int i = 0; i < exceptNames.length; i++) {
	    try {
		exceptTypes[i] = topLevel.getType(exceptNames[i].getName());
	    } catch (ClassNotFoundException classEx) {
	    }
	}
	return exceptTypes;
    }

    public boolean isAccessible(final Type caller) {
	// Is it public?
	final int mod = getModifiers();
	if (Modifier.isPublic(mod)) {
	    return true;
	}

	// Is it protected?
	final Type myType = getDeclaringClass();
	if (Modifier.isProtected(mod)) {
	    return myType.getPackage().equals(caller.getPackage()) ||
		myType.superClassOf(caller);
	}

	// Is it private?
	if (Modifier.isPrivate(mod)) {
	    // Is caller equal to or an inner class of myType?
	    for (Type t = caller; t != null; t = t.getDeclaringClass()) {
		if (t == myType) {
		    return true;
		}
	    }
	    return false;
	}

	// It must have package visibility
	return myType.getPackage().equals(caller.getPackage());
    }

    /**
     * Get the code for the body of this method
     *
     * @return an AST node representing the body of the method
     */
    public CompoundAST getBody() {
	return body;
    }

    /**
     * Determines whether this method matches the parameters given by a caller
     *
     * @param methName the name of the method to match
     * @param params the types of the parameters to the method
     * @param caller the type of the caller
     * @return <code>true</code> if this method matches, <code>false</code>
     * otherwise
     */
    public boolean match(final String methName, final Type[] params,
			 final Type caller) {
	return getName().equals(methName) ? match(params, caller) : false;
    }

    /**
     * Determines whether this method matches the parameters given by a caller
     *
     * @param params the types of the parameters to the method
     * @param caller the type of the caller
     * @return <code>true</code> if this method matches, <code>false</code>
     * otherwise
     */
    public boolean match(final Type[] params, final Type caller) {
	// Does the number of parameters match?
	final Type[] formalParams = getParameterTypes();
	if (params.length != formalParams.length) {
	    return false;
	}

	// Do the types of the parameters match?
	for (int i = 0; i < params.length; i++) {
	    if (!formalParams[i].isAssignableFrom(params[i])) {
		return false;
	    }
	}

	// They match, so report a match iff it is accessible
	return isAccessible(caller);
    }

    /**
     * Find the best match, given two matching methods
     *
     * @param meth the other method to compare
     * @return either <var>this</var> or <var>meth</var>, depending on which
     * matches best, or <code>null</code> if neither matches best
     */
    public Method bestMatch(final Method meth) {
	// Since they both match, these arrays have equal length
	final Type[] parms1 = getParameterTypes();
	final Type[] parms2 = meth.getParameterTypes();

	// The variable comp is zero if I can't tell the difference between
	// them, -1 if I'm better, and 1 if the parameter is better
	int comp = 0;
	for (int i = 0; i < parms1.length; i++) {
	    final boolean assignToMe  = parms1[i].isAssignableFrom(parms2[i]);
	    final boolean assignOther = parms2[i].isAssignableFrom(parms1[i]);
	    if (assignToMe && !assignOther) {
		if (comp == -1)
		    return null;
		comp = 1;
	    } else if (!assignToMe && assignOther) {
		if (comp == 1)
		    return null;
		comp = -1;
	    }
	}

	// See if we got an answer
	if (comp == -1)
	    return this;
	if (comp == 1)
	    return meth;

	// See if one method overrides the other
	boolean sameParms = true;
	for (int i = 0; i < parms1.length; i++) {
	    if (parms1[i] != parms2[i])
		sameParms = false;
	}
	if (sameParms) {
	    final Type type1 = getDeclaringClass();
	    final Type type2 = meth.getDeclaringClass();
	    if (type1.isAssignableFrom(type2))
		return meth;
	    else if (type2.isAssignableFrom(type1))
		return this;
	}

	// See if one has a more specific return type
	final Type retType1 = getReturnType();
	final Type retType2 = meth.getReturnType();
	if (retType1.isAssignableFrom(retType2))
	    return meth;
	else if (retType2.isAssignableFrom(retType1))
	    return this;

	// They are exactly the same.  That's okay if at least one is abstract
	// (which also happens if it is from an interface)
	if (modifiers.isAbstract())
	    return meth;
	if (Modifier.isAbstract(meth.getModifiers()))
	    return this;

	// I give up!
	return null;
    }

    public boolean exactMatch(Method meth) {
	// Do they have the same name?
	if (!getName().equals(meth.getName())) {
	    return false;
	}

	// Do they have the same number of parameters?
	final Type[] myParams = getParameterTypes();
	final Type[] methParams = meth.getParameterTypes();
	if (myParams.length != methParams.length) {
	    return false;
	}

	// Do they have precisely the same parameter types?
	for (int i = 0; i < myParams.length; i++) {
	    if (myParams[i] != methParams[i]) {
		return false;
	    }
	}

	return true;
    }

    /**
     * Compares this method with another for order, where the order is based
     * on the method names
     *
     * @param meth the <code>MethAST</code> to compare with this one
     * @return a negative integer, zero, or a positive integer as this object
     * is less than, equal to, or greater than the specified
     * <code>MethAST</code>
     */
    public int compareTo(final MethAST meth) {
	return methodName.compareTo(meth.methodName);
    }

    /**
     * Return a string describing this <code>MethAST</code>
     *
     * @return a string describing this <code>MethAST</code>
     */
    public String toString() {
	final StringBuffer buf = new StringBuffer();
	final int mods = getModifiers();
	if (mods != 0) {
	    buf.append(Modifier.toString(mods));
	    buf.append(' ');
	}
	buf.append(getReturnType().getName());
	buf.append(' ');
	buf.append(typeAST.name);
	buf.append('.');
	buf.append(getName());
	buf.append('(');
	final Type[] params = getParameterTypes();
	if (params.length > 0) {
	    for (int i = 0; i < params.length - 1; i++) {
		buf.append(params[i].getName());
		buf.append(',');
	    }
	    buf.append(params[params.length - 1].getName());
	}
	buf.append(')');
	final Type[] exceptions = getExceptionTypes();
	if (exceptions.length > 0) {
	    buf.append(" throws ");
	    for (int i = 0; i < exceptions.length - 1; i++) {
		buf.append(exceptions[i].getName());
		buf.append(',');
	    }
	    buf.append(exceptions[exceptions.length - 1].getName());
	}
	return buf.toString();
    }
}
