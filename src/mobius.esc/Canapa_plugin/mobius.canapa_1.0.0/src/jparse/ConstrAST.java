/*
 * @(#)$Id: ConstrAST.java,v 1.2 2004/04/02 05:48:47 james Exp $
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
 * An AST node that represents a constructor definition
 *
 * @version $Revision: 1.2 $, $Date: 2004/04/02 05:48:47 $
 * @author Jerry James
 */
public final class ConstrAST extends JavaAST
    implements Constructor, JavaTokenTypes {

    /**
     * The modifiers for this constructor
     */
    private final ModifierAST modifiers;

    /**
     * The names of the parameter for this constructor
     */
    private final ParameterAST[] paramNames;

    /**
     * The parameter types for this constructor
     */
    private Type[] paramTypes;

    /**
     * The names of the exception types thrown by this constructor
     */
    private final IdentifierAST[] exceptNames;

    /**
     * The checked exceptions this constructor might throw
     */
    private Type[] exceptions;

    /**
     * The body of the constructor
     */
    private final CompoundAST body;

    /**
     * Create a default constructor
     */
    ConstrAST() {
	modifiers = new ModifierAST(Modifier.PUBLIC);
	paramNames = new ParameterAST[0];
	exceptNames = new IdentifierAST[0];
	body = null;
    }

    /**
     * Create a new constructor AST
     *
     * @param mods the modifiers for this constructor
     * @param parameters the parameters for this constructor
     * @param exceptions the exceptions thrown by this constructor
     * @param block the body of the constructor
     */
    ConstrAST(final ModifierAST mods, final JavaAST parameters,
	      final JavaAST exceptions, final CompoundAST block) {
	setType(CTOR_DEF);
	modifiers = mods;

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

	// Get the exception type names; exceptions is a LITERAL_throws node
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
	
	// Set the body of the constructor
	body = block;

	// Register the constructor
	TypeAST.currType.addConstructor(this);
    }

    public void parseComplete() {
	context.isField = false;
	for (int i = 0; i < paramNames.length; i++) {
	    paramNames[i].parseComplete();
	}
	context.nextStmt = null;
	body.parseComplete();
	context.isField = true;
    }

    /**
     * Returns the <code>Type</code> object representing the class or
     * interface that declares the constructor represented by this object.
     *
     * @return the <code>Type</code> of the declaring class
     */
    public Type getDeclaringClass() {
	return typeAST.retrieveType();
    }

    /**
     * Returns the Java language modifiers for the constructor represented by
     * this object, as an integer.  The {@link java.lang.reflect.Modifier
     * Modifier} class should be used to decode the modifiers.
     *
     * @return the modifiers for this constructor
     */
    public int getModifiers() {
	return modifiers.mods;
    }

    /**
     * Get the formal parameters of this constructor
     *
     * @return an array containing the formal parameters
     */
    public ParameterAST[] getParameters() {
	return paramNames;
    }

    /**
     * Returns an array of <code>Type</code> objects that represent the formal
     * parameter types, in declaration order, of this constructor.  Returns an
     * array of length 0 if the underlying constructor takes no parameters.
     *
     * @return the parameter types of this constructor
     */
    public Type[] getParameterTypes() {
	if (paramTypes == null) {
	    int source;
	    if (typeAST.outer != null && !typeAST.modifiers.isStatic() &&
		!((SourceType)typeAST.retrieveType()).anonymous) {

		// Add the hidden first parameter for non-static inner classes
		paramTypes = new Type[paramNames.length + 1];
		paramTypes[0] = typeAST.outer.retrieveType();
		source = 1;
	    } else {
		paramTypes = new Type[paramNames.length];
		source = 0;
	    }
	    for (int i = 0; i < paramNames.length; i++, source++) {
		paramTypes[source] =
		    paramNames[i].getParamName().retrieveType();
	    }
	}
	return paramTypes;
    }

    /**
     * Get the checked exception types that might be thrown by this constructor
     *
     * @return an array of types representing the exceptions that this
     * constructor might throw
     */
    public final Type[] getExceptionTypes() {
	if (exceptions == null)
	    exceptions = computeExceptions();
	return exceptions;
    }

    /**
     * Returns an array of <code>Type</code> objects that represent the types
     * of the exceptions declared to be thrown by this constructor.  Returns
     * an array of length 0 if the constructor declares no exceptions in its
     * <code>throws</code> clause.
     *
     * @return the exceptions declared by this constructor
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

    /**
     * Get the code for the body of this constructor
     *
     * @return an AST node representing the body of the constructor
     */
    public CompoundAST getBody() {
	return body;
    }

    /**
     * Determines whether this constructor matches the parameters given by a
     * caller
     *
     * @param params the types of the parameters to the constructor
     * @param caller the type of the caller
     * @return <code>true</code> if this constructor matches,
     * <code>false</code> otherwise
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
		/*
		System.err.println("No, " + formalParams[i] + '(' +
				   formalParams[i].getClass() +
				   ") is not assignable from " + params[i] +
				   '(' + params[i].getClass() +
				   ") and they are " +
				   ((formalParams[i] == params[i])
				    ? "the same" : "different"));
		*/
		return false;
	    }
	}

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
     * Find the best match, given two matching constructors
     *
     * @param cons the other constructor to compare
     * @return either <var>this</var> or <var>cons</var>, depending on which
     * matches best, or <code>null</code> if neither matches best
     */
    public Constructor bestMatch(final Constructor cons) {
	// Since they both match, these arrays have equal length
	final Type[] parms1 = getParameterTypes();
	final Type[] parms2 = cons.getParameterTypes();

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

	// What's the answer?
	switch (comp) {
	case -1:
	    return this;
	case 1:
	    return cons;
	default:
	    return null;
	}
    }

    /**
     * Return a string describing this <code>ConstrAST</code>
     *
     * @return a string describing this <code>ConstrAST</code>
     */
    public String toString() {
	final StringBuffer buf = new StringBuffer(modifiers.toString());
	if (buf.length() != 0) {
	    buf.append(' ');
	}
	buf.append(typeAST.name);
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
