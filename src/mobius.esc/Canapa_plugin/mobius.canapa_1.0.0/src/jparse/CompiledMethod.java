/*
 * @(#)$Id: CompiledMethod.java,v 1.2 2004/04/02 05:48:47 james Exp $
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

import java.lang.reflect.Modifier;

/**
 * Information on a Java method defined in a Java class file
 *
 * @version $Revision: 1.2 $, $Date: 2004/04/02 05:48:47 $
 * @author Jerry James
 */
public final class CompiledMethod implements Method {

    /**
     * The method object wrapped by this <code>CompiledMethod</code> object
     */
    private final java.lang.reflect.Method theMethod;

    /**
     * Create a new <code>CompiledMethod</code> object
     *
     * @param meth the <code>Method</code> object to wrap
     */
    CompiledMethod(final java.lang.reflect.Method meth) {
	theMethod = meth;
    }

    /**
     * Returns the <code>Type</code> object representing the class or
     * interface that declares the method represented by this object.
     *
     * @return the <code>Type</code> of the declaring class
     */
    public Type getDeclaringClass() {
	return Type.forClass(theMethod.getDeclaringClass());
    }

    /**
     * Return the name of this method
     *
     * @return the name of this method
     */
    public String getName() {
	return theMethod.getName();
    }

    /**
     * Returns the Java language modifiers for the method represented by this
     * object, as an integer.  The {@link java.lang.reflect.Modifier Modifier}
     * class should be used to decode the modifiers.
     *
     * @return the modifiers for this method
     */
    public int getModifiers() {
	return theMethod.getModifiers();
    }

    /**
     * Returns a <code>Type</code> object that represents the formal return
     * type of this method.
     *
     * @return the return type of this method
     */
    public Type getReturnType() {
	return Type.forClass(theMethod.getReturnType());
    }

    /**
     * Returns an array of <code>Type</code> objects that represent the formal
     * parameter types, in declaration order, of this method.  Returns an
     * array of length 0 if the underlying method takes no parameters.
     *
     * @return the parameter types of this method
     */
    public Type[] getParameterTypes() {
	final Class[] params = theMethod.getParameterTypes();
	final Type[] paramTypes = new Type[params.length];
	for (int i = 0; i < params.length; i++)
	    paramTypes[i] = Type.forClass(params[i]);
	return paramTypes;
    }

    public Type[] getExceptionTypes() {
	final Class[] except = theMethod.getExceptionTypes();
	final Type[] exceptTypes = new Type[except.length];
	for (int i = 0; i < except.length; i++)
	    exceptTypes[i] = Type.forClass(except[i]);
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
     * Determines whether this method matches the parameters given by a caller
     *
     * @param name the name of the method to match
     * @param params the types of the parameters to the method
     * @param caller the type of the caller
     * @return <code>true</code> if this method matches, <code>false</code>
     * otherwise
     */
    public boolean match(final String name, final Type[] params,
			 final Type caller) {
	return name.equals(theMethod.getName())
	    ? match(params, caller)
	    : false;
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
	if (Modifier.isAbstract(getModifiers()))
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
     * Return a string describing this <code>CompiledMethod</code>
     *
     * @return a string describing this <code>CompiledMethod</code>
     */
    public String toString() {
	return theMethod.toString();
    }
}
