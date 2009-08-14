/*
 * @(#)$Id: CompiledConstructor.java,v 1.2 2004/04/02 05:48:47 james Exp $
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
 * Information on a Java constructor defined in a Java class file
 *
 * @version $Revision: 1.2 $, $Date: 2004/04/02 05:48:47 $
 * @author Jerry James
 */
public final class CompiledConstructor implements Constructor {

    /**
     * The constructor object wrapped by this <code>CompiledConstructor</code>
     * object
     */
    private final java.lang.reflect.Constructor theConstructor;

    /**
     * Create a new <code>CompiledConstructor</code> object
     *
     * @param cons the <code>Constructor</code> object to wrap
     */
    CompiledConstructor(final java.lang.reflect.Constructor cons) {
	theConstructor = cons;
    }

    /**
     * Returns the <code>Type</code> object representing the class or
     * interface that declares the constructor represented by this object.
     *
     * @return the <code>Type</code> of the declaring class
     */
    public Type getDeclaringClass() {
	return Type.forClass(theConstructor.getDeclaringClass());
    }

    /**
     * Return the name of this constructor
     *
     * @return the name of this constructor
     */
    public String getName() {
	return theConstructor.getName();
    }

    /**
     * Returns the Java language modifiers for the constructor represented by
     * this object, as an integer.  The
     * {@link java.lang.reflect.Modifier Modifier} class should be used to
     * decode the modifiers.
     *
     * @return the modifiers for this constructor
     */
    public int getModifiers() {
	return theConstructor.getModifiers();
    }

    /**
     * Returns an array of <code>Type</code> objects that represent the formal
     * parameter types, in declaration order, of this constructor.  Returns an
     * array of length 0 if the underlying constructor takes no parameters.
     *
     * @return the parameter types of this constructor
     */
    public Type[] getParameterTypes() {
	final Class[] params = theConstructor.getParameterTypes();
	final Type[] paramTypes = new Type[params.length];
	for (int i = 0; i < params.length; i++)
	    paramTypes[i] = Type.forClass(params[i]);
	return paramTypes;
    }

    /**
     * Returns an array of <code>Type</code> objects that represent the types
     * of the exceptions declared to be thrown by this constructor.  Returns
     * an array of length 0 if the constructor declares no exceptions in its
     * <code>throws</code> clause.
     *
     * @return the exceptions declared by this constructor
     */
    public Type[] getExceptionTypes() {
	final Class[] except = theConstructor.getExceptionTypes();
	final Type[] exceptTypes = new Type[except.length];
	for (int i = 0; i < except.length; i++)
	    exceptTypes[i] = Type.forClass(except[i]);
	return exceptTypes;
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
     * Return a string describing this <code>CompiledConstructor</code>
     *
     * @return a string describing this <code>CompiledConstructor</code>
     */
    public String toString() {
	return theConstructor.toString();
    }
}
