/*
 * @(#)$Id: CompiledType.java,v 1.2 2004/04/02 05:48:47 james Exp $
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

import java.io.Serializable;
import java.lang.reflect.Array;
import java.lang.reflect.Modifier;
import java.util.ArrayList;

/**
 * Information on a Java type defined in a Java class file.
 *
 * @version $Revision: 1.2 $, $Date: 2004/04/02 05:48:47 $
 * @author Jerry James
 */
public final class CompiledType extends Type {

    /**
     * The class object wrapped by this <code>CompiledType</code> object
     */
    private final Class theClass;

    /**
     * The constructor objects in this class, in no particular order
     */
    private final CompiledConstructor[] constrs;

    /**
     * The method objects in this class, in no particular order
     */
    private final CompiledMethod[] meths;

    /**
     * The inner classes and interfaces of this class, in no particular order
     */
    private Type[] inner;

    /**
     * Create a new <code>CompiledType</code> object
     *
     * @param cls the <code>Class</code> object to wrap
     */
    CompiledType(final Class cls) {
	theClass = cls;

	// Look up all the constructors
	final java.lang.reflect.Constructor[] realConstrs =
	    cls.getDeclaredConstructors();
	constrs = new CompiledConstructor[realConstrs.length];
	for (int i = 0; i < realConstrs.length; i++)
	    constrs[i] = new CompiledConstructor(realConstrs[i]);

	// Look up all the methods
	final java.lang.reflect.Method[] realMeths = cls.getDeclaredMethods();
	meths = new CompiledMethod[realMeths.length];
	for (int i = 0; i < realMeths.length; i++)
	    meths[i] = new CompiledMethod(realMeths[i]);
    }

    /**
     * Create a new <code>CompiledType</code> object by modifying the
     * dimension of another <code>CompiledType</code> object
     *
     * @param original the original <code>CompiledType</code> object
     * @param dims the dimension of the array type
     */
    CompiledType(final CompiledType original, final int dims) {
	// This is stupid.  We wouldn't have to do this if Class.forName could
	// actually look up primitive types!  Vote for JDC bug #4171142, since
	// Sun has closed more relevant bug reports as not being bugs!
	Class cls = original.theClass;
	for (int i = 0; i < dims; i++)
	    cls = Array.newInstance(cls, 1).getClass();
	theClass = cls;
	constrs = new CompiledConstructor[0];
	meths = new CompiledMethod[0];
	inner = new Type[0];
    }

    public boolean isAssignableFrom(final Type type) {
	// Case 1: The types are exactly equivalent
	if (this == type)
	    return true;

	// Case 2: The parameter is null.  This means that the Java keyword
	// null was used in the source.  So we return true if this type is not
	// primitive.
	if (type == null)
	    return !theClass.isPrimitive();

	// Case 3: Both are primitive types.  Then Class won't give us the
	// right answer, so we have to do the hard work ourselves.
	if (type.isPrimitive() && theClass.isPrimitive()) {
	    final Class tClass = ((CompiledType)type).theClass;
	    if (theClass == void.class || tClass == void.class)
		return false;	// Can't assign those suckers!
	    if (theClass == double.class)
		return true;
	    if (theClass == float.class)
		return tClass != double.class;
	    if (theClass == long.class)
		return tClass != double.class && tClass != float.class;
	    if (theClass == int.class)
		return tClass != double.class && tClass != float.class &&
		    tClass != long.class;
	    if (theClass == short.class)
		return tClass == byte.class || tClass == short.class;
	    if (theClass == char.class)
		return tClass == byte.class || tClass == char.class;
	    // byte.class is the only one left!
	    return tClass == byte.class;
	}

	// Case 4: The parameter is also a compiled type.  Then let Class do
	// the hard work for us.
	if (type instanceof CompiledType)
	    return theClass.isAssignableFrom(((CompiledType)type).theClass);

	// Case 5: This is a primitive type.  Since the parameter is *not* a
	// compiled type (see case 3), then it is not a primitive type.
	if (theClass.isPrimitive())
	    return false;

	// Case 6: The parameter is an array type.  Then this must represent
	// an array with the same dimension and the same type or a supertype,
	// OR one of java.lang.Object, java.lang.Cloneable, or
	// java.io.Serializable.
	if (type.isArray()) {
	    return (theClass.isArray())
		? getComponentType().isAssignableFrom(type.getComponentType())
		: theClass == Object.class || theClass == Cloneable.class ||
		  theClass == Serializable.class;
	}

	// Case 7: This is an interface.
	if (isInterface()) {
	    return type.isInterface()
		// Case 7a: Type is also an interface.  Check whether this is
		// a superinterface of type.
		? superInterfaceOf(type)

		// Case 7b: Type is not an interface.  Check whether it, or
		// any of its parents, implement this interface
		: type.implementsInterface(this);
	}

	// Case 8: Check whether type is a subclass (or subinterface) of this
	// type
	return superClassOf(type);
    }

    public boolean isInterface() {
	return theClass.isInterface();
    }

    public boolean isArray() {
	return theClass.isArray();
    }

    public boolean isPrimitive() {
	return theClass.isPrimitive();
    }

    public boolean isInner() {
	return theClass.getDeclaringClass() != null;
    }

    public String getName() {
	return demangle(theClass.getName());
    }

    public Type getSuperclass() throws ClassNotFoundException {
	final Class superClass = theClass.getSuperclass();
	return (superClass == null) ? null : forClass(superClass);
    }

    public String getPackage() {
	// The getPackage() method of java.lang.Class sometimes returns null,
	// so we do it the hard way instead of like this:
	// return theClass.getPackage().getName();
	final String name = getName();
	final int index = name.lastIndexOf('.');
	return (index < 0) ? "" : name.substring(0, index);
    }

    public Type[] getInterfaces() {
	final Class[] interfaces = theClass.getInterfaces();
	final Type[] interTypes = new Type[interfaces.length];
	try {
	    for (int i = 0; i < interfaces.length; i++)
		interTypes[i] = forName(interfaces[i].getName());
	} catch (ClassNotFoundException classEx) {
	    System.err.println("This can't happen!  I could not find a class that the JDK has a reference to!");
	    classEx.printStackTrace();
	}
	return interTypes;
    }

    public Type getComponentType() {
	final Class compClass = theClass.getComponentType();
	return (compClass == null) ? null : forClass(compClass);
    }

    public int getModifiers() {
	return theClass.getModifiers();
    }

    public Type getDeclaringClass() {
	return forClass(theClass.getDeclaringClass());
    }

    public Type[] getClasses() {
	if (inner == null) {
	    Type[] parentTypes;
	    try {
		final Type parent = getSuperclass();
		parentTypes = parent.getClasses();
	    } catch (ClassNotFoundException classEx) {
		parentTypes = new Type[0];
	    } catch (NullPointerException nullEx) {
		parentTypes = new Type[0];
	    }
	    final Class[] myInner = theClass.getDeclaredClasses();
	    inner = new Type[parentTypes.length + myInner.length];
	    for (int i = 0; i < myInner.length; i++) {
		inner[i] = forClass(myInner[i]);
	    }
	    System.arraycopy(parentTypes, 0, inner, myInner.length,
			     parentTypes.length);
	}
	return inner;
    }

    public Method[] getMethods() {
	// Should we bother?
	if (isPrimitive() || isArray()) {
	    return new Method[0];
	}

	// All of the methods go here
	final ArrayList methods = new ArrayList();

	// Get the superclass methods
	try {
	    final Type parent = getSuperclass();
	    final Method[] parentMeths = parent.getMethods();
	    for (int i = 0; i < meths.length; i++) {
		methods.add(parentMeths[i]);
	    }
	} catch (ClassNotFoundException classEx) {
	    // Don't know what this means, but don't bomb out just yet.
	} catch (NullPointerException nullEx) {
	    // This is java.lang.Object (we hope).  Don't do anything.
	}

	// Add the methods declared in this class, overwriting those it
	// overrides
	outer:
	for (int i = 0; i < meths.length; i++) {
	    for (int j = 0; j < methods.size(); j++) {
		if (meths[i].exactMatch((Method)methods.get(j))) {
		    methods.set(j, meths[i]);
		    continue outer;
		}
	    }
	    methods.add(meths[i]);
	}

	// Add abstract methods declared in interfaces, if not implemented in
	// this type.  That means we only have to do this if this type is
	// abstract or an interface, since otherwise it won't compile!  If
	// anything overrides an interface method, just forget it.
	final int mods = getModifiers();
	if (Modifier.isAbstract(mods) || Modifier.isInterface(mods)) {
	    final Type[] interfaces = getInterfaces();
	    for (int i = 0; i < interfaces.length; i++) {
		final Method[] interMeths = interfaces[i].getMethods();
		outer2:
		for (int j = 0; j < interMeths.length; j++) {
		    for (int k = 0; k < methods.size(); k++) {
			if (interMeths[j].exactMatch((Method)methods.get(k))) {
			    continue outer2;
			}
		    }
		    methods.add(interMeths[j]);
		}
	    }
	}

	// We have the whole list, so return it
	final Method[] retMeths = new Method[methods.size()];
	methods.toArray(retMeths);
	return retMeths;
    }

    public Method getMethod(final String methName, final Type[] paramTypes,
			    final Type caller) {
	// Get all matching methods
	Method[] matches = getMeths(methName, paramTypes, caller);

	// If we didn't get a match...
	if (matches.length == 0) {
	    if (isInterface()) {
		// ... then check java.lang.Object for interfaces
		matches = Type.objectType.getMeths(methName, paramTypes,
						   caller);
	    } else {
		// ... or implemented interfaces for classes
		final Type[] interfaces = getInterfaces();
		for (int i = 0; i < interfaces.length; i++) {
		    final Method[] iMatches =
			interfaces[i].getMeths(methName, paramTypes, caller);
		    if (iMatches.length > 0) {
			final Method[] all =
			    new Method[matches.length + iMatches.length];
			System.arraycopy(matches, 0, all, 0, matches.length);
			System.arraycopy(iMatches, 0, all, matches.length,
					 iMatches.length);
			matches = all;
		    }
		}
	    }
	}

	// Did we get a match?
	if (matches.length == 0) {
	    getMeths(methName, paramTypes, caller);
	    return null;
	}

	// Pick the best match
	Method bestMatch = matches[0];
	boolean needBetter = false;
	for (int i = 1; i < matches.length; i++) {
	    Method newMatch = bestMatch.bestMatch(matches[i]);
	    needBetter = newMatch == null;
	    if (newMatch != null)
		bestMatch = newMatch;
	}
	if (needBetter) {
	    System.err.println("There was no best match!\nContenders are:");
	    for (int i = 0; i < matches.length; i++) {
		System.err.println(matches[i].toString());
	    }
	}
	return bestMatch;
    }

    public Constructor getConstructor(final Type[] params, final Type caller) {
	Constructor best = null;
	for (int i = 0; i < constrs.length; i++) {
	    final Constructor c = constrs[i];
	    if (c.match(params, caller)) {
		best = (best == null) ? c : best.bestMatch(c);
	    }
	}
	if (best == null && isInner()) {
	    // Is it an anonymous class?
	    final String fullName = getName();
	    final String name =
		fullName.substring(fullName.lastIndexOf('$') + 1);
	    try {
		int anonNumber = Integer.parseInt(name);
		best = getSuperclass().getConstructor(params, caller);
	    } catch (NumberFormatException numberEx) {
		// It wasn't an anonymous class
	    } catch (ClassNotFoundException classEx) {
	    }
	}
	return best;
    }

    public Type getInner(final String name) {
	final Type[] inner = getClasses();
	for (int i = 0; i < inner.length; i++) {
	    if (inner[i].getName().endsWith(name)) {
		return inner[i];
	    }
	}
	return null;
    }

    public Type getArrayType() {
	return forClass(Array.newInstance(theClass, 1).getClass());
    }

    public Type varType(final String varName) {
	// See if it is defined in this class
	try {
	    return forClass(theClass.getDeclaredField(varName).getType());
	} catch (Exception ex) {
	}

	// See if it is defined in a superclass
	try {
	    final Type parent = getSuperclass();
	    if (parent != null) {
		final Type type = parent.varType(varName);
		if (type != null)
		    return type;
	    }
	} catch (ClassNotFoundException classEx) {
	}
	
	// See if it is defined in an interface
	final Type[] interfaces = getInterfaces();
	for (int i = 0; i < interfaces.length; i++) {
	    final Type type = interfaces[i].varType(varName);
	    if (type != null)
		return type;
	}

	// Can't find it
	return null;
    }

    public Method[] getMeths(final String name, final Type[] params,
			     final Type caller) {
	// Get any matches from the superclass or superinterfaces
	Method[] matches;
	if (isInterface()) {
	    matches = new Method[0];
	    final Type[] superInts = getInterfaces();
	    for (int i = 0; i < superInts.length; i++) {
		final Method[] iMatches =
		    superInts[i].getMeths(name, params, this);
		if (iMatches.length > 0) {
		    final Method[] all =
			new Method[matches.length + iMatches.length];
		    System.arraycopy(matches, 0, all, 0, matches.length);
		    System.arraycopy(iMatches, 0, all, matches.length,
				     iMatches.length);
		    matches = all;
		}
	    }
	} else {
	    try {
		matches = getSuperclass().getMeths(name, params, caller);
	    } catch (ClassNotFoundException classEx) {
		// Just leave the list of matches empty
		matches = new Method[0];
	    } catch (NullPointerException nullEx) {
		// Likewise ... this happens for java.lang.Object ONLY
		matches = new Method[0];
	    }
	}

	// Add matches from this class
	final ArrayList res = new ArrayList();
	for (int i = 0; i < meths.length; i++) {
	    if (meths[i].match(name, params, caller))
		res.add(meths[i]);
	}
	final int size = res.size();
	if (size > 0) {
	    final Method[] newMatches = new Method[matches.length + size];
	    res.toArray(newMatches);
	    System.arraycopy(matches, 0, newMatches, size, matches.length);
	    matches = newMatches;
	}

	// If there are no matches yet, add matches from any enclosing class
	if (matches.length == 0) {
	    final Type outer = getDeclaringClass();
	    if (outer != null) {
		final Method[] outerMatches =
		    outer.getMeths(name, params, caller);
		if (outerMatches.length > 0) {
		    final Method[] newMatches =
			new Method[matches.length + outerMatches.length];
		    System.arraycopy(matches, 0, newMatches, 0,
				     matches.length);
		    System.arraycopy(outerMatches, 0, newMatches,
				     matches.length, outerMatches.length);
		    matches = newMatches;
		}
	    }
	}

	return matches;
    }

    public String toString() {
	return theClass.toString();
    }

    public void dump() {
	final StringBuffer buf = new StringBuffer(theClass.toString());
	buf.append(':');
	try {
	    final Type parent = getSuperclass();
	    buf.append("\n  Superclass = ");
	    buf.append(parent);
	} catch (ClassNotFoundException classEx) {
	}
	final Type outer = getDeclaringClass();
	buf.append("\n  Outer class = ");
	buf.append(outer);
	buf.append("\n  Constructors:\n");
	for (int i = 0; i < constrs.length; i++) {
	    buf.append(constrs[i].toString());
	    buf.append('\n');
	}
	System.err.println(buf.toString());
    }
}
