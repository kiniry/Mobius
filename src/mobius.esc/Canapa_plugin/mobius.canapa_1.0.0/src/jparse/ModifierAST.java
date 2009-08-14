/*
 * @(#)$Id: ModifierAST.java,v 1.2 2004/04/02 05:48:47 james Exp $
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
 * An AST node that represents a (possibly empty) set of modifiers
 *
 * @version $Revision: 1.2 $, $Date: 2004/04/02 05:48:47 $
 * @author Jerry James
 */
public final class ModifierAST extends JavaAST implements JavaTokenTypes {

    /**
     * The modifier values represented by this modifier AST
     */
    int mods;

    /**
     * Create a new modifier AST node
     *
     * @param modBits the modifier bits
     */
    public ModifierAST(final int modBits) {
	super();
	initialize(MODIFIERS, "MODIFIERS");
	mods = modBits;
    }

    /**
     * Identify this set of modifiers as belonging to an interface
     */
    void setInterface() {
	mods |= Modifier.INTERFACE;
    }

    /**
     * Identify this as modifiers for an interface method
     */
    void setInterfaceMethod() {
	mods |= Modifier.PUBLIC | Modifier.ABSTRACT;
    }

    /**
     * Determine whether this set of modifiers includes the
     * <code>public</code> modifier
     *
     * @return <code>true</code> if <code>public</code> is included
     */
    public boolean isPublic() {
	return Modifier.isPublic(mods);
    }

    /**
     * Determine whether this set of modifiers includes the
     * <code>private</code> modifier
     *
     * @return <code>true</code> if <code>private</code> is included
     */
    public boolean isPrivate() {
	return Modifier.isPrivate(mods);
    }

    /**
     * Determine whether this set of modifiers includes the
     * <code>protected</code> modifier
     *
     * @return <code>true</code> if <code>protected</code> is included
     */
    public boolean isProtected() {
	return Modifier.isProtected(mods);
    }

    /**
     * Determine whether this set of modifiers includes the
     * <code>static</code> modifier
     *
     * @return <code>true</code> if <code>static</code> is included
     */
    public boolean isStatic() {
	return Modifier.isStatic(mods);
    }

    /**
     * Determine whether this set of modifiers includes the <code>final</code>
     * modifier
     *
     * @return <code>true</code> if <code>final</code> is included
     */
    public boolean isFinal() {
	return Modifier.isFinal(mods);
    }

    /**
     * Determine whether this set of modifiers includes the
     * <code>synchronized</code> modifier
     *
     * @return <code>true</code> if <code>synchronized</code> is included
     */
    public boolean isSynchronized() {
	return Modifier.isSynchronized(mods);
    }

    /**
     * Determine whether this set of modifiers includes the
     * <code>volatile</code> modifier
     *
     * @return <code>true</code> if <code>volatile</code> is included
     */
    public boolean isVolatile() {
	return Modifier.isVolatile(mods);
    }

    /**
     * Determine whether this set of modifiers includes the
     * <code>transient</code> modifier
     *
     * @return <code>true</code> if <code>transient</code> is included
     */
    public boolean isTransient() {
	return Modifier.isTransient(mods);
    }

    /**
     * Determine whether this set of modifiers includes the
     * <code>native</code> modifier
     *
     * @return <code>true</code> if <code>native</code> is included
     */
    public boolean isNative() {
	return Modifier.isNative(mods);
    }

    /**
     * Determine whether this set of modifiers includes the
     * <code>interface</code> modifier
     *
     * @return <code>true</code> if <code>interface</code> is included
     */
    public boolean isInterface() {
	return Modifier.isInterface(mods);
    }

    /**
     * Determine whether this set of modifiers includes the
     * <code>abstract</code> modifier
     *
     * @return <code>true</code> if <code>abstract</code> is included
     */
    public boolean isAbstract() {
	return Modifier.isAbstract(mods);
    }

    /**
     * Determine whether this set of modifiers includes the
     * <code>strictfp</code> modifier
     *
     * @return <code>true</code> if <code>strictfp</code> is included
     */
    public boolean isStrict() {
	return Modifier.isStrict(mods);
    }

    /**
     * Return a string representation of this set of modifiers
     *
     * @return a string representation of this set of modifiers
     */
    public String toString() {
	return Modifier.toString(mods);
    }
}
