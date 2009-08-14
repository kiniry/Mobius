/*
 * @(#)$Id: Constructor.java,v 1.2 2004/04/02 05:48:47 james Exp $
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

/**
 * Information on a Java constructor.
 *
 * @version $Revision: 1.2 $, $Date: 2004/04/02 05:48:47 $
 * @author Jerry James
 */
public interface Constructor extends HasExceptions {

    /**
     * Returns the <code>Type</code> object representing the class or
     * interface that declares the constructor represented by this object.
     *
     * @return the <code>Type</code> of the declaring class
     */
    public Type getDeclaringClass();

    /**
     * Returns the Java language modifiers for the constructor represented by
     * this object, as an integer.  The
     * {@link java.lang.reflect.Modifier Modifier} class should be used to
     * decode the modifiers.
     *
     * @return the modifiers for this constructor
     */
    public int getModifiers();

    /**
     * Returns an array of <code>Type</code> objects that represent the formal
     * parameter types, in declaration order, of this constructor.  Returns an
     * array of length 0 if the underlying constructor takes no parameters.
     *
     * @return the parameter types of this constructor
     */
    public Type[] getParameterTypes();

    /**
     * Determines whether this constructor matches the parameters given by a
     * caller
     *
     * @param params the types of the parameters to the constructor
     * @param caller the type of the caller
     * @return <code>true</code> if this constructor matches,
     * <code>false</code> otherwise
     */
    public boolean match(Type[] params, Type caller);

    /**
     * Find the best match, given two matching constructors
     *
     * @param cons the other constructor to compare
     * @return either <var>this</var> or <var>cons</var>, depending on which
     * matches best, or <code>null</code> if neither matches best
     */
    public Constructor bestMatch(Constructor cons);
}
