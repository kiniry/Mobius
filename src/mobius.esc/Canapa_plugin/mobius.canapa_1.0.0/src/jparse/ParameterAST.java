/*
 * @(#)$Id: ParameterAST.java,v 1.2 2004/04/02 05:48:47 james Exp $
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

import jparse.expr.VarAST;

/**
 * An AST node that represents a formal parameter
 *
 * @version $Revision: 1.2 $, $Date: 2004/04/02 05:48:47 $
 * @author Jerry James
 */
public final class ParameterAST extends JavaAST implements JavaTokenTypes {

    /**
     * The modifiers for this parameter
     */
    private final ModifierAST mods;

    /**
     * The declared type of this parameter
     */
    private final jparse.expr.TypeAST typeAST;

    /**
     * The parameter name and trailing brackets
     */
    private final VarAST var;

    /**
     * Create a new parameter AST
     *
     * @param mod the modifiers for this parameter
     * @param type the type of this parameter
     * @param variable the parameter name and trailing brackets (if any)
     */
    public ParameterAST(final ModifierAST mod, final jparse.expr.TypeAST type,
			final VarAST variable) {
	setType(PARAMETER_DEF);
	mods = mod;
	typeAST = type;
	var = variable;
    }

    public void parseComplete() {
	context.mods = mods;
	context.type = typeAST;
	var.parseComplete();
    }

    /**
     * Get the modifiers for this variable
     *
     * @return the modifiers
     */
    public ModifierAST getModifiers() {
	return mods;
    }

    /**
     * Get the name of the declared type for this variable
     *
     * @return the type name
     */
    public jparse.expr.TypeAST getTypeName() {
	return typeAST;
    }

    /**
     * Get the parameter name and trailing brackets
     *
     * @return a variable declaration
     */
    public VarAST getParamName() {
	return var;
    }

    public String toString() {
	return var.toString();
    }
}
