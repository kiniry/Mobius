/*
 * @(#)$Id: DeclarationAST.java,v 1.2 2004/04/02 05:48:48 james Exp $
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
package jparse.stmt;

import antlr.collections.AST;
import java.util.ArrayList;
import jparse.JavaTokenTypes;
import jparse.ModifierAST;
import jparse.Type;
import jparse.VarList;
import jparse.expr.VarAST;
import jparse.expr.TypeAST;

/**
 * An AST node that represents a variable declaration statement
 *
 * @version $Revision: 1.2 $, $Date: 2004/04/02 05:48:48 $
 * @author Jerry James
 */
public final class DeclarationAST extends StatementAST
    implements JavaTokenTypes {

    /**
     * The modifiers for this declaration
     */
    private final ModifierAST modifiers;

    /**
     * The type for this declaration
     */
    private final TypeAST typeSpec;

    /**
     * The variables declared in this declaration
     */
    private final VarAST[] variables;

    /**
     * Create a new declaration statement AST
     *
     * @param mods the modifiers for this declaration
     * @param type the type for this declaration
     * @param vars the varaibles declared in this declaration
     */
    public DeclarationAST(final ModifierAST mods, final TypeAST type,
			  AST vars) {
	initialize(VARIABLE_DEFS, "VARIABLE_DEFS");
	modifiers = mods;
	typeSpec = type;

	// Collect the variable declarations
	final ArrayList list = new ArrayList();
	while (vars != null) {
	    list.add(vars.getFirstChild());
	    vars = vars.getNextSibling();	// Skip the comma
	    if (vars == null)
		break;
	    vars = vars.getNextSibling();
	}

	// Create the variables array
	variables = new VarAST[list.size()];
	list.toArray(variables);
    }

    public void parseComplete() {
	super.parseComplete();
	context.mods = modifiers;
	context.type = typeSpec;
	for (int i = 0; i < variables.length; i++) {
	    variables[i].parseComplete();
	}
    }

    protected Type[] computeExceptions() {
	Type[] exceptions = noTypes;
	for (int i = 0; i < variables.length; i++)
	    exceptions = Type.mergeTypeLists(exceptions,
					     variables[i].getExceptionTypes());
	return exceptions;
    }

    protected StatementAST[] computeControl() {
	return new StatementAST[] { next };
    }

    public VarList getVarList() {
	return new VarList(variables);
    }

    /**
     * Get the modifiers for this declaration
     *
     * @return the modifiers
     */
    public ModifierAST getModifiers() {
	return modifiers;
    }

    /**
     * Get the type name for this declaration
     *
     * @return the type name
     */
    public TypeAST getTypeName() {
	return typeSpec;
    }

    /**
     * Get the variables declared in this declaration
     *
     * @return an array of variables
     */
    public VarAST[] getVariables() {
	return variables;
    }
}
