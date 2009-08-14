/*
 * @(#)$Id: CatchAST.java,v 1.2 2004/04/02 05:48:48 james Exp $
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

import antlr.Token;
import antlr.collections.AST;
import java.util.ArrayList;
import jparse.ModifierAST;
import jparse.Type;
import jparse.VarList;
import jparse.expr.TypeAST;
import jparse.expr.VarAST;

/**
 * An AST node that represents a catch clause
 *
 * @version $Revision: 1.2 $, $Date: 2004/04/02 05:48:48 $
 * @author Jerry James
 */
public final class CatchAST extends StatementAST {

    /**
     * The catch parameter
     */
    private VarAST param;

    /**
     * The catch body
     */
    private CompoundAST body;

    /**
     * Create a new catch clause AST
     *
     * @param token the token represented by this AST node
     */
    public CatchAST(final Token token) {
	super(token);
    }

    public void parseComplete() {
	super.parseComplete();
	final AST theParam = getFirstChild().getNextSibling();
	context.mods = (ModifierAST)theParam.getFirstChild();
	context.type = (TypeAST)context.mods.getNextSibling();
	param = (VarAST)context.type.getNextSibling();
	param.parseComplete();
	body = (CompoundAST)theParam.getNextSibling().getNextSibling();
	body.parseComplete();
    }

    protected Type[] computeExceptions() {
	return body.getExceptionTypes();
    }

    /**
     * Remove the exception caught by this catch clause from a list of
     * exceptions.  This will actually remove all subclasses of the exception
     * caught by this catch clause
     *
     * @param list the list of exceptions to modify
     * @return <var>list</var>, modified to remove any exceptions caught by
     * this catch clause
     */
    Type[] removeCaughtException(final Type[] list) {
	final Type theCatch = param.retrieveType();
	final ArrayList newList = new ArrayList();
	for (int i = 0; i < list.length; i++) {
	    if (!theCatch.isAssignableFrom(list[i])) {
		newList.add(list[i]);
	    }
	}
	final Type[] retList = new Type[newList.size()];
	newList.toArray(retList);
	return retList;
    }

    protected StatementAST[] computeControl() {
	return body.nextControlPoints();
    }

    public VarList getVarList() {
	return new VarList(body.getVarList(), param);
    }

    /**
     * Get the parameter to the catch clause
     *
     * @return the parameter
     */
    public VarAST getParameter() {
	return param;
    }

    /**
     * Get the body of the catch clause
     *
     * @return the body
     */
    public CompoundAST getBody() {
	return body;
    }
}
