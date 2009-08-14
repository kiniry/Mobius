/*
 * @(#)$Id: StatementAST.java,v 1.2 2004/04/02 05:48:48 james Exp $
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
import jparse.HasExceptions;
import jparse.JavaAST;
import jparse.Type;
import jparse.VarList;

/**
 * An AST node that represents a statement
 *
 * @version $Revision: 1.2 $, $Date: 2004/04/02 05:48:48 $
 * @author Jerry James
 */
public abstract class StatementAST extends JavaAST implements HasExceptions {

    /**
     * A special member of the <code>StatementAST</code> class which is used
     * to indicate that control passes out of the current method due to a
     * <code>throw</code> or <code>return</code>.
     */
    public static final StatementAST nonlocal = new CaseGroupAST();
    // There is no significance to this being a CaseGroupAST.  That is just a
    // StatementAST with a no-args constructor.

    /**
     * The checked exceptions this statement might throw
     */
    protected Type[] exceptions;

    /**
     * The next statement in a sequential list of statements
     */
    protected StatementAST next;

    /**
     * The points to which control might flow from this statement
     */
    protected StatementAST[] control;

    /**
     * Create a new statement AST
     */
    protected StatementAST() {
	super();
    }

    /**
     * Create a new statement AST
     *
     * @param token the token represented by this AST node
     */
    protected StatementAST(final Token token) {
	super(token);
    }

    public void parseComplete() {
	// Set the "next" pointer
	next = context.nextStmt;
    }

    /**
     * Get the checked exception types that might be thrown by this statement
     *
     * @return an array of types representing the exceptions that this
     * statement might throw
     */
    public final Type[] getExceptionTypes() {
	if (exceptions == null)
	    exceptions = computeExceptions();
	return exceptions;
    }

    /**
     * Compute the checked exception types that might be thrown by this
     * statement
     *
     * @return an array of types representing the exceptions that this
     * statement might throw
     */
    protected abstract Type[] computeExceptions();

    /**
     * Get the list of points to which control might pass after executing this
     * statement.  This may include <code>StatementAST.nonlocal</code> if the
     * statement returns or throws something.
     *
     * @return a list of statements to which control might pass from this one
     */
    public StatementAST[] nextControlPoints() {
	if (control == null)
	    control = computeControl();
	return control;
    }

    /**
     * Compute the list of points to which control might flow after this
     * statement
     *
     * @return a list of statements to which control might pass from this one
     */
    protected abstract StatementAST[] computeControl();

    /**
     * Get the list of variables read, written, and declared by this statement
     *
     * @return the list of variables read, written, and declared by this
     * statement
     */
    public abstract VarList getVarList();
}
