/*
 * @(#)$Id: CompileContext.java,v 1.2 2004/04/02 05:48:47 james Exp $
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

import java.util.LinkedList;
import jparse.stmt.StatementAST;

/**
 * Information about the compilation context so that individual AST nodes can
 * set up needed values
 *
 * @version $Revision: 1.2 $, $Date: 2004/04/02 05:48:47 $
 * @author Jerry James
 */
public final class CompileContext {

    /**
     * Whether the current construct is a field (top-level construct in a
     * class), or not.  This is used to distinguish local variables from
     * static and instance variables.
     */
    public boolean isField = true;

    /**
     * The next statement in sequence after the current one
     */
    public StatementAST nextStmt;

    /**
     * The current modifiers
     */
    public ModifierAST mods;

    /**
     * The current variable or array base type
     */
    public jparse.expr.TypeAST type;

    /**
     * The current sign of a number being read, <code>true</code> for negative
     * or <code>false</code> for positive.  This is necessary to avoid a
     * {@link java.lang.NumberFormatException NumberFormatException} when
     * reading in the most negative number.
     */
    public boolean negative;

    /**
     * The current targets for <code>break</code> statements; i.e., the
     * closest enclosing <code>for</code>, <code>while</code>,
     * <code>do-while</code>, or <code>switch</code> statements.
     */
    private final LinkedList breakTarget = new LinkedList();

    /**
     * The current targets for <code>continue</code> statements; i.e., the
     * closest enclosing <code>for</code>, <code>while</code>, or
     * <code>do-while</code> statements.
     */
    private final LinkedList continueTarget = new LinkedList();

    /**
     * Push a new break target onto the stack
     *
     * @param target the new break target
     */
    public void pushBreak(final JavaAST target) {
	breakTarget.addFirst(target);
    }

    /**
     * Pop a break target off of the stack
     */
    public void popBreak() {
	breakTarget.removeFirst();
    }

    /**
     * Get the current break target
     *
     * @return the current break target
     */
    public StatementAST breakTarget() {
	return (StatementAST)breakTarget.getFirst();
    }

    /**
     * Push a new continue (and break) target onto the stack
     *
     * @param target the new continue target
     */
    public void pushContinue(final JavaAST target) {
	breakTarget.addFirst(target);
	continueTarget.addFirst(target);
    }

    /**
     * Pop a continue (and break) target off of the stack
     */
    public void popContinue() {
	breakTarget.removeFirst();
	continueTarget.removeFirst();
    }

    /**
     * Get the current continue target
     *
     * @return the current continue target
     */
    public StatementAST continueTarget() {
	return (StatementAST)continueTarget.getFirst();
    }
}
