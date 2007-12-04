/*
 * Software Engineering Tools.
 *
 * $Id: DebugOutputBase.jass,v 1.1.1.1 2002/12/29 12:36:14 kiniry Exp $
 *
 * Copyright (c) 1997-2001 Joseph Kiniry
 * Copyright (c) 2000-2001 KindSoftware, LLC
 * Copyright (c) 1997-1999 California Institute of Technology
 * 
 * All rights reserved.
 * 
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are
 * met:
 *
 * - Redistributions of source code must retain the above copyright
 * notice, this list of conditions and the following disclaimer.
 * 
 * - Redistributions in binary form must reproduce the above copyright
 * notice, this list of conditions and the following disclaimer in the
 * documentation and/or other materials provided with the distribution.
 * 
 * - Neither the name of the Joseph Kiniry, KindSoftware, nor the
 * California Institute of Technology, nor the names of its contributors
 * may be used to endorse or promote products derived from this software
 * without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS ``AS
 * IS'' AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED
 * TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A
 * PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL KIND SOFTWARE OR
 * CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
 * EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
 * PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR
 * PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
 * LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
 * NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
 * SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */

package mobius.logging;

import java.io.Writer;

/**
 * <p> The abstract class from which all classes providing output methods
 * used to send debugging messages to various types of devices must
 * inherit. All final output methods use the <code>printMsg</code> as their
 * final "output destinations", thus only they need to be overridden. </p>
 *
 * @history Changed visibility of isValidCategory and isValidLevel methods
 * to accomodate specification of subclasses.
 *
 * @version alpha-0
 * @author Joseph R. Kiniry (kiniry@acm.org)
 * @see ConsoleOutput
 * @see ServletLogOutput
 * @see WindowOutput
 * @see WriterOutput
 */

public abstract class AbstractDebugOutputBase implements DebugOutput
{
  // Attributes

  /**
   * <p> The <code>Debug</code> object associated with this output
   * object. </p>
   */
  protected Debug my_debug;

  // Inherited Classes
  // Constructors
  // Public Methods

  //@ ensures \result == my_debug;
  /**
   * @return What is my debugging object?
   */
  public /*@ pure @*/ Debug getDebug() {
    return my_debug;
  }

  //@ modifies my_debug;
  //@ ensures my_debug == the_debug;
  /**
   * Set my debugging object to <code>the_debug</code>.
   *
   * @param the_debug the new debugging object.
   */
  public void setDebug(Debug the_debug) {
    this.my_debug = the_debug;
  }

  /**
   * <p> Print out the debugging message, no questions asked. </p>
   *
   * @param category is the category of this message.
   * @param message is the debugging message to print.
   */
  public abstract void printMsg(String category, String message);

  /**
   * <p> Print out the debugging message, no questions asked. </p>
   *
   * @returns a boolean indicating if the message was printed.
   * @param level The debugging level of this message.
   * @param message The debugging message to print.
   */
  public abstract void printMsg(int level, String message);

  /**
   * <p> Print out the debugging message, no questions asked. </p>
   *
   * @param message The debugging message to print.
   */
  public abstract void printMsg(String message);

  /**
   * <p> Print out a debugging message if the debugging context
   * warrents. </p>
   *
   * @returns a boolean indicating if the message was printed.
   * @param level The debugging level of this message.
   * @param message The debugging message to print.
   */
  public final boolean print(int level, String message)
  {
    // If the level is outside of the valid range, return false.
    if ((level < my_debug.getDebugConstants().LEVEL_MIN) ||
        (level > my_debug.getDebugConstants().LEVEL_MAX))
      return false;

    if (isValidLevel(level)) {
      printMsg(level, message);
      return true;
    } else return false;

    /** ensure [Result_valid] (Result == isValidLevel(level)); **/
  }

  /**
   * <p> Print out an object if the debugging context warrents. </p>
   *
   * @returns a boolean indicating if the message was printed.
   * @param level The debugging level of this message.
   * @param object The object to print.
   */
  public final boolean print(int level, Object object)
  {
    return print(level, object.toString());
  }

  /**
   * <p> Print out a debugging message if the debugging context
   * warrents. </p>
   *
   * @returns a boolean indicating if the message was printed.
   * @param category The category of this message.
   * @param message The debugging message to print.
   */
  public final boolean print(String category, String message)
  {
    if (isValidCategory(category)) {
      printMsg(category, message);
      return true;
    } else return false;

    /** ensure [Result_valid] (Result == isValidCategory(category)); **/
  }

  /**
   * <p> Print out an object if the debugging context warrents. </p>
   *
   * @returns a boolean indicating if the message was printed.
   * @param category The category of this message.
   * @param object The object to print.
   */
  public final boolean print(String category, Object object)
  {
    return print(category, object.toString());
  }

  /**
   * <p> Print out an object if the debugging context warrents. </p>
   *
   * @returns a boolean indicating if the message was printed.
   * @param category The category of this message.
   * @param object The object to print.
   */
  public final boolean println(String category, Object object)
  {
    return println(category, object.toString());
  }

  /**
   * <p> Print out a debugging message if the debugging context
   * warrents. </p>
   *
   * @returns a boolean indicating if the message was printed.
   * @param category The category of this message.
   * @param message The debugging message to print.
   */
  public final boolean println(String category, String message)
  {
    return print(category, message + "\n");
  }

  /**
   * <p> Print out an object if the debugging context warrents. </p>
   *
   * @returns a boolean indicating if the message was printed.
   * @param level The debugging level of this message.
   * @param object The object to print.
   */
  public final boolean println(int level, Object object)
  {
    return println(level, object.toString());
  }

  /**
   * <p> Print out a debugging message if the debugging context
   * warrents. </p>
   *
   * @returns a boolean indicating if the message was printed.
   * @param level The debugging level of this message.
   * @param message The debugging message to print.
   */
  public final boolean println(int level, String message)
  {
    return print(level, message + "\n");
  }

  /**
   * <p> Returns a <code>Writer</code> for this output interface if one is
   * available. </p>
   *
   * @return a <code>Writer</code> for this output interface if one is
   * available.
   * @see java.io.Writer
   */
  public abstract Writer getWriter();

  /**
   * <p> Tests to see if the current debug context is interested in a given
   * category. </p>
   *
   * @param the_category the category to inspect.
   * @return a boolean indicating if the category in question is valid at
   * this time for this context (i.e. debugging framework state, thread,
   * class invoking the method, etc.)
   * @see Context
   */
  public final boolean isValidCategory(final String the_category)
  {
    return my_debug.my_debug_utilities.categoryTest(the_category);
  }

  /**
   * <p> Tests to see if the current debug context is interested in a given
   * level. </p>
   *
   * @param a_level the level to inspect.
   * @return a boolean indicating if the level in question is valid at this
   * time for this context (i.e. debugging framework state, thread, class
   * invoking the method, etc.)
   * @see Context
   */

  public final boolean isValidLevel(final int a_level)
  {
    return my_debug.my_debug_utilities.levelTest(a_level);
  }

  // Protected Methods
  // Package Methods
  // Private Methods

} // end of class DebugOutputBase

/*
 * Local Variables:
 * Mode: Java
 * fill-column: 75
 * End:
 */
