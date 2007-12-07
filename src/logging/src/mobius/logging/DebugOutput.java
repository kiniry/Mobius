/*
 * Software Engineering Tools.
 *
 * $Id: DebugOutput.jass,v 1.1.1.1 2002/12/29 12:36:13 kiniry Exp $
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
 * <p> The interface which all classes providing output methods used to
 * send debugging messages to various types of devices must implement. </p>
 *
 * @version alpha_1
 * @author Joseph R. Kiniry (kiniry@acm.org)
 * @see AbstractDebugOutputBase
 */
//@ nullable_by_default
public interface DebugOutput {
  // Attributes
  // Inherited Classes
  // Constructors
  // Public Methods

  /**
   * <p> Print out the debugging message, no questions asked. </p>
   *
   * @param the_category is the category of this message.
   * @param the_message is the debugging message to print.
   */
  void printMsg(String the_category, String the_message);

  /**
   * <p> Print out the debugging message, no questions asked. </p>
   *
   * @param the_level The debugging level of this message.
   * @param the_message The debugging message to print.
   */
  void printMsg(int the_level, String the_message);

  /**
   * <p> Print out the debugging message, no questions asked. </p>
   *
   * @param the_message The debugging message to print.
   */
  void printMsg(String the_message);

  /**
   * <p> Print out a debugging message if the debugging context
   * warrants. </p>
   *
   * @return a boolean indicating if the message was printed.
   * @param the_level The debugging level of this message.
   * @param the_message The debugging message to print.
   */
  boolean print(int the_level, String the_message);

  /**
   * <p> Print out an object if the debugging context warrants. </p>
   *
   * @return a boolean indicating if the message was printed.
   * @param the_level The debugging level of this message.
   * @param the_object The object to print.
   */
  boolean print(int the_level, Object the_object);

  /**
   * <p> Print out a debugging message if the debugging context
   * warrants. </p>
   *
   * @return a boolean indicating if the message was printed.
   * @param the_category The category of this message.
   * @param the_message The debugging message to print.
   */
  boolean print(String the_category, String the_message);

  /**
   * <p> Print out an object if the debugging context warrants. </p>
   *
   * @return a boolean indicating if the message was printed.
   * @param the_category The category of this message.
   * @param the_object The object to print.
   */
  boolean print(String the_category, Object the_object);

  /**
   * <p> Print out an object if the debugging context warrants. </p>
   *
   * @return a boolean indicating if the message was printed.
   * @param the_category The category of this message.
   * @param the_object The object to print.
   */
  boolean println(String the_category, Object the_object);

  /**
   * <p> Print out a debugging message if the debugging context
   * warrants. </p>
   *
   * @return a boolean indicating if the message was printed.
   * @param the_category The category of this message.
   * @param the_message The debugging message to print.
   */
  boolean println(String the_category, String the_message);

  /**
   * <p> Print out an object if the debugging context warrants. </p>
   *
   * @return a boolean indicating if the message was printed.
   * @param the_level The debugging level of this message.
   * @param the_object The object to print.
   */
  boolean println(int the_level, Object the_object);

  /**
   * <p> Print out a debugging message if the debugging context
   * warrants. </p>
   *
   * @return a boolean indicating if the message was printed.
   * @param the_level The debugging level of this message.
   * @param the_message The debugging message to print.
   */
  boolean println(int the_level, String the_message);

  /**
   * <p> Returns a <code>Writer</code> for this output interface if one is
   * available. </p>
   *
   * @return a <code>Writer</code> for this output interface if one is
   * available.
   * @see java.io.Writer
   */
  Writer getWriter();

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
  boolean isValidCategory(String the_category);

  /**
   * <p> Tests to see if the current debug context is interested in a given
   * level. </p>
   *
   * @param the_level the level to inspect.
   * @return a boolean indicating if the level in question is valid at this
   * time for this context (i.e. debugging framework state, thread, class
   * invoking the method, etc.)
   * @see Context
   */
  boolean isValidLevel(int the_level);

  // Protected Methods
  // Package Methods
  // Private Methods

} // end of class DebugOutput

/*
 * Local Variables:
 * Mode: Java
 * fill-column: 75
 * End:
 */
