/*
 * Software Engineering Tools: The Mobius Logging Framework
 *
 * $Id: Assert.jass,v 1.1.1.1 2002/12/29 12:36:07 kiniry Exp $
 *
 * Copyright (c) 2007 Joseph Kiniry, University College Dublin
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
 * - Neither the name of the Joseph Kiniry, University College Dublin,
 * Mobius, KindSoftware, nor the California Institute of Technology,
 * nor the names of its contributors may be used to endorse or promote
 * products derived from this software without specific prior written
 * permission.
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

/**
 * <p> The core interface to making assertions. </p>
 *
 * @version alpha-1
 * @author Joseph R. Kiniry (kiniry@acm.org)
 * @see Debug
 * @see Context
 */
//@ nullable_by_default
public class Assert
  implements Cloneable {
  // Attributes

  /**
   * <p> The <code>Debug</code> object associated with this
   * <code>Assert</code> object. </p>
   *
   * @modifies SINGLE-ASSIGNMENT
   */
  //@ constraint (my_debug != null) ==> (\old(my_debug) == my_debug);
  private Debug my_debug;

  // Constructors

  /*@ private normal_behavior
    @   assignable my_debug;
    @   ensures my_debug == the_debug;
    @*/
  /**
   * <p> Construct a new <code>Assert</code> class. </p>
   *
   * @param the_debug the debugging interface associated with this assertion interface.
   */
  Assert(final Debug the_debug) {
    my_debug = the_debug;
  }

  // Public Methods

  /*@ public exceptional_behavior
    @   signals (FailedAssertionException) !the_assertion;
    @*/
  /**
   * <p> Assert that the passed boolean expression evaluates to true.  If
   * it does not, the assertion fails, a stack dump takes place via the
   * current debugging output channel, and a
   * <var>FailedAssertionException</var> is thrown. </p>
   *
   * @param the_assertion is the boolean expression to assert.
   *
   * @concurrency GUARDED
   * @modifies QUERY
   */
  public static synchronized /*@ pure @*/ void assertTrue(final boolean the_assertion) {
    if (!the_assertion) {
      Utilities.dumpStackSafe();
      throw new FailedAssertionException();
    }
  }

  /*@ public exceptional_behavior
    @   signals (FailedAssertionException) !the_assertion;
    @*/
  /**
   * <p> Assert that the passed boolean expression evaluates to true.  If
   * it does not, the assertion fails, a stack dump takes place, and a
   * <var>FailedAssertionException</var> is thrown. </p>
   *
   * @param the_assertion is the boolean expression to assert.
   * @param the_assertion_text is the text of the assertion itself.
   *
   * @concurrency GUARDED
   * @modifies QUERY
   */
  public final synchronized /*@ pure @*/ void assertTrue(final boolean the_assertion,
                                                         final String the_assertion_text) {
    if (!the_assertion) {
      final String output = my_debug.getDebugConstants().FAILED_ASSERTION_STRING +
        " `" + the_assertion_text + "'\n";
      my_debug.getOutputInterface().printMsg(output);
      Utilities.dumpStackSafe();
      throw new FailedAssertionException(output);
    }
  }

  /*@ public exceptional_behavior
    @   signals (FailedAssertionException) !the_assertion;
    @*/
   /**
   * <p> Assert that the passed boolean expression evaluates to true.  If
   * it does not, the assertion fails, the message is displayed, a stack
   * dump takes place, and a <var>FailedAssertionException</var> is
   * thrown. </p>
   *
   * @param the_assertion is the boolean expression to assert.
   * @param the_assertion_text is the text of the assertion itself.
   * @param the_assertion_message the debugging message to print if the assertion fails.
   * The method <code>toString()</code> is called on the message object.
   *
   * @concurrency GUARDED
   * @modifies QUERY
   */
  public final synchronized /*@ pure @*/ void
  assertTrue(final boolean the_assertion,
             final String the_assertion_text,
             /*@ non_null @*/ final Object the_assertion_message) {
    if (!the_assertion) {
      final String output = my_debug.getDebugConstants().FAILED_ASSERTION_STRING +
        " `" + the_assertion_text + "': " + the_assertion_message.toString() + "\n";
      my_debug.getOutputInterface().printMsg(output);
      Utilities.dumpStackSafe();
      throw new FailedAssertionException(output);
    }
  }

  // Inherited Methods

  /**
   * {@inheritDoc}
   */
  public final Object clone() throws CloneNotSupportedException {
    try {
      return super.clone();
    } catch (CloneNotSupportedException cnse) {
      throw new RuntimeException(cnse.getMessage(), cnse);
    }
  }

  // Protected Methods
  // Package Methods
  // Private Methods

} // end of class Assert

/*
 * Local Variables:
 * Mode: Java
 * fill-column: 75
 * End:
 */
