/*
 * Software Engineering Tools.
 *
 * $Id: DebugConstants.jass,v 1.1.1.1 2002/12/29 12:36:13 kiniry Exp $
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

import java.util.Map;

/**
 * <p> <code>DebugConstants</code> is an interface that collects the
 * various constants of the debugging package including debug level ranges,
 * standard debugging messages, statistics definitions, etc. </p>
 *
 * <p> This interface can be implemented or the default implementation of
 * it can be subtyped to modify the various values contained herein for
 * specific debugging subpackages, applications, etc. </p>
 *
 * <p> An example of such a subtype is included as
 * <code>FrenchConstants</code>. </p>
 *
 * <p> The default categories are specified in the following table.
 * <table align="abscenter" border="1" cellspacing="0" cellpadding="0">
 * <tr>
 * <td> <strong>Category</strong> </td>
 * <td> <strong>Level</strong> </td>
 * <td> <strong>Description</strong> </td>
 * </tr>
 * <tr>
 * <td> ASSERTION </td>
 * <td> 9 </td>
 * <td> The highest level category that exists.  Assertions are predicates
 * that <strong>must</strong> be true.  If an assertion is false, a stack
 * dump takes place and the object in question should shut down in an
 * orderly fashion.  Note that a single assertion should be made for each
 * predicate that is in the precondition, postcondition, requires, and
 * ensures expressions for every method. </td>
 * </tr>
 * <tr>
 * <td> FAILURE </td>
 * <td> 9 </td>
 * <td> The highest level category that exists.  Sometimes a object need
 * fail outside an assertion.  This default category provides this
 * functionality.  If a failure is seen, a stack dump takes place and the
 * object in question should shut down in an orderly fashion.</td>
 * </tr>
 * <tr>
 * <td> CRITICAL </td>
 * <td> 7 </td>
 * <td> Very important problems/errors that will eventually cause Failures
 * or Assertions should be tagged as Critical.  The user/system must be
 * information of such problems but the object in question need not shut
 * down immediately and can potentially recover.  Typical examples of
 * Critial errors are resource-related errors (out of memory, disk space,
 * cpu time, etc.).</td>
 * </tr>
 * <tr>
 * <td> ERROR </td>
 * <td> 5 </td>
 * <td> This is the standard error level.  An Error means "something went
 * wrong and the user should probably be notified whether the the system
 * can automatically recover properly or not".</td>
 * </tr>
 * <tr>
 * <td> WARNING </td>
 * <td> 3 </td>
 * <td> A warning is a message that says something has gone wrong but it's
 * not terribly serious.  Warnings are often, but not always, communicated
 * on to the user.</td>
 * </tr>
 * <tr>
 * <td> NOTICE </td>
 * <td> 1 </td>
 * <td> A notice is simply a progress message.  Notices are used to track a
 * thread of control during debugging.</td>
 * </tr>
 * </table>
 * </p>
 *
 * @version alpha-1
 * @author Joseph R. Kiniry (kiniry@acm.org)
 * @see Debug
 * @see Context
 * @see Assert
 * @see DebugOutput
 * @see AbstractCollect
 * @see Statistic
 * @see DefaultDebugConstants
 * @see mobius.logging.examples.FrenchConstants
 */
//@ non_null_by_default
public interface DebugConstants
{
  // Public Attributes

  /**
   * <p> The minimum debug level. </p>
   *
   * @design Higher valued levels usually indicate higher priorities.  E.g.,
   * a level 9 message is in the default implementation an asssertion; if
   * it fails, the program exits.  A level 5 message is an error and the
   * user should probably be informed of the problem.  You can override
   * this behavior by subtyping DebugConstants and installing the new
   * constant set when you construct your Debug instance.
   */

  int LEVEL_MIN = 0;

  /**
   * <p> The maximum debug level. </p>
   */

  int LEVEL_MAX = 9;

  /**
   * <p> An error message that can be localized or otherwise
   * customized. </p>
   */

  String ERROR_STRING = "Error";

  /**
   * <p> An assertion failure message that can be localized or otherwise
   * customized. </p>
   */

  String FAILED_ASSERTION_STRING = "Failed assertion";

  // The default debugging levels are pre-defined to simplify the use
  // of the print() and println() functions for simple debugging.

  /**
   * <p> The highest level category that exists.  Assertions are predicates
   * that <strong>must</strong> be true.  If an assertion is false, a stack
   * dump takes place and the object in question should shut down in an
   * orderly fashion.  Note that a single assertion should be made for each
   * predicate that is in the precondition, postcondition, requires, and
   * ensures expressions for every method. </p>
   */

  int ASSERTION_LEVEL = 9;

  /**
   * <p> The highest level category that exists.  Sometimes a object need
   * fail outside an assertion.  This default category provides this
   * functionality.  If a failure is seen, a stack dump takes place and the
   * object in question should shut down in an orderly fashion. </p>
   */

  int FAILURE_LEVEL = 9;

  /**
   * <p> Very important problems/errors that will eventually cause Failures
   * or Assertions should be tagged as Critical.  The user/system must be
   * information of such problems but the object in question need not shut
   * down immediately and can potentially recover.  Typical examples of
   * Critial errors are resource-related errors (out of memory, disk space,
   * cpu time, etc.). </p>
   */

  int CRITICAL_LEVEL = 7;

  /**
   * <p> This is the standard error level.  An Error means "something went
   * wrong and the user should probably be notified whether the the system
   * can automatically recover properly or not". </p>
   */

  int ERROR_LEVEL = 5;

  /**
   * <p> A warning is a message that says something has gone wrong but it's
   * not terribly serious.  Warnings are often, but not always,
   * communicated on to the user. </p>
   */

  int WARNING_LEVEL = 3;

  /**
   * <p> A notice is simply a progress message.  Notices are used to track
   * a thread of control during debugging. </p>
   */

  int NOTICE_LEVEL = 1;

  // The default debugging categories are pre-defined to simplify the use
  // of the print() and println() functions for simple debugging.

  /**
   * <p> The highest level category that exists.  Assertions are predicates
   * that <strong>must</strong> be true.  If an assertion is false, a stack
   * dump takes place and the object in question should shut down in an
   * orderly fashion.  Note that a single assertion should be made for each
   * predicate that is in the precondition, postcondition, requires, and
   * ensures expressions for every method. </p>
   */

  String ASSERTION = "ASSERTION";

  /**
   * <p> The highest level category that exists.  Sometimes a object need
   * fail outside an assertion.  This default category provides this
   * functionality.  If a failure is seen, a stack dump takes place and the
   * object in question should shut down in an orderly fashion. </p>
   */

  String FAILURE = "FAILURE";

  /**
   * <p> Very important problems/errors that will eventually cause Failures
   * or Assertions should be tagged as Critical.  The user/system must be
   * information of such problems but the object in question need not shut
   * down immediately and can potentially recover.  Typical examples of
   * Critial errors are resource-related errors (out of memory, disk space,
   * cpu time, etc.). </p>
   */

  String CRITICAL = "CRITICAL";

  /**
   * <p> This is the standard error level.  An Error means "something went
   * wrong and the user should probably be notified whether the the system
   * can automatically recover properly or not". </p>
   */

  String ERROR = "ERROR";

  /**
   * <p> A warning is a message that says something has gone wrong but it's
   * not terribly serious.  Warnings are often, but not always,
   * communicated on to the user. </p>
   */

  String WARNING = "WARNING";

  /**
   * <p> A notice is simply a progress message.  Notices are used to track
   * a thread of control during debugging. </p>
   */

  String NOTICE = "NOTICE";

  // Error condition for the Debug class.

  /**
   * <p> Indicates that an invalid thread was passed to a thread-related
   * method in idebug.Debug. </p>
   */

  int INVALID_THREAD = -1;

  // Public Methods

  /**
   * <p> Initializes default categories of debugging facilities. </p>
   *
   * @concurrency CONCURRENT
   * @precondition Parameters must be valid.
   * @postcondition We are inserting the default six types of categories into 
   * the default implementation of <code>DebugConstants</code>.
   * @param the_initial_categories is the map to initialize.
   */
  //@ ensures 6 <= the_initial_categories.size();
  void initCategories(/*@ non_null @*/ Map the_initial_categories);

  /**
   * <p> Check whether a level is valid, that is, bound byte the minimum
   * and maximum levels of this interface's implementation. </p>
   *
   * @param a_level the level to check.
   * @return a boolean indicating if the passed level is valid.
   * @postcondition (Result == (LEVEL_MIN <= l) && (l <= LEVEL_MAX))
   */

  boolean checkLevel(int a_level);

} // end of interface DebugConstants

/*
 * Local Variables:
 * Mode: Java
 * fill-column: 75
 * End:
 */
