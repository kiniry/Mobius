/*
 * Software Engineering Tools.
 *
 * $Id: Utilities.jass,v 1.1.1.1 2002/12/29 12:36:17 kiniry Exp $
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

import java.io.PrintWriter;
import java.io.StringWriter;
import java.util.Map;

/**
 * <p> A collection of shared algorithms for the this package. </p>
 *
 * @version alpha-1
 * @author Joseph R. Kiniry (kiniry@acm.org)
 * @see Debug
 * @see Context
 */
//@ non_null_by_default
class Utilities
{
  // Attributes

  /**
   * <p> The Debug object associated with this object. </p>
   */
  private Debug my_debug;

  // Inherited Methods
  // Constructors

  //@ assignable my_debug;
  //@ ensures my_debug == the_debug;
  /**
   * Construct a new Utilities class.
   *
   * @param the_debug the debug instance for this utility class.
   */
  Utilities(final Debug the_debug)
  {
    this.my_debug = the_debug;
  }

  // Public Methods

  /**
   * <p> Prints the stack trace of the current thread to the current
   * debugging output stream. </p>
   *
   * @concurrency GUARDED
   */
  public static synchronized void printStackTrace()
  {
    final Throwable throwable = new Throwable();
    throwable.printStackTrace();
  }

  /**
   * <p> Dumps the current stack and but <em>doesn't</em> shut down the
   * current thread.  This method can be called from any thread
   * context. </p>
   *
   * @concurrency GUARDED
   * @see java.lang.Thread#dumpStack
   */

  public static synchronized void dumpStackSafe()
  {
    final Thread currentThread = Thread.currentThread();
    currentThread.dumpStack();
  }

  // Protected Methods
  // Package Methods

  /**
   * <p> Adds a class to a map of class-specific enabled debugging.
   * If the current class debugging context is "*", adding a class has no
   * effect.  If adding the context "*", the database is cleared and the
   * "*" in inserted. </p>
   *
   * @concurrency GUARDED
   * @param the_map the map to which the class is added.
   * @param the_class_name the name of the class to add to the set of classes
   * that have debugging enabled.
   */

  static synchronized void addClassToMap(final /*@ non_null @*/ Map the_map,
                                         final /*@ non_null @*/ String the_class_name)
  {
    // If we are adding "*", the tabled should be cleared and the "*"
    // should be inserted.
    if (the_class_name.equals("*")) {
      the_map.clear();
      the_map.put("*", Boolean.TRUE);
    } else
      // See if an entry for the passed class exists.
      if (!the_map.containsKey(the_class_name)) {
        // If a "*" is in the table, then don't bother adding at all, just
        // return true.
        if (the_map.containsKey("*"))
          return;
        else
          // Add a new entry for the passed class.
          the_map.put(the_class_name, null);
      }
  }

  /**
   * <p> Removes a class from a database of debugging-enabled classes.
   * Note that a class of "*" means that all classes will be removed
   * and debugging disabled.  There is no way to "undo" such a
   * command.  Adding classes after the removal of "*" works as you
   * would expect. </p>
   *
   * @concurrency GUARDED
   * @param the_map the map from which the class is removed.
   * @param the_class_name the name of the class to remove.
   */

  static synchronized void removeClassFromMap(final /*@ non_null @*/ Map the_map,
                                              final /*@ non_null @*/ String the_class_name)
  {
    // If we are removing the class "*", just clear the map.
    if (the_class_name.equals("*")) {
      the_map.clear();
    } else
      // If entry is in the map, remove it.
      if (the_map.containsKey(the_class_name))
        the_map.remove(the_class_name);
  }

  /**
   * <p> Tests to see if the current debug context warrants output. </p>
   *
   * @concurrency GUARDED
   * @param the_level The debugging level of this message.
   * @return true iff the current debug context warrants output.
   */

  synchronized boolean levelTest(final int the_level)
  {
    // Get the current thread.
    Thread currentThread = Thread.currentThread();

    // Check to see if global-debugging is enabled.
    if (my_debug.isOn()) {
      // Global debugging is enabled, so check the current global
      // debugging level and, if it is greater than or equal to the
      // passed debugging level, print out the message.

      return ((the_level >= my_debug.getLevel()) && sourceClassValid());
    }

    // Global debugging is not enabled, so check per-thread debugging.

    // Check to see if this thread has a debugging context.
    final Context the_debug_context = my_debug.getContext(currentThread);

    // If there is no context of if this thread does not have debugging enabled,
    // we should not give the ok to print.
    if ((the_debug_context == null) || (!the_debug_context.isOn()))
      return false;

    // Now, see the current per-thread debugging level is >= the
    // passed debugging level.  If this condition holds, print the
    // message.

    return ((the_level >= the_debug_context.getLevel()) && sourceClassValid());
  }

  /**
   * <p> Tests to see if the current debug context warrants output. </p>
   *
   * @concurrency GUARDED
   * @return a boolean indicating if the context warrants output.
   * @param a_category is the category of this message.
   */

  synchronized boolean categoryTest(final String a_category)
  {
    int the_category_level = 0;

    // Get the current thread.
    final Thread the_current_thread = Thread.currentThread();

    // Check to see if global-debugging is enabled.
    if (my_debug.isOn()) {
      // Get a reference to the global category map.
      final Map the_category_map =
        (Map)(my_debug.my_thread_map.get("GLOBAL_CATEGORIES"));

      // If this category is not defined in the global map,
      // we break out of the global checks and start the per-thread
      // checks.
      if (the_category_map.containsKey(a_category)) {
        // Get the debugging level of this defined global category.

        the_category_level =
          ((Integer)(the_category_map.get(a_category))).intValue();

        // Global debugging is enabled, the category is defined in the
        // global database, so check the current global debugging level
        // and, if it is greater than or equal to the debugging level of
        // the passed category, print out the message.

        return ((the_category_level >= my_debug.getLevel()) && sourceClassValid());
      }
    }

    // Global debugging is not enabled, so check per-thread debugging.

    // Check to see if this thread has a debugging context.
    final Context the_debug_context = my_debug.getContext(the_current_thread);

    // If there is no context, or if this thread does not have debugging enabled,
    // or if this category is not defined for the current thread, then
    // we should not give the ok to print.
    if ((the_debug_context == null) || !the_debug_context.isOn() ||
        (!the_debug_context.containsCategory(a_category)))
      return false;

    // The current thread has context, debugging is enabled, the
    // category is defined, so get the per-thread debugging level of
    // this defined per-thread category.
    the_category_level = the_debug_context.getCategoryLevel(a_category);

    // Now, see the current per-thread debugging level is >= the
    // per-thread category debugging level of the passed category.  If
    // this condition holds, print the message.

    if ((the_category_level >= the_debug_context.getLevel()) && sourceClassValid())
      return true;

    return false;
  }

  /**
   * <p> Tests to see whether the object performing the debugging action is
   * permitted to print in the current debugging context. </p>
   *
   * @concurrency GUARDED
   * @return a true if the object performing the debugging action
   * is permitted to print in the current debugging context.
   */

  synchronized boolean sourceClassValid()
  {
    int index, startIndex, parenIndex;
    Throwable throwable;
    StringWriter stringWriter;
    PrintWriter printWriter;
    StringBuffer stringBuffer;
    String string, matchString, className;
    Map classMap;
    
    // Create a new Throwable object so that we can get a snapshot of
    // the current execution stack.  Snapshot the stack into a
    // StringBuffer that we can parse.
    throwable = new Throwable();
    stringWriter = new StringWriter();
    printWriter = new PrintWriter(stringWriter);
    throwable.printStackTrace(printWriter);

    // Now stringWriter contains a textual snapshot of the current
    // execution stack.  We need to pull lines out of it until we find
    // the last line containing the string "at mobius.logging.".  The very
    // next line is the stack level of the object that called the
    // logging method in question.  We need to strip out its name, then
    // compare it with the database of classes that have debugging
    // enabled.

    stringBuffer = stringWriter.getBuffer();
    string = stringBuffer.toString();
    // Match to the last occurence of a Mobius logging stack frame.
    matchString = "mobius.logging";
    index = string.lastIndexOf(matchString);
    // Bump the index past the matched string.
    startIndex = index + matchString.length() + 1;
    // Match forward to the beginning of the classname for the next
    // stack frame (the object that called a logging method).
    final String at = "at "; // NOPMD
    index = string.indexOf(at, startIndex);
    // Bump up the index past the "at ".
    index += at.length();
    // Grab out the class name of the next stack frame.
    parenIndex = string.indexOf('(', index);
    // So, everything between index and parenIndex is the class name
    // that we are interested in.
    className = string.substring(index, parenIndex);
    // Strip off the last part past the last ".", it is a method name.
    index = className.lastIndexOf('.');
    className = className.substring(0, index);

    // Now, we have the name of the class that called the debugging
    // routine.  It is stored in className.

    // See if global debugging is enabled.
    if (my_debug.isOn()) {
      // It is, so see if this class is included in the list of
      // classes that have debugging enabled.
      classMap =
        (Map)(my_debug.my_thread_map.get("GLOBAL_CLASSES"));

      // If "*" is in the map, then we are testing for reductive
      // specification of classes.  I.e. if the class is not in the map
      // _and_ "*" is in the map, then we _should_ return a true.  If "*"
      // is _not_ in the map and the class _is_, then we _should_ return
      // a true.  We do not return a false here because there is still the
      // possibility that per-thread context will specify that output
      // should appear.

      if ((classMap.containsKey("*")) &&
          (!classMap.containsKey(className)))
        return true;
      else
        if (classMap.containsKey(className))
          return true;
    }

    // Either global debugging isn't enabled or the global debugging
    // context didn't specify that output should appear. So, now we check
    // the per-thread context.

    Thread currentThread = Thread.currentThread();

    // If there is no per-thread context for the current thread, return a
    // false.

    if (!my_debug.my_thread_map.containsKey(currentThread))
      return false;

    // The table has the key, so get the record for this thread.
    Context debugContext =
      (Context)(my_debug.my_thread_map.get(currentThread));

    // Is debugging turned on at all for this thread? If not, return a
    // false.
    if (!debugContext.isOn())
      return false;
    
    // Debugging is enabled for this thread, so perform the same check as
    // above to see if the calling class should output debugging
    // information.  This time, if we fail, we fail.
    if (debugContext.containsClass("*")) {
      return !debugContext.containsClass(className);
    } else {
      return debugContext.containsClass(className);
    }
  }

  // Private Methods
  
} // end of class Utilities

/*
 * Local Variables:
 * Mode: Java
 * fill-column: 75
 * End:
 */

