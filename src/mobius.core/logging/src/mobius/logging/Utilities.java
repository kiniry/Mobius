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
//+@ nullable_by_default
class Utilities {
  // Attributes

  /**
   * <p> The Debug object associated with this object. </p>
   */
  private final /*@ non_null spec_public @*/ Debug my_debug /*#guarded_by this*/;

  // Inherited Methods
  // Constructors

  /**
   * Construct a new Utilities class.
   *
   * @param the_debug the debug instance for this utility class.
   */
  //@ assignable my_debug;
  //@ ensures my_debug == the_debug;
  Utilities(final /*@ non_null @*/ Debug the_debug) {
    this.my_debug = the_debug;
  }

  // Public Methods

  /**
   * <p> Prints the stack trace of the current thread to the current
   * debugging output stream. </p>
   *
   * @concurrency GUARDED
   */
  public static synchronized void printStackTrace() {
    final Throwable throwable = new Throwable();
    throwable.printStackTrace();
  }

  /**
   * <p> Dumps the current stack, but <em>doesn't</em> shut down the
   * current thread.  This method can be called from any thread
   * context. </p>
   *
   * @concurrency GUARDED
   * @see java.lang.Thread#dumpStack
   */

  public static synchronized void dumpStackSafe() {
    Thread.dumpStack();
  }

  // Protected Methods
  // Package Methods

  /**
   * <p> Adds a class to a map of class-specific enabled debugging.
   * If the current class debugging context is "*", adding a class has no
   * effect.  If adding the context "*", the database is cleared and the
   * "*" in inserted. </p>
   * 
   * <p> The caller must guarantee that this method is synchronized. </p>
   *
   * @param the_map the map to which the class is added.
   * @param the_class_name the name of the class to add to the set of classes
   * that have debugging enabled.
   */

  static void addClassToMap(final /*@ non_null @*/ Map the_map,
                            final /*@ non_null @*/ String the_class_name) {
    // If we are adding "*", the tabled should be cleared and the "*"
    // should be inserted.
    if ("*".equals(the_class_name)) {
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
          the_map.put(the_class_name, Boolean.TRUE);
      }
  }

  /**
   * <p> Removes a class from a database of debugging-enabled classes.
   * Note that a class of "*" means that all classes will be removed
   * and debugging disabled.  There is no way to "undo" such a
   * command.  Adding classes after the removal of "*" works as you
   * would expect. </p>
   * 
   * <p> The caller must guarantee that this method is synchronized. </p>
   *
   * @param the_map the map from which the class is removed.
   * @param the_class_name the name of the class to remove.
   */

  static void removeClassFromMap(final /*@ non_null @*/ Map the_map,
                                 final /*@ non_null @*/ String the_class_name) {
    // If we are removing the class "*", just clear the map.
    if ("*".equals(the_class_name)) {
      the_map.clear();
    } else
      // If entry is in the map, remove it.
      the_map.remove(the_class_name);
  }

  /**
   * <p> Tests to see if the current debug context warrants output. </p>
   *
   * @param the_level The debugging level of this message.
   * @return true iff the current debug context warrants output.
   */
  //@ requires my_debug != null;
  /*@ pure @*/ boolean levelTest(final int the_level) {
    // Get the current thread.
    final Thread currentThread = Thread.currentThread();

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
   * @return a boolean indicating if the context warrants output.
   * @param a_category is the category of this message.
   */
  //@ requires a_category.length() > 0;
  boolean categoryTest(final /*@ non_null @*/ String a_category) {
	int the_category_level_int = 0;
    // Get the current thread.
    final Thread the_current_thread = Thread.currentThread();

    synchronized (my_debug) {
        // Check to see if global-debugging is enabled.
        if (my_debug.isOn()) {
          // Get category level
          Integer the_category_level =
              my_debug.categoryLevel(a_category);

          // If this category is not defined in the global map,
          // we break out of the global checks and start the per-thread
          // checks.
          if (the_category_level != null) {
            // Get the debugging level of this defined global category.

            the_category_level_int = the_category_level.intValue();

            // Global debugging is enabled, the category is defined in the
            // global database, so check the current global debugging level
            // and, if it is greater than or equal to the debugging level of
            // the passed category, print out the message.

            return ((the_category_level_int >= my_debug.getLevel()) && sourceClassValid());
          }
      }
      // Global debugging is not enabled, so check per-thread debugging.

      // Check to see if this thread has a debugging context.
      final Context the_debug_context = my_debug.getContext(the_current_thread);

      // If there is no context, or if this thread does not have debugging enabled,
      // or if this category is not defined for the current thread, then
      // we should not give the OK to print.
      if ((the_debug_context == null) || !the_debug_context.isOn() ||
          (!the_debug_context.containsCategory(a_category)))
        return false;

      // The current thread has context, debugging is enabled, the
      // category is defined, so get the per-thread debugging level of
      // this defined per-thread category.
      the_category_level_int = the_debug_context.getCategoryLevel(a_category);

      // Now, see the current per-thread debugging level is >= the
      // per-thread category debugging level of the passed category.  If
      // this condition holds, print the message.

      return ((the_category_level_int >= the_debug_context.getLevel()) && sourceClassValid());
    }
  }

  /**
   * <p> Tests to see whether the object performing the debugging action is
   * permitted to print in the current debugging context. </p>
   *
   * @concurrency GUARDED
   * @return a true if the object performing the debugging action
   * is permitted to print in the current debugging context.
   */
  // XXX @ modifies \nothing;
  // Can't use modifies \nothing since Throwable.printStackTrace has
  // assignable \not_specified
  // @REVIEW Should be obs_pure, not just pure.
  /*@ pure @*/ boolean sourceClassValid() {
    int an_index, the_start_index, the_paren_index;
    Throwable throwable;
    StringWriter a_string_writer;
    PrintWriter a_print_writer;
    StringBuffer a_string_buffer;
    String a_string, a_match_string, a_class_name;
    Map the_class_map;

    // Create a new Throwable object so that we can get a snapshot of
    // the current execution stack.  Snapshot the stack into a
    // StringBuffer that we can parse.
    throwable = new Throwable();
    a_string_writer = new StringWriter();
    a_print_writer = new PrintWriter(a_string_writer);
    throwable.printStackTrace(a_print_writer);

    // Now stringWriter contains a textual snapshot of the current
    // execution stack.  We need to pull lines out of it until we find
    // the last line containing the string "at mobius.logging.".  The very
    // next line is the stack level of the object that called the
    // logging method in question.  We need to strip out its name, then
    // compare it with the database of classes that have debugging
    // enabled.

    a_string_buffer = a_string_writer.getBuffer();
    a_string = a_string_buffer.toString();
    // Match to the last occurrence of a Mobius logging stack frame.
    a_match_string = "mobius.logging";
    an_index = a_string.lastIndexOf(a_match_string);
    // Bump the index past the matched string.
    the_start_index = an_index + a_match_string.length() + 1;
    // Match forward to the beginning of the classname for the next
    // stack frame (the object that called a logging method).
    final String at = "at "; // NOPMD
    an_index = a_string.indexOf(at, the_start_index);
    // Bump up the index past the "at ".
    an_index += at.length();
    // Grab out the class name of the next stack frame.
    the_paren_index = a_string.indexOf('(', an_index);

    // We relay on the output layout of printStackTrace.
    //@ assume the_paren_index != -1;

    // So, everything between index and parenIndex is the class name
    // that we are interested in.
    a_class_name = a_string.substring(an_index, the_paren_index);
    // Strip off the last part past the last ".", it is a method name.
    an_index = a_class_name.lastIndexOf('.');

    // We relay on the output layout of printStackTrace.
    //@ assume an_index != -1;
    a_class_name = a_class_name.substring(0, an_index);

    // Now, we have the name of the class that called the debugging
    // routine.  It is stored in className.

    synchronized (my_debug) {    // See if global debugging is enabled.
      if (my_debug.isOn()) {
          // It is, so see if this class is included in the list of
          // classes that have debugging enabled.
          the_class_map = my_debug.my_class_map;

          // If "*" is in the map, then we are testing for reductive
          // specification of classes.  I.e. if the class is not in the map
          // _and_ "*" is in the map, then we _should_ return a true.  If "*"
          // is _not_ in the map and the class _is_, then we _should_ return
          // a true.  We do not return a false here because there is still the
          // possibility that per-thread context will specify that output
          // should appear.

          if (((the_class_map.containsKey("*")) &&
              (!the_class_map.containsKey(a_class_name))) ||
              (the_class_map.containsKey(a_class_name)))
              return true;
      }

      // Either global debugging isn't enabled or the global debugging
      // context didn't specify that output should appear. So, now we check
      // the per-thread context.

      final Thread currentThread = Thread.currentThread();

      // If there is no per-thread context for the current thread, return a
      // false.

      if (!my_debug.my_thread_map.containsKey(currentThread))
        return false;

      // The table has the key, so get the record for this thread.
      final Context debugContext =
        (Context)(my_debug.my_thread_map.get(currentThread));

      // Is debugging turned on at all for this thread? If not, return a
      // false.
      if (!debugContext.isOn())
        return false;

      // Debugging is enabled for this thread, so perform the same check as
      // above to see if the calling class should output debugging
      // information.  This time, if we fail, we fail.
      if (debugContext.containsClass("*")) {
        return !debugContext.containsClass(a_class_name);
      } else {
        return debugContext.containsClass(a_class_name);
      }
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
