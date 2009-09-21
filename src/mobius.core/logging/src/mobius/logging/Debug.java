/*
 * Software Engineering Tools.
 *
 * $Id: Debug.jass,v 1.1.1.1 2002/12/29 12:36:12 kiniry Exp $
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

import java.util.HashMap;
import java.util.Map;
import java.util.Vector;

/**
 * <p>
 * <code>Debug</code> is the core class of the Mobius logging and debugging
 * facilities.
 * </p>
 *
 * <p>
 * The <code>Debug</code> class is used as the central facility for
 * configuring debugging for a component.
 * </p>
 *
 * <p>
 * All assertions are handled in the <code>Assert</code> class, all logging is
 * accomplished via the <code>DebugOutput</code> class, and all system
 * monitoring and statistics gathering takes place via the <code>Collect</code>
 * class.
 * </p>
 *
 * <p>
 * This debug package is meant to help, in general, produce high quality, high
 * confidence, code.
 * </p>
 *
 * <p>
 * The <code>Debug</code> facility is non-static. The first thing your
 * component or application needs to do is construct a new <code>Debug</code>
 * object. If you wish to install an alternate implementation of the debugging
 * constants (i.e. categories, levels, error messages, etc.), pass your
 * implementation of <code>DebugConstants</code> to the constructor of
 * <code>Debug</code>.
 * </p>
 *
 * <p>
 * Each thread that calls the <code>Debug</code> class has, potentially, a
 * different context. Elements of this context include a notion of current
 * message level, message types, classes currently under inspection, and whether
 * debugging is turned on or off.
 * </p>
 *
 * <p>
 * Threads create new debugging contexts by constructing a <code>Context</code>
 * object and calling its methods. This context is then passed to the
 * <code>Debug</code> object to change the current global debugging context at
 * runtime.
 * </p>
 *
 * <p>
 * In brief, the <code>Debug</code> class is normally used in the following
 * manner. A more detailed discussion of the use of this class can be found in
 * the full documentation for the package. See the Mobius Logging package's
 * <a href="../../../index.html">main index</a> for more information.
 * </p>
 *
 * <p>
 * Each thread needs to construct a debugging context (see the
 * <code>Context</code> class for details) to detail its specific debugging
 * needs. After creating a valid debugging context, encapsulated in the
 * <code>Context</code> object, the object is passed to this class (<code>Debug</code>)
 * via the <code>addContext()</code> method so that the debugging runtime
 * system knows the thread's context. Note that the debug runtime keeps a
 * reference to the passed <code>Context</code>, it does not make a copy of
 * it. Thus, you can modify the <code>Context</code> (change debugging levels,
 * add new thread-specific categories, etc.) after the context is installed and
 * changes will be noted immediately by the debug runtime.
 * </p>
 *
 * <p>
 * Finally, you have to direct the output of the debugging runtime. This is
 * accomplished by constructing an implementation of the
 * <code>DebugOutput</code> interface, e.g. <code>ConsoleOutput</code>.
 * This object is then passed to your <code>Debug</code> object via the
 * <code>Debug.setOutputInterface()</code> method.
 * </p>
 *
 * <p>
 * You're ready to rock and roll. Call <code>debug.getAssert()</code> to get a
 * reference to your debug runtime's <code>Assert</code> object. Finally, if
 * you chose not to install your own implementation of
 * <code>DebugConstants</code>, call <code>debug.getDebugConstants()</code>
 * to get a reference to your debug constants.
 * </p>
 *
 * <p>
 * Then, simply use <code>assert.assert()</code>, the <code>print()</code>,
 * <code>println()</code> of your <code>DebugOutput</code> and/or
 * <code>Utilities.dumpStackSafe()</code> methods in your code as necessary.
 * </p>
 *
 * <p>
 * Note that all class-specific debugging is <em>additive</em> and
 * <em>reductive</em>. You can either remove all classes from the debugging
 * table then add classes one by one, or you can add all <em>potential</em>
 * classes then remove them one by one at this time. Meaning, when you perform
 * an add of "*", you are <em>not</em> adding all classes currently defined in
 * this VM; you are adding all classes currently defined and all classes that
 * might ever be defined in this VM.
 * </p>
 *
 * @version alpha-1
 * @author Joseph R. Kiniry (kiniry@acm.org)
 * @history Versions 0.01 through 0.10 were developed as
 *          <code>edu.caltech.cs.kiniry.coding.Debug</code>. New revision
 *          history began when class was moved to
 *          <code>edu.caltech.cs.infospheres.util.Debug</code>. Six versions
 *          were developed while in this package. The code was then moved to
 *          Joe's PhD repository and refactoring began to take place as of
 *          cumulative version 0.17.
 *
 * @todo kiniry Possible future enhancements:
 *       <ol>
 *       <li> New derivative: persistence mobile debug object. </li>
 *       <li> GUI interface to runtime debugging. </li>
 *       <li> Garbage collection thread for <code>Debug</code> to clean up
 *       stopped threads. </li>
 *       <li> Support for ThreadGroup contexts. </li>
 *       </ol>
 *
 * @review kiniry To make debugging classes as robust as possible, we need to
 *         decide if they should not throw exceptions at all and only return
 *         error values if outright failures occur in processing, or throw real
 *         exceptions, etc. Once javap is built, this will be something of a
 *         non-issue (since the user will not have to type the
 *         exception-handling code at all).
 *
 * @review kiniry Should all precondition/postcondition checks be assertions?
 *         This would lower the robustness of the code. Perhaps this means that
 *         the definitions for
 * @pre/postconditions need be refined (i.e. are they always assertions or
 *                     not?).
 *
 * @review kiniry Should assertions always call stackDump()? Should they always
 *         call System.exit()? That's not very nice or robust, and it certainly
 *         doesn't support distributed debugging well. Perhaps we can throw some
 *         kind of InterruptedException in the thread?
 *
 * @review kiniry Should null or zero-length debugging messages be permitted?
 *         Wouldn't this increase robustness?
 *
 * @review kiniry Are print() and println() methods both necessary? Why not just
 *         print()? Similar to the isOn() controversy.
 *
 * @review kiniry Should calls to println with an ASSERTION_LEVEL cause the
 *         calling thread to stop, as in a real assertion? This complicates the
 *         semantics of the print() methods.
 *
 * @review kiniry Addition of an exception stack trace printing mechanism (as
 *         per dmz, 15 January).
 *
 * @review kiniry Addition of a system property to turn global debugging on/off
 *         (as per dmz, 15 January).
 *
 * @design General Debug design obtained through group consensus in mid
 *         November, 1997.
 *
 * @todo kiniry Should the global DebugOutput be public? Should a client be able
 *       to get a reference to it via a call to the appropriate getter instead?
 *       I.e. Detect whether the thread is in a per-thread debugging state and,
 *       if not, return the global output interface?
 */
//+@ nullable_by_default
/*#thread_shared*/public class Debug implements Cloneable {
  // Attributes

  /**
   * <p>
   * <code>my_thread_map</code> is a map of all threads that have some
   * per-thread specific debugging attributes defined. Per-thread attributes
   * include categories and classes. A key of this map is a reference to a
   * <code>Thread</code>, while a data value is a <code>Context</code>
   * object which contains the information specific to this thread.
   * </p>
   */
  protected /*@ non_null @*/ Map my_thread_map /*#guarded_by this*/;

  /**
   * <p>
   * Class-specific information.
   * </p>
   * 
   * <p>
   * Internal class handling is somewhat complicated. If the expression "*" is
   * <em>removed</em>, the database is simply cleared. If the expression
   * "*" is <em>added</em>, the entry is inserted in the table. So, if one
   * removes specific classes after removing "*", or if one adds specific
   * classes after adding "*", there is no change to the database.
   * <em>But</em>, if you remove specific classes after adding "*", or if
   * you add specific classes after removing "*", your changes will be noted.
   * I.e. <code>Debug</code> handles both additive and reductive
   * specification of classes.
   * </p>
   */
  //@ constraint \old(my_classes_map) == my_classes_map;
  protected /*@ non_null @*/ Map my_classes_map /*#guarded_by this*/;

  /**
   * <p>
   * class-global categories.
   */
  //@ constraint \old(my_categories_map) == my_categories_map;
  protected /*@ non_null @*/ Map my_categories_map /*#guarded_by this*/;

  /**
   * <p>
   * The debugging constants for this class.
   * </p>
   *
   * @modifies SINGLE-ASSIGNMENT
   */
  //@ constraint \old(my_debug_constants) == my_debug_constants;
  protected /*@ non_null @*/ DebugConstants my_debug_constants /*#guarded_by this*/;

  /**
   * <p>
   * The current "global" (<code>Debug</code> instance scoped) flag
   * indicating if any debugging is enabled. If (isOn == false), all calls
   * like <code>Assert.assert()</code> and <code>DebugOutput.print()</code>,
   * but for the query and state change functions (like <code>isOn()</code>,
   * <code>turnOn()</code>, etc.) are short-circuited and do nothing.
   * </p>
   */
  protected /*@ spec_public @*/ boolean my_is_on /*#guarded_by this*/;

  /**
   * <p>
   * The current global (<code>Debug</code> instance scoped) debug level of
   * the <code>Debug</code> class.
   * </p>
   *
   * @design Higher valued levels usually indicate higher priorities. E.g. A
   *         level 9 message is in the default implementation an assertion;
   *         if it fails, the program exits. A level 5 message is an error and
   *         the user should probably be informed of the problem. You can
   *         override this behavior by subtyping <code>DebugConstants</code>
   *         and installing the new constant set when constructing
   *         <code>Debug</code>.
   *
   * @values (my_debug_constants.LEVEL_MIN <= level <= my_debug_constants.LEVEL_MAX)
   */
  //@ invariant my_debug_constants.LEVEL_MIN <= my_level & my_level <= my_debug_constants.LEVEL_MAX;
  protected int my_level /*#guarded_by this*/;

  /**
   * <p>
   * The <code>Assert</code> object associated with this <code>Debug</code>
   * object, when instantiated.
   * </p>
   *
   * @modifies SINGLE-ASSIGNMENT
   */
  protected /*@ non_null @*/ Assert my_assert /*#guarded_by this*/;

  /**
   * <p>
   * The <code>Collect</code> object associated with this <code>Debug</code>
   * object, when instantiated.
   * </p>
   *
   * @modifies SINGLE-ASSIGNMENT
   */
  protected Collector /*#{this}*/ my_collect /*#guarded_by this*/;

  /**
   * <p>
   * Private debugging utility class that encapsulates several helpful
   * algorithms.
   * </p>
   *
   * @modifies SINGLE-ASSIGNMENT
   */
  protected /*@ non_null @*/ Utilities my_debug_utilities /*#guarded_by this*/;

  /**
   * <p>
   * The class used by this thread to control debugging output device. All
   * global debugging messages will use this interface for output.
   * </p>
   */
  protected transient /*@ spec_public @*/ DebugOutput my_debug_output_interface /*#guarded_by this*/;

  // Constructors

  /**
   * <p>
   * Construct a new <code>Debug</code> class. Note that the method
   * <code>setOutputInterface</code> need be called on the newly constructed
   * <code>Debug</code> object before it can be used.
   * </p>
   */
  public Debug() {
    init(new DefaultDebugConstants(), null);
  }

  /**
   * <p>
   * Construct a new <code>Debug</code> class. Note that the method
   * <code>setOutputInterface</code> need be called on the newly constructed
   * <code>Debug</code> object before it can be used.
   * </p>
   *
   * @param some_constants
   *            an implementation of the <code>DebugConstants</code>
   *            interface that defines the semantics of this debug context.
   * @param a_collect
   *            an implementation of the <code>Collect</code> class.
   * @see mobius.logging.examples.SimpleCollect
   */
  public Debug(final /*@ non_null @*/ DebugConstants some_constants,
               final /*@ non_null @*/ Collector a_collect) {
    init(some_constants, a_collect);
  }

  // Public Methods

  // Inherited Methods

  /**
   * {@inheritDoc}
   */
  public final /*@ non_null */ Object clone() throws CloneNotSupportedException {
    try {
      return super.clone();
    } catch (CloneNotSupportedException cnse) {
      throw new RuntimeException(cnse.getMessage(), cnse);
    }
  }

  /**
   * <p>
   * Set the global output interface to a new <code>DebugOutput</code>.
   * </p>
   *
   * @concurrency CONCURRENT
   * @modifies debugOutputInterface
   * @param the_new_debug_output
   *            the new output interface.
   */
  //@ ensures my_debug_output_interface == the_new_debug_output;
  public synchronized void setOutputInterface(final DebugOutput the_new_debug_output) {
    this.my_debug_output_interface = the_new_debug_output;
  }

  /**
   * @concurrency CONCURRENT
   * @modifies QUERY
   * @return the <code>Assert</code> object associated with this
   *         <code>Debug</code> object.
   */
  //@ ensures \result != null;
  public /*@ pure @*/ Assert getAssert() {
    return my_assert;
  }

  /**
   * @concurrency CONCURRENT
   * @modifies QUERY
   * @return the <code>Collect</code> object associated with this
   *         <code>Debug</code> object.
   */
  public /*@ pure @*/ Collector getCollect() {
    return my_collect;
  }

  /**
   * @concurrency CONCURRENT
   * @modifies QUERY
   * @return the <code>DebugOutput</code> corresponding to the invoking
   *         thread or, if that thread has no interface, the global output
   *         interface.
   */
  public synchronized /*@ pure @*/ DebugOutput getOutputInterface() {
    final Thread currentThread = Thread.currentThread();
    final Context debugContext = (Context)(my_thread_map.get(currentThread));

    if (debugContext != null) {
      return debugContext.getOutputInterface();
    } else
      return this.my_debug_output_interface;
  }

  /**
   * @concurrency CONCURRENT
   * @modifies QUERY
   * @return the <code>DebugConstants</code> for this <code>Debug</code>
   *         object.
   */
  public /*@ pure non_null @*/ DebugConstants getDebugConstants() {
    return my_debug_constants;
  }

  /**
   * <p>
   * Returns a boolean indicating if any debugging is turned on.
   * </p>
   *
   * @concurrency GUARDED
   * @modifies QUERY
   * @return a boolean indicating if any debugging is turned on.
   */
  public /*@ pure @*/ synchronized boolean isOn() {
    return my_is_on;
  }

  /**
   * <p>
   * Returns a boolean indicating whether any debugging facilities are turned
   * on for a particular thread.
   * </p>
   *
   * @concurrency GUARDED
   * @modifies QUERY
   * @ensures Debugging turned on for passed thread.
   * @param a_thread
   *            is the thread that we are interested in.
   * @return a boolean indicating whether any debugging facilities are turned
   *         on for a particular thread.
   */
  public synchronized boolean isOn(final /*@ non_null @*/ Thread a_thread) {
      // Get the object that describes the per-thread debugging state.
    final Context the_debug_context = (Context) (my_thread_map.get(a_thread)); //@ nowarn Exception;
    // Make sure that there is a legal entry in the my_thread_map
    // for this particular thread.
    if (the_debug_context != null) {
      return the_debug_context.isOn();
    } else
      return false;
  }

  /**
   * <p>
   * Returns a boolean indicating if any debugging is turned off.
   * </p>
   *
   * @concurrency GUARDED
   * @modifies QUERY
   * @return a boolean indicating if any debugging is turned on.
   * @review kiniry Are the isOff() methods necessary at all?
   */
  public synchronized boolean isOff() {
    return (!isOn());
  }

  /**
   * <p>
   * Returns a boolean indicating whether any debugging facilities are turned
   * off for a particular thread.
   * </p>
   *
   * @concurrency GUARDED
   * @modifies QUERY
   * @param a_thread
   *            is the thread that we are interested in.
   * @return a boolean indicating whether any debugging facilities are turned
   *         off for a particular thread.
   * @review kiniry Are the isOff() methods necessary at all?
   */
  public synchronized boolean isOff(final /*@ non_null @*/ Thread a_thread) {
    return (!isOn(a_thread));
  }

  /**
   * <p>
   * Turns on class-global debugging facilities.
   * </p>
   *
   * @concurrency GUARDED
   * @modifies isOn
   */
  //@ assignable my_is_on;
  //@ ensures my_is_on == true;
  public synchronized void turnOn() {
    my_is_on = true;
  }

  /**
   * <p>
   * Turns off class-global debugging facilities.
   * </p>
   *
   * @concurrency GUARDED
   * @modifies isOn
   */
  //@ assignable my_is_on;
  //@ ensures my_is_on == false;
  public synchronized void turnOff() {
    my_is_on = false;
  }

  /**
   * <p>
   * Adds a category to the database of legal debugging categories. Once a
   * category exists in the database, its debugging level cannot be changed.
   * </p>
   *
   * @concurrency GUARDED
   * @modifies my_thread_map
   * @param a_category
   *            the category to add to the global set of categories.
   * @param a_level
   *            the debugging level associated with the passed category.
   * @return a boolean indicating if the category was successfully added to
   *         the database. A false indicates either the category was already
   *         in the database at a different level or the parameters were
   *         invalid.
   */
  //@ requires 0 < a_category.length();
  public synchronized boolean addCategory(final /*@ non_null @*/ String a_category,
                                          final int a_level) {
    return addCategoryToMap(my_categories_map, a_category, a_level);
  }

  /**
   * <p>
   * Removes a category from the database of legal debugging categories.
   * </p>
   *
   * @concurrency GUARDED
   * @modifies threadMap
   * @param a_category the category to remove.
   * @return a boolean indicating if the category was successfully removed
   *         from the database. A false indicates that the parameters were
   *         invalid.
   */
  //@ requires 0 < a_category.length();
  public synchronized boolean removeCategory(final /*@ non_null @*/ String a_category) {
    return removeCategoryFromMap(my_categories_map, a_category);
  }

  /**
   * <p>
   * Returns a boolean indicating if a category is in the class-global
   * category database.
   * </p>
   *
   * @concurrency GUARDED
   * @modifies QUERY
   * @param a_category
   *            is the category to lookup.
   * @return a boolean indicating if a category is in the class-global
   *         category database.
   */
  //@ requires 0 < a_category.length();
  public synchronized boolean containsCategory(final /*@ non_null @*/ String a_category) {
    return my_categories_map.containsKey(a_category);
  }

  /**
   * <p>
   * Returns a <code>Vector</code> that contains all the class-global
   * debugging categories that are currently in the category database.
   * Only a copy is returned, not the internal structure.
   * </p>
   *
   * @concurrency GUARDED
   * @modifies QUERY
   * @return an <code>Iterator</code> that contains the list of class-global
   *         debugging categories that are currently in the category database.
   * @see Map#values
   */
  public synchronized Vector listCategories() {
    return new Vector( my_categories_map.values());
  }

  /**
   * <p>
   * Adds a class to the class-global database of classes that have debugging
   * enabled.
   * </p>
   *
   * @concurrency GUARDED
   * @modifies threadMap, classMap
   * @param a_class_ref
   *            the class to add to the global table of classes that have
   *            debugging enabled.
   */
  public synchronized void addClass(final /*@ non_null @*/ Class a_class_ref) {
    Utilities.addClassToMap(my_classes_map, a_class_ref.getName());
  }

  /**
   * <p>
   * Adds a class to the class-global database of classes that have debugging
   * enabled. Note that a class of "*" means that all classes will now have
   * debugging enabled. There is no way to "undo" such a command short of
   * manually adding the individual classes back to the database. (Or,
   * equivalently, removing the complement.)
   * </p>
   *
   * @concurrency GUARDED
   * @modifies threadMap, classMap
   * @param a_class_name
   *            the name of the class to add.
   */
  //@ requires 0 < a_class_name.length();
  public synchronized void addClass(final /*@ non_null @*/ String a_class_name) {
    Utilities.addClassToMap(my_classes_map, a_class_name);
  }

  /**
   * <p>
   * Removes a class from the class-global database of classes that have
   * debugging enabled.
   * </p>
   *
   * @concurrency GUARDED
   * @modifies threadMap, classMap
   * @param a_class_ref
   *            the class to remove.
   */
  public synchronized void removeClass(final /*@ non_null @*/ Class a_class_ref) {
    Utilities.removeClassFromMap(my_classes_map, a_class_ref.getName());
  }

  /**
   * <p>
   * Removes a class from the class-global database of classes that have
   * debugging enabled. Removes a class from a database of debugging-enabled
   * classes. Note that a class of "*" means that all classes will be removed
   * and debugging disabled. There is no way to "undo" such a command.
   * </p>
   *
   * @concurrency GUARDED
   * @modifies threadMap, classMap
   * @param a_class_name
   *            the name of the class to remove.
   */
  //@ requires 0 < a_class_name.length();
  public synchronized void removeClass(final /*@ non_null @*/ String a_class_name) {
    Utilities.removeClassFromMap(my_classes_map, a_class_name);
  }

  /**
   * <p>
   * Get the context for a specific thread.
   * </p>
   *
   * @concurrency GUARDED
   * @modifies QUERY
   * @modifies threadMap
   * @param a_thread
   *            the thread that we are interested in.
   * @return the <code>Context</code> corresponding to thread, or
   *         <code>null</code> if no such context exists.
   */
  public synchronized /*@ pure @*/ Context getContext(final /*@ non_null @*/ Thread a_thread) {
    return (Context) (my_thread_map.get(a_thread));
  }

  /**
   * <p>
   * Adds a context to the class-global database of threads that have
   * debugging context.
   * </p>
   *
   * @concurrency GUARDED
   * @modifies my_thread_map
   * @param the_debug_context
   *            is the context that we are interested in adding.
   * @return a boolean indicating if the context was added to the database
   *         successfully or that the thread was already in the database. A
   *         false indicates that the context was invalid.
   */
  public synchronized boolean addContext(final /*@ non_null @*/ Context the_debug_context) {
    // @review kiniry Why is a null value being checked given the
    // precondition?
    if (the_debug_context != null) {
      my_thread_map.put(the_debug_context.getThread(), the_debug_context);
      return true;
    }
    
    return false;
  }

  /**
   * <p>
   * Removes a context from the class-global database of threads that have
   * debugging context.
   * </p>
   *
   * @concurrency GUARDED
   * @modifies my_thread_map
   * @param a_debug_context
   *            is the context that we are interested in removing.
   * @return a boolean indicating if the context was removed from the database
   *         successfully or that the thread was not in the database at all. A
   *         false indicates that the context was invalid or not in the table.
   */
  public synchronized boolean removeContext(final /*@ non_null @*/ Context a_debug_context) {
    // @review kiniry Why is a null value being checked given the
    // precondition?
    if ((a_debug_context != null) && (my_thread_map.containsKey(a_debug_context))) {
      my_thread_map.remove(a_debug_context);
      return true;
    }
    
    return false;
  }

  /**
   * <p>
   * Returns a <code>Vector</code> containing all the class-global classes that have
   * debugging enabled.
   * </p>
   *
   * @concurrency GUARDED
   * @modifies QUERY
   * @return an <code>Enumeration</code> that is the list of class-global
   *         classes that currently have debugging enabled (they are in the
   *         class database). Returns a null if a null is passed, otherwise a
   *         zero-length Enumeration will be returned if there is no
   *         information on the thread at all.
   */
  public synchronized Vector listClasses() {
    return new Vector( my_classes_map.values());
  }

  /**
   * <p>
   * Set a new class-global debugging level.
   * </p>
   *
   * @concurrency GUARDED
   * @modifies level
   * @param the_level
   *            the new debugging level.
   * @return a boolean indicating whether the level change succeeded. The only
   *         reason why a setLevel might fail is if the level passed is out of
   *         range.
   */
  public synchronized boolean setLevel(final int the_level) {
    if ((the_level >= DebugConstants.LEVEL_MIN) &&
        (the_level <= DebugConstants.LEVEL_MAX)) {
      this.my_level = the_level;
      return true;
    }
    
    return false;
  }

  /**
   * <p>
   * Returns the current class-global debugging level.
   * </p>
   *
   * @concurrency GUARDED
   * @modifies QUERY
   * @return the current class-global debugging level.
   */
  public /*@ pure @*/ synchronized int getLevel() {
    return my_level;
  }

  /**
   * <p>
   * Returns a <code>Vector</code> containing all the class-global
   * threads that have debugging enabled. Only a copy is returned,
   * the internal structures are not eposed.
   * </p>
   *
   * @concurrency GUARDED
   * @modifies QUERY
   * @return an <code>Enumeration</code> that is the list of class-global
   *         threads that currently have debugging enabled (they are in the
   *         thread database).
   */
  public synchronized Vector listThreads() {
    return new Vector( my_thread_map.keySet());
  }

  // Protected Methods
  // Package Methods
  // Private Methods

  /**
   * <p>
   * Initialize all the static data-structures used by the <code>Debug</code>
   * class. Note that the <code>initCategories()</code> method is
   * automatically called as necessary to initialize the default categories
   * database of the <code>Debug</code> class.
   * </p>
   *
   * @concurrency CONCURRENT
   * @modifies my_thread_map, debugConstants, assert, collect, debugUtilities
   * @param the_debug_constants
   *            an implementation of the <code>DebugConstants</code> that
   *            defines the semantics of this debug context.
   * @param the_collect
   *            an implementation of the <code>Collect</code> class.
   */
  //@ ensures my_thread_map != null;
  //@ ensures my_classes_map != null;
  //@ ensures my_categories_map != null;
  //@ ensures getAssert() != null;
  //@ ensures getCollect() == the_collect;
  //@ ensures my_debug_utilities != null;
  //@ ensures getDebugConstants() == the_debug_constants;
  //@ nowarn Exception;
  private /*@ helper @*/ void init(final /*@ non_null @*/ DebugConstants the_debug_constants,
                                   final Collector the_collect) {
    my_thread_map = new HashMap();
    //@ set my_thread_map.keyType = \type(Thread);
    //@ set my_thread_map.elementType = \type(Context);
    
    my_categories_map = new HashMap();
    //@ set my_categories_map.keyType = \type(String);
    //@ set my_categories_map.elementType = \type(Integer);

    my_debug_constants = the_debug_constants;
    my_debug_constants.initCategories(my_categories_map);

    my_classes_map = new HashMap();
    //@ set my_categories_map.keyType = \type(String);
    //@ set my_categories_map.elementType = \type(Boolean);
    my_classes_map.put("*", Boolean.TRUE);

    // Note that we need to actually initialize our own debugging context!
    my_assert = new Assert(this);
    my_collect = the_collect;

    my_debug_utilities = new Utilities(this);
  }

  /**
   * <p>
   * Adds a category to a map of legal debugging categories. Once a category
   * exists in the database, its debugging level cannot be changed without
   * removing and re-adding the category to the database.
   * </p>
   *
   * @concurrency GUARDED
   * @modifies QUERY
   * @param the_map
   *            the map to remove the class from.
   * @param a_category
   *            the category to add to the set of defined categories.
   * @param a_level
   *            the debugging level associated with the passed category.
   * @return a boolean indicating if the category was sucessfully added to the
   *         database. A false indicates either the category was already in
   *         the database at a different level or the parameters were invalid.
   */
  //@ requires 0 < a_category.length();
  private synchronized boolean addCategoryToMap(final /*@ non_null @*/ Map the_map,
                                                final /*@ non_null @*/ String a_category,
                                                final int a_level) {
    // See if an entry for the passed category exists.
    if (the_map.containsKey(a_category)) {
      final Integer an_existing_level = (Integer) the_map.get(a_category);
      //@ assume an_existing_level != null;
      return an_existing_level.intValue() == a_level;
    }

    // Add a new entry for the passed category.
    the_map.put(a_category, Integer.valueOf(a_level));
    return true;
  }

  /**
   * <p>
   * Removes a category from a database of legal debugging categories.
   * </p>
   *
   * @concurrency GUARDED
   * @modifies my_thread_map, categoryMap
   * @param the_map
   *            is the thread that we are interested in.
   * @param a_category
   *            the category to remove.
   * @return a boolean indicating if the category was successfully removed from
   *         the database. A false indicates that the parameters were invalid.
   */
  //@ requires 0 < a_category.length();
  private synchronized boolean
  removeCategoryFromMap(final /*@ non_null @*/ Map the_map,
                        final /*@ non_null @*/ String a_category) {
    return the_map.remove(a_category) != null;
  }

} // end of class Debug

/*
 * Local Variables: Mode: Java fill-column: 75 End:
 */

