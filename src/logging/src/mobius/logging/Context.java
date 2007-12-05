/*
 * Software Engineering Tools.
 *
 * $Id: Context.jass,v 1.1.1.1 2002/12/29 12:36:10 kiniry Exp $
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

import java.io.Serializable;
import java.util.concurrent.ConcurrentHashMap;
import java.util.Iterator;
import java.util.Map;

/**
 * <p> Context is the data structure that holds the information that is
 * relevant to debugging on a per-thread and a per-thread group basis. </p>
 *
 * <p> Each thread within a program is either in a debugging state or it is
 * not.  To signal that it is in the debugging state, that thread should do
 * the following (perhaps in an initDebug() method):
 *
 * <ol>
 * <li> Create a new Context object for that thread.  E.g.  <code>Context
 * debugContext = new Context();</code> All of the following method calls
 * are applied to this object, unless otherwise noted. </li>
 *
 * <li> Call the <code>turnOn();</code> to turn debugging on for this
 * thread. </li>
 *
 * <li> Add any new debugging categories specific to that thread with one
 * or more of the <code>addCategory()</code> methods. </li>
 *
 * <li> If this thread is only interested in the debugging output from a
 * specific set of classes, the <code>addClass()</code> methods can be used
 * to specify specific methods of interest.  Note that you'll likely want
 * to prefix the series of "class additions" with a
 * <code>removeClass(Thread.currentThread(), "*");</code> to flush the
 * context of the class narrowing/widening. </li>
 *
 * <li> Set the debug level that the thread is interested in with one of
 * the <code>setLevel()</code> methods. </li>
 * </ol>
 *
 * </p>
 *
 * <p> Now your thread has a valid debugging context, encapsulated in
 * its Context object.  This object is then passed to the Debug class
 * via the <code>addContext()</code> method so that the debugging
 * runtime system knows the threads context. </p>
 *
 * @version $Revision: 1.1.1.1 $ $Date: 2002/12/29 12:36:10 $
 * @author Joseph R. Kiniry (kiniry@acm.org)
 * @see Debug
 * @see DebugConstants
 *
 * @design Most of this class used to be called PerDebugElement and
 * was used in package versions 0.01 through 0.17.
 * @design changeonly{} specifications are not used here because the
 * clone() method is part of the IDebug context design and is not
 * implemented for changeonly semantics.
 */
//@ non_null_by_default
public class Context implements Cloneable, Serializable
{
  // Attributes

  /**
   * <p> This class contains several core instance variables:
   *
   * <ol>
   * <li> <code>isOn</code> is a boolean that indicates if debugging for
   * this element (thread or thread group) is turned on. </li>
   *
   * <li> <code>level</code> is an integer that indicates the current
   * debugging level for this element.  Its value ranges from
   * <code>LEVEL_MIN</code> to <code>LEVEL_MAX</code> of the current
   * installed <code>DebugConstantInterface</code>. </li>
   *
   * <li> <code>categoryMap</code> is a map containing
   * information on all categories defined in this debugging context and
   * their severity levels.  A key of this map is the category (type
   * <code>String</code>), while the data value is an <code>Integer</code>
   * representing the severity level of the category. </li>
   *
   * <li> <code>classMap</code> is a map containing information
   * on all classes that have debugging enabled or disabled in this
   * context.  A key of this map is the <code>String</code>
   * representation of a class (<code>Class.getName()</code>), while a data
   * value is a <code>Boolean</code> indicating if a the given class has
   * debugging enabled. </li>
   * </ol>
   * </p>
   *
   * <p> Context objects are stored in the class-global per-thread and
   * per-thread group maps of the <code>Debug</code> class, keyed on
   * references to the thread or thread group, respectively. </p>
   */

  /**
   * A default UID.
   * @review kiniry Put in real UIDs?
   */
  private static final long serialVersionUID = 1L;

  /**
   * @serial The debugging constants for this class.
   */
  private DebugConstants my_debug_constants = null;

  /**
   * @serial A flag indicating if debugging is enabled for this
   * context.  If (isOn == false), all Debug calls like assert() and
   * print(), but for the query and state change functions (like
   * isOn(), turnOn(), etc.), are short-circuited and do nothing.
   */
  private boolean my_is_on;

  /**
   * @serial The current debug level of this context.
   * @design Higher valued levels usually indicate higher priorities.
   * E.g. A level 9 message is in the default implementation an assertion;
   * if it fails, the program exits.  A level 5 message is an error and the
   * user should probably be informed of the problem.  You can override
   * this behavior by subtyping DebugConstants and installing the new
   * constant during the construction of a Context.
   */
  private int my_level;

  /**
   * @serial A map that binds category keys (Strings) to levels
   * (Integers).
   */
  private /*@ non_null @*/ Map my_category_map;

  /**
   * @serial A map that binds class names (Strings) to enable flags
   * (Booleans).
   */
  private /*@ non_null @*/ Map my_class_map;

  /**
   * The thread that owns this context.
   */
  private transient Thread my_thread;

  /**
   * <p> The object used by this thread to control debugging output device.
   * All debugging messages that come from the owning thread will use this
   * output interface. </p>
   */
  private transient DebugOutput my_debug_output_interface;

  /**
   * <p> The standard constructor.  The thread that is constructing the
   * context is the "owning thread".  All calls to this context will be
   * recognized only in the context of the original constructing
   * thread. </p>
   *
   * <p> The constructor initializes all the static data-structures used by
   * the Context class.  Note that the <code>initCategories()</code> method
   * is automatically called as necessary to initialize the default
   * categories database of the Context class. </p>
   *
   * @concurrency CONCURRENT
   * @param some_debug_constants an implementation of the <code>DebugConstants</code> that
   * defines the semantics of this debug context.
   * @param a_debug_output an implementation of <code>DebugOutput</code> that defines
   * the semantics of debugging output.
   */
  //@ assignable my_is_on, my_level;
  //@ assignable my_category_map, my_class_map;
  //@ assignable my_debug_constants, my_debug_output_interface, my_thread;
  // @todo kiniry put fields in objectState and use datagroup in frame axiom
  //@ ensures my_is_on == false;
  //@ ensures my_level == 0;
  //@ ensures my_category_map != null;
  //@ ensures my_class_map != null;
  //@ ensures my_debug_constants != null;
  //@ ensures my_debug_output_interface != null;
  //@ ensures my_thread != null;
  // @todo kiniry Change these postconditions into an initially assertion.
  public Context(final /*@ non_null @*/ DebugConstants some_debug_constants,
                 final /*@ non_null @*/ DebugOutput a_debug_output) {
    super();
    my_is_on = false;
    my_level = 0;
    my_category_map = new ConcurrentHashMap();
    my_class_map = new ConcurrentHashMap();
    my_class_map.put("*", Boolean.TRUE);
    my_debug_constants = some_debug_constants;
    my_debug_constants.initCategories(my_category_map);
    my_debug_output_interface = a_debug_output;
    my_thread = Thread.currentThread();
  }

  /**
   * <p> Used to clone a Context for another thread.  Should be called
   * <em>only</em> by the thread that is going to use/modify the
   * context. </p>
   *
   * @concurrency CONCURRENT
   * @modifies QUERY
   * @return the clone of the Context.
   * @throws CloneNotSupportedException never.
   */
  public /*@ non_null @*/ Object clone() throws CloneNotSupportedException {
    Context contextClone = null;
    try {
      contextClone = (Context)super.clone();
    } catch (CloneNotSupportedException cnse) {
      throw new RuntimeException(cnse.getMessage(), cnse);
    }
    contextClone.my_thread = Thread.currentThread();
    contextClone.my_debug_output_interface = my_debug_output_interface;

    return contextClone;
  }

  /**
   * @return the thread that owns this context.
   *
   * @concurrency CONCURRENT
   * @modifies QUERY
   */
  //@ ensures \result == my_thread;
  public /*@ pure @*/ Thread getThread() {
    return my_thread;
  }

  /**
   * <p> Turns on debugging facilities for the owner thread.  Note that if
   * you do not <code>turnOff()</code> debugging for this thread before it
   * becomes in active in the system, it will not be garbage collected,
   * since it is referenced by the Context object. </p>
   *
   * @concurrency GUARDED
   */
  //@ assignable my_is_on;
  //@ ensures my_is_on;
  public synchronized void turnOn() {
    my_is_on = true;
  }

  /**
   * <p> Turns off debugging facilities for the owner thread.  Note that if
   * you do not <code>turnOff</code> debugging for this thread before it
   * becomes in active in the system, it will not be garbage collected,
   * since it is referenced by the Context object. </p>
   *
   * @concurrency GUARDED
   * @review Create a garbage collection thread for Debug to clean up dead
   * threads?
   */
  //@ assignable my_is_on;
  //@ ensures !my_is_on;
  public synchronized void turnOff() {
    my_is_on = false;
  }

  /**
   * @concurrency GUARDED
   * @modifies QUERY
   * @return a boolean indicating if any debugging is turned on.
   */
  //@ ensures \result == my_is_on;
  public /*@ pure @*/ synchronized boolean isOn() {
    return my_is_on;
  }

  /**
   * <p> Adds a category to the database of legal debugging categories for
   * the owner thread.  Once a category exists in the database, its
   * debugging level cannot be changed without removing and re-adding the
   * category to the database. </p>
   *
   * @concurrency GUARDED
   * @modifies categoryMap
   * @param category the category to add to the global set of categories.
   * @param level the debugging level associated with the passed category.
   * @return a boolean indicating if the category was successfully added to
   * the database.  A false indicates either the category was already in
   * the database at a different level or the parameters were invalid.
   */
  //@ requires category.length() > 0;
  //@ requires validLevel(level);
  //@ ensures containsCategory(category);
  public synchronized boolean addCategory(/*@ non_null @*/ String category,
                                          int level) {
    // See if an entry for the passed category exists.
    if (my_category_map.containsKey(category)) {
      return (((Integer)(my_category_map.get(category))).intValue() == level);
    }

    // Add a new entry for the passed category.
    my_category_map.put(category, Integer.valueOf(level));

    return true;
  }

  /**
   * <p> Removes a category from the database of legal debugging categories
   * for the owner thread. </p>
   *
   * @concurrency GUARDED
   * @param a_category the category to remove.
   * @return a boolean indicating if the category was successfully
   * removed from the database.  A false indicates that the parameters
   * were invalid.
   */
  //@ requires category.length() > 0;
  //@ assignable my_category_map;
  //@ ensures !containsCategory(category);
  public synchronized boolean removeCategory(/*@ non_null @*/ String a_category) {
    // If is in the map, remove it.
    if (my_category_map.containsKey(a_category)) {
      my_category_map.remove(a_category);
      return true;
    } else return false;
  }

  /**
   * @modifies QUERY
   * @concurrency GUARDED
   * @param a_category is the category to lookup.
   * @return a boolean indicating if a category is in the class-global
   * category database.
   */
  //@ requires category.length() > 0;
  public synchronized /*@ pure @*/ boolean containsCategory(/*@ non_null @*/ String a_category) {
    return (my_category_map.containsKey(a_category));
  }

  /**
   * @modifies QUERY
   * @concurrency GUARDED
   * @param a_category is the category to lookup.
   * @return the level of the category provided it is in the category
   * database of this context.
   */
  //@ requires category.length() > 0;
  //@ requires containsCategory(category);
  public synchronized /*@ pure @*/ int getCategoryLevel(/*@ non_null @*/ String a_category) {
    return ((Integer)(my_category_map.get(a_category))).intValue();
  }

  /**
   * @modifies QUERY
   * @concurrency GUARDED
   * @return an iterator that contains the list of per-thread debugging
   * categories that are currently in this Context's category
   * database.  An empty iterator will be returned if there
   * are no categories defined in the database as of yet.
   * @see Map#elements
   */
  public synchronized /*@ pure @*/ Iterator listCategories() {
    return (my_category_map.values().iterator());
  }

  /**
   * @return a boolean indicating that this Context's database of classes
   * contains the specified class.
   *
   * @modifies QUERY
   * @concurrency GUARDED
   * @param className the name of the class to check.
   */
  //@ requires className.length() > 0;
  public synchronized /*@ pure @*/ boolean containsClass(final /*@ non_null @*/ String className) {
    return my_class_map.containsKey(className);
  }

  /**
   * @return a boolean indicating that this Context's database of classes
   * contains the specified class.
   *
   * @modifies QUERY
   * @concurrency GUARDED
   * @param classRef the class to check.
   */
  public synchronized /*@ pure @*/ boolean containsClass(final /*@ non_null @*/ Class classRef) {
    return containsClass(classRef.getName());
  }

  /**
   * <p> Adds a class to this Context's database of classes that have
   * debugging enabled. </p>
   *
   * @concurrency GUARDED
   * @param a_class_reference the class to add to the global table of classes
   * that have debugging enabled.
   */
  //@ assignable my_class_map;
  public synchronized void addClass(final /*@ non_null @*/ Class a_class_reference) {
    Utilities.addClassToMap(my_class_map, a_class_reference.getName());
  }

  /**
   * <p> Adds a class to this Context's database of classes that have
   * debugging enabled. Note that a class of "*" means that all classes
   * will now have debugging enabled for the owning thread.  There is no
   * way to "undo" such a command short of manually adding the individual
   * classes back to the database. (Or, equivalently, removing the
   * complement.) </p>
   *
   * @concurrency GUARDED
   * @param a_class_name the name of the class to add.
   */
  //@ requires className.length() > 0;
  //@ assignable my_class_map;
  public synchronized void addClass(final /*@ non_null @*/ String a_class_name) {
    Utilities.addClassToMap(my_class_map, a_class_name);
  }

  /**
   * <p> Removes a class from this Context's database of classes that have
   * debugging enabled. </p>
   *
   * @concurrency GUARDED
   * @param a_class_reference the class to remove from this Context's table of
   * classes that have debugging enabled.
   */
  //@ assignable my_class_map;
  public synchronized void removeClass(final /*@ non_null @*/ Class a_class_reference) {
    Utilities.removeClassFromMap(my_class_map, a_class_reference.getName());
  }

  /**
   * <p> Removes a class from this Context's database of classes that have
   * debugging enabled.  Note that a class of "*" means that all classes
   * will be removed and debugging disabled.  There is no way to "undo"
   * such a command. </p>
   *
   * @concurrency GUARDED
   * @param a_class_name the class to remove from this Context's table of
   * classes that have debugging enabled.
   */
  //@ requires className.length() > 0;
  //@ assignable my_class_map;
  public synchronized void removeClass(/*@ non_null @*/ String a_class_name) {
    Utilities.removeClassFromMap(my_class_map, a_class_name);
  }

  /**
   * <p> Returns an iterator that contains the list of classes that have
   * debugging enabled in this Context. </p>
   *
   * @modifies QUERY
   * @concurrency GUARDED
   * @return an iterator that contains the list of the classes that
   * currently have debugging enabled (they are in the class database)
   * for the owning thread. Returns an empty iterator if there
   * are no enabled classes.
   * @see Map#elements
   */
  public synchronized /*@ pure @*/ Iterator listClasses() {
    return (my_class_map.values().iterator());
  }

  /**
   * <p> Set a new debugging level for the owning thread. </p>
   *
   * @concurrency GUARDED
   * @param the_new_level the new debugging level.
   */
  //@ requires validLevel(the_new_level);
  //@ assignable my_level;
  //@ ensures getLevel() == the_new_level;
  public synchronized void setLevel(int the_new_level) {
    my_level = the_new_level;
  }

  /**
   * @modifies QUERY
   * @concurrency GUARDED
   * @return the current debugging level for the owning thread.
   */
  //@ ensures validLevel(\result);
  public synchronized /*@ pure @*/ int getLevel() {
    return my_level;
  }

  /**
   * @concurrency CONCURRENT
   * @modifies QUERY
   * @return the <code>DebugOutput</code> for the owning thread.
   */
  public /*@ pure @*/ DebugOutput getOutputInterface() {
    return my_debug_output_interface;
  }

  /**
   * @concurrency CONCURRENT
   * @modifies QUERY
   * @return a flag indicating if the provided level is valid.
   * @param a_level the level to check.
   */

  public /*@ pure @*/ boolean validLevel(int a_level) {
    return ((a_level >= DebugConstants.LEVEL_MIN) &&
            (a_level <= DebugConstants.LEVEL_MAX));
  }

  // Protected Methods
  // Package Methods
  // Private Methods

} // end of class Context

/*
 * Local Variables:
 * Mode: Java
 * fill-column: 75
 * End:
 */
