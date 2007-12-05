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

import java.util.Iterator;
import java.util.concurrent.ConcurrentHashMap;
import java.util.Map;

/** 
 * <p> <code>Debug</code> is the core class of the Mobius logging and debugging
 * facilities. </p>
 *
 * <p> The <code>Debug</code> class is used as the central facility for
 * configuring debugging for a component. </p>
 *
 * <p> All assertions are handled in the <code>Assert</code> class, all
 * logging is accomplished via the <code>DebugOutput</code> class, and all
 * system monitoring and statistics gathering takes place via the
 * <code>Collect</code> class. </p>
 *
 * <p> This debug package is meant to help, in general, produce high
 * quality, high confidence, code. </p>
 *
 * <p> The <code>Debug</code> facility is non-static.  The first thing your
 * component or application needs to do is construct a new
 * <code>Debug</code> object.  If you wish to install an alternate
 * implementation of the debugging constants (i.e. categories, levels,
 * error messages, etc.), pass your implementation of
 * <code>DebugConstants</code> to the constructor of
 * <code>Debug</code>. </p>
 *
 * <p> Each thread that calls the <code>Debug</code> class has,
 * potentially, a different context.  Elements of this context include a
 * notion of current message level, message types, classes currently under
 * inspection, and whether debugging is turned on or off. </p>
 *
 * <p> Threads create new debugging contexts by constructing a
 * <code>Context</code> object and calling its methods.  This context is
 * then passed to the <code>Debug</code> object to change the current
 * global debugging context at runtime. </p>
 *
 * <p> In brief, the <code>Debug</code> class is normally used in the
 * following manner.  A more detailed discussion of the use of this class
 * can be found in the full documentation for the package.  See the Mobius Logging
 * package's <a href="../../../index.html">main index</a> for more
 * information. </p>
 *
 * <p> Each thread needs to construct a debugging context (see the
 * <code>Context</code> class for details) to detail its specific debugging
 * needs.  After creating a valid debugging context, encapsulated in the
 * <code>Context</code> object, the object is passed to this class
 * (<code>Debug</code>) via the <code>addContext()</code> method so that
 * the debugging runtime system knows the thread's context.  Note that the
 * debug runtime keeps a reference to the passed <code>Context</code>, it
 * does not make a copy of it.  Thus, you can modify the
 * <code>Context</code> (change debugging levels, add new thread-specific
 * categories, etc.)  after the context is installed and changes will be
 * noted immediately by the debug runtime. </p>
 *
 * <p> Finally, you have to direct the output of the debugging runtime.
 * This is accomplished by constructing an implementation of the
 * <code>DebugOutput</code> interface, e.g. <code>ConsoleOutput</code>.
 * This object is then passed to your <code>Debug</code> object via the
 * <code>Debug.setOutputInterface()</code> method. </p>
 *
 * <p> You're ready to rock and roll.  Call <code>debug.getAssert()</code>
 * to get a reference to your debug runtime's <code>Assert</code> object.
 * Finally, if you chose not to install your own implementation of
 * <code>DebugConstants</code>, call <code>debug.getDebugConstants()</code>
 * to get a reference to your debug constants. </p>
 *
 * <p> Then, simply use <code>assert.assert()</code>, the
 * <code>print()</code>, <code>println()</code> of your
 * <code>DebugOutput</code> and/or <code>Utilities.dumpStackSafe()</code>
 * methods in your code as necessary. </p>
 *
 * <p> Note that all class-specific debugging is <em>additive</em> and
 * <em>reductive</em>.  You can either remove all classes from the
 * debugging table then add classes one by one, or you can add all
 * <em>potential</em> classes then remove them one by one at this time.
 * Meaning, when you perform an add of "*", you are <em>not</em> adding all
 * classes currently defined in this VM; you are adding all classes
 * currently defined and all classes that might ever be defined in this
 * VM. </p>
 *
 * @version alpha-1
 * @author Joseph R. Kiniry (kiniry@acm.org)
 * @history Versions 0.01 through 0.10 were developed as
 * <code>edu.caltech.cs.kiniry.coding.Debug</code>.  New revision
 * history began when class was moved to
 * <code>edu.caltech.cs.infospheres.util.Debug</code>.  Six versions
 * were developed while in this package.  The code was then moved to
 * Joe's PhD repository and refactoring began to take place as of
 * cumulative version 0.17.
 *
 * @todo kiniry Possible future enhancements:
 * <ol>
 * <li> New derivative: persistence mobile debug object. </li>
 * <li> GUI interface to runtime debugging. </li>
 * <li> Garbage collection thread for <code>Debug</code> to clean up
 * stopped threads. </li>
 * <li> Support for ThreadGroup contexts. </li>
 * </ol>
 *
 * @review kiniry To make debugging classes as robust as possible, we
 * need to decide if they should not throw exceptions at all and only
 * return error values if outright failures occur in processing, or
 * throw real exceptions, etc.  Once javap is built, this will be
 * something of a non-issue (since the user will not have to type the
 * exception-handling code at all).
 *
 * @review kiniry Should all precondition/postcondition checks be
 * assertions?  This would lower the robustness of the code.  Perhaps
 * this means that the definitions for @pre/postconditions need be
 * refined (i.e. are they always assertions or not?).
 *
 * @review kiniry Should assertions always call stackDump()?  Should
 * they always call System.exit()?  That's not very nice or robust,
 * and it certainly doesn't support distributed debugging well.
 * Perhaps we can throw some kind of InterruptedException in the
 * thread?
 *
 * @review kiniry Should null or zero-length debugging messages be
 * permitted?  Wouldn't this increase robustness?
 *
 * @review kiniry Are print() and println() methods both necessary?
 * Why not just print()?  Similar to the isOn() controversy.
 *
 * @review kiniry Should calls to println with an ASSERTION_LEVEL
 * cause the calling thread to stop, as in a real assertion?  This
 * complicates the semantics of the print() methods.
 *
 * @review kiniry Addition of an exception stack trace printing
 * mechanism (as per dmz, 15 January).
 *
 * @review kiniry Addition of a system property to turn global
 * debugging on/off (as per dmz, 15 January).
 *
 * @design General Debug design obtained through group consensus in
 * mid November, 1997.
 *
 * @todo kiniry Should the global DebugOutput be public?  Should a
 * client be able to get a reference to it via a call to the
 * appropriate getter instead?  I.e. Detect whether the thread is in a
 * per-thread debugging state and, if not, return the global output
 * interface?
 */
//@ non_null_by_default
public class Debug implements Cloneable
{
  // Attributes

  /**
   * <p> <code>my_thread_map</code> is a map of all threads that
   * have some per-thread specific debugging attributes defined.
   * Per-thread attributes include categories and classes.  A key of this
   * map is a reference to a <code>Thread</code>, while a data value
   * is a <code>Context</code> object which contains the information
   * specific to this thread. </p>
   *
   * <p> <code>my_thread_map</code> always has an two entries, one under
   * the key "GLOBAL_CATEGORIES" and one under the key "GLOBAL_CLASSES".
   * These entries contain all the class-global categories and
   * class-specific information for debugging, respectively. </p>
   *
   * <p> Internal class handling is somewhat complicated.  If the
   * expression "*" is <em>removed</em>, the database is simply cleared.
   * If the expression "*" is <em>added</em>, the entry is inserted in the
   * table.  So, if one removes specific classes after removing "*", or if
   * one adds specific classes after adding "*", there is no change to the
   * database.  <em>But</em>, if you remove specific classes after adding
   * "*", or if you add specific classes after removing "*", your changes
   * will be noted.  I.e. <code>Debug</code> handles both additive and
   * reductive specification of classes. </p>
   */
  protected Map my_thread_map;

  /**
   * <p> The debugging constants for this class. </p>
   *
   * @modifies SINGLE-ASSIGNMENT
   */
  /*@ constraint (my_debug_constants != null) ==>
    @            (\old(my_debug_constants) == my_debug_constants);
    @*/
  protected DebugConstants my_debug_constants;

  /**
   * <p> The current "global" (<code>Debug</code> instance scoped) flag
   * indicating if any debugging is enabled.  If (isOn == false), all calls
   * like <code>Assert.assert()</code> and
   * <code>DebugOutput.print()</code>, but for the query and state change
   * functions (like <code>isOn()</code>, <code>turnOn()</code>, etc.)  are
   * short-circuited and do nothing. </p>
   */
  protected boolean my_is_on;

  /*@ invariant my_debug_constants.LEVEL_MIN <= my_level &
    @           my_level <= my_debug_constants.LEVEL_MAX;
    @*/
  /**
   * <p> The current global (<code>Debug</code> instance scoped) debug
   * level of the <code>Debug</code> class. </p>
   *
   * @design Higher valued levels usually indicate higher priorities.
   * E.g. A level 9 message is in the default implementation an asssertion;
   * if it fails, the program exits.  A level 5 message is an error and the
   * user should probably be informed of the problem.  You can override
   * this behavior by subtyping <code>DebugConstants</code> and installing
   * the new constant set when constructing <code>Debug</code>.
   *
   * @values (my_debug_constants.LEVEL_MIN <= level <= my_debug__constants.LEVEL_MAX)
   */
  protected int my_level;

  /**
   * <p> The <code>Assert</code> object associated with this
   * <code>Debug</code> object, when instantiated. </p>
   *
   * @modifies SINGLE-ASSIGNMENT
   */
  //@ constraint (my_assert != null) ==> (\old(my_assert) == my_assert);
  protected Assert my_assert;

  /**
   * <p> The <code>Collect</code> object associated with this
   * <code>Debug</code> object, when instantiated. </p>
   *
   * @modifies SINGLE-ASSIGNMENT
   */
  //@ constraint (my_collect != null) ==> (\old(my_collect) == my_collect);
  protected AbstractCollect my_collect;

  /**
   * <p> Private debugging utility class that encapsulates several helpful
   * algorithms. </p>
   *
   * @modifies SINGLE-ASSIGNMENT
   */
  /*@ constraint (my_debug_utilities != null) ==>
    @            (\old(my_debug_utilities) == my_debug_utilities);
    @*/
  protected Utilities my_debug_utilities;

  /**
   * <p> The class used by this thread to control debugging output device.
   * All global debugging messages will use this interface for output. </p>
   */
  protected transient DebugOutput my_debug_output_interface;

  // Constructors

  /**
   * <p> Construct a new <code>Debug</code> class.  Note that the method
   * <code>setOutputInterface</code> need be called on the newly
   * constructed <code>Debug</code> object before it can be used. </p>
   */

  public Debug()
  {
    init(new DefaultDebugConstants(), null);
  }

  /**
   * <p> Construct a new <code>Debug</code> class.  Note that the method
   * <code>setOutputInterface</code> need be called on the newly
   * constructed <code>Debug</code> object before it can be used. </p>
   *
   * @param some_constants an implementation of the <code>DebugConstants</code>
   * interface that defines the semantics of this debug context.
   * @param a_collect an implementation of the <code>Collect</code> class.
   * @see mobius.logging.examples.SimpleCollect
   */

  public Debug(final /*@ non_null @*/ DebugConstants some_constants,
               final /*@ non_null @*/ AbstractCollect a_collect)
  {
    init(some_constants, a_collect);
  }

  // Public Methods

  // Inherited Methods

  /**
   * {@inheritDoc}
   */
  public final Object clone() throws CloneNotSupportedException
  {
    try {
      return super.clone();
    } catch (CloneNotSupportedException cnse) {
      throw new RuntimeException(cnse.getMessage(), cnse);
    }
  }

  //@ ensures getOutputInterface() == the_new_debug_output;
  /**
   * <p> Set the global output interface to a new
   * <code>DebugOutput</code>. </p>
   *
   * @concurrency CONCURRENT
   * @modifies debugOutputInterface
   * @param the_new_debug_output the new output interface.
   */
  public void setOutputInterface(final DebugOutput the_new_debug_output)
  {
    this.my_debug_output_interface = the_new_debug_output;
  }

  /**
   * @concurrency CONCURRENT
   * @modifies QUERY
   * @return the <code>Assert</code> object associated with this
   * <code>Debug</code> object.
   */
  public /*@ pure @*/ Assert getAssert()
  {
    return my_assert;
  }

  /**
   * @concurrency CONCURRENT
   * @modifies QUERY
   * @return the <code>Collect</code> object associated with this
   * <code>Debug</code> object.
   */
  public /*@ pure @*/ AbstractCollect getCollect()
  {
    return my_collect;
  }

  /**
   * @concurrency CONCURRENT
   * @modifies QUERY
   * @return the <code>DebugOutput</code> corresponding to the invoking
   * thread or, if that thread has no interface, the global output
   * interface.
   */
  public /*@ pure @*/ DebugOutput getOutputInterface()
  {
    Thread currentThread = Thread.currentThread();

    if (my_thread_map.containsKey(currentThread)) {
      Context debugContext =
        (Context)(my_thread_map.get(currentThread));
      return debugContext.getOutputInterface();
    } else return this.my_debug_output_interface;
  }

  /**
   * @concurrency CONCURRENT
   * @modifies QUERY
   * @return the <code>DebugConstants</code> for this <code>Debug</code>
   * object.
   */

  public DebugConstants getDebugConstants()
  {
    return my_debug_constants;
  }

  /**
   * <p> Returns a boolean indicating if any debugging is turned on. </p>
   *
   * @concurrency GUARDED
   * @modifies QUERY
   * @return a boolean indicating if any debugging is turned on.
   */

  public synchronized boolean isOn() {
    return my_is_on;
  }

  /**
   * <p> Returns a boolean indicating whether any debugging facilities are
   * turned on for a particular thread. </p>
   *
   * @concurrency GUARDED
   * @modifies QUERY
   * @ensures Debugging turned on for passed thread.
   * @param thread is the thread that we are interested in.
   * @return a boolean indicating whether any debugging facilities are
   * turned on for a particular thread.
   */

  public synchronized boolean isOn(/*@ non_null @*/ Thread thread)
  {
    // Make sure that there is a legal entry in the threadMap
    // for this particular thread.
    if (my_thread_map.containsKey(thread)) {
      // Get the object that describes the per-thread debugging state.
      final Context the_debug_context = (Context)(my_thread_map.get(thread));

      return the_debug_context.isOn();
    }
    else return false;
  }

  /**
   * <p> Returns a boolean indicating if any debugging is turned off. </p>
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
   * <p> Returns a boolean indicating whether any debugging facilities are
   * turned off for a particular thread. </p>
   *
   * @concurrency GUARDED
   * @modifies QUERY
   * @param thread is the thread that we are interested in.
   * @return a boolean indicating whether any debugging facilities are
   * turned off for a particular thread.
   * @review kiniry Are the isOff() methods necessary at all?
   */

  public synchronized boolean isOff(/*@ non_null @*/ Thread thread)
  {
    return (!isOn(thread));
  }
  
  /**
   * <p> Turns on class-global debugging facilities. </p>
   *
   * @concurrency GUARDED
   * @modifies isOn
   */

  public synchronized void turnOn()
  {
    my_is_on = true;
  }

  /**
   * <p> Turns off class-global debugging facilities. </p>
   *
   * @concurrency GUARDED
   * @modifies isOn
   */

  public synchronized void turnOff()
  {
    my_is_on = false;
  }

  /**
   * <p> Adds a category to the database of legal debugging categories.
   * Once a category exists in the database, its debugging level cannot be
   * changed. </p>
   *
   * @concurrency GUARDED
   * @modifies threadMap, categoryMap
   * @param category the category to add to the global set of 
   * categories.
   * @param level the debugging level associated with the passed
   * category.
   * @return a boolean indicating if the category was successfully
   * added to the database.  A false indicates either the category was
   * already in the database at a different level or the parameters
   * were invalid.
   */
  //@ requires 0 < category.length();
  public synchronized boolean addCategory(/*@ non_null @*/ String category, 
                                          int level)
  {
    // Get a reference to the global category map.
    Map categoryMap = 
      (Map)(my_thread_map.get("GLOBAL_CATEGORIES"));

    return addCategoryToMap(categoryMap, category, level);
  }

  /**
   * <p> Removes a category to the database of legal debugging
   * categories. </p>
   *
   * @concurrency GUARDED
   * @modifies threadMap, categoryMap
   * @param category the category to remove.
   * @return a boolean indicating if the category was successfully
   * removed from the database.  A false indicates that the parameters
   * were invalid.
   */
  //@ requires 0 < category.length();
  public synchronized boolean removeCategory(/*@ non_null @*/ String category)
  {
    // Get a reference to the global category map.
    Map categoryMap =
      (Map)(my_thread_map.get("GLOBAL_CATEGORIES"));

    return removeCategoryFromMap(categoryMap, category);
  }

  /**
   * <p> Returns a boolean indicating if a category is in the class-global
   * category database. </p>
   *
   * @concurrency GUARDED
   * @modifies QUERY
   * @param category is the category to lookup.
   * @return a boolean indicating if a category is in the class-global
   * category database.
   */
  //@ requires 0 < category.length();
  public synchronized boolean containsCategory(/*@ non_null @*/ String category)
  {
    // Get global category map.
    Map map =
      (Map)(my_thread_map.get("GLOBAL_CATEGORIES"));
    
    // If entry exists, return a true; otherwise return a false.
    return (map.containsKey(category));
  }
  
  /**
   * <p> Returns an <code>Iterator</code> that contains the list of
   * class-global debugging categories that are currently in the category
   * database. </p>
   *
   * @concurrency GUARDED
   * @modifies QUERY
   * @return an <code>Iterator</code> that contains the list of class-global
   * debugging categories that are currently in the category database.
   * @see Map#values
   */

  public synchronized Iterator listCategories()
  {
    // Get global category map.
    Map map = 
      (Map)(my_thread_map.get("GLOBAL_CATEGORIES"));
    
    return (map.values().iterator());
  }

  /**
   * <p> Adds a class the the class-global database of classes that
   * have debugging enabled. </p>
   *
   * @concurrency GUARDED
   * @modifies threadMap, classMap
   * @param classRef the class to add to the global table of classes
   * that have debugging enabled.
   */

  public synchronized void addClass(/*@ non_null @*/ Class classRef)
  {
    //  Get a reference to the global class map.
    Map classMap = 
      (Map)(my_thread_map.get("GLOBAL_CLASSES"));

    Utilities.addClassToMap(classMap, classRef.getName());
  }

  /**
   * <p> Adds a class the the class-global database of classes that have
   * debugging enabled. Note that a class of "*" means that all classes
   * will now have debugging enabled.  There is no way to "undo" such a
   * command short of manually adding the individual classes back to the
   * database. (Or, equivalently, removing the complement.) </p>
   *
   * @concurrency GUARDED
   * @modifies threadMap, classMap
   * @param className the name of the class to add.
   */
  //@ requires 0 < className.length();
  public synchronized void addClass(/*@ non_null @*/ String className)
  {
    //  Get a reference to the global class map.
    Map classMap = 
      (Map)(my_thread_map.get("GLOBAL_CLASSES"));

    Utilities.addClassToMap(classMap, className);
  }
  
  /**
   * <p> Removes a class the the class-global database of classes that have
   * debugging enabled. </p>
   *
   * @concurrency GUARDED
   * @modifies threadMap, classMap
   * @param classRef the class to remove.
   */

  public synchronized void removeClass(/*@ non_null @*/ Class classRef)
  {
    //  Get a reference to the global class map.
    Map classMap = 
      (Map)(my_thread_map.get("GLOBAL_CLASSES"));

    Utilities.removeClassFromMap(classMap, 
                                       classRef.getName());
  }

  /**
   * <p> Removes a class the the class-global database of classes that have
   * debugging enabled.  Removes a class from a database of
   * debugging-enabled classes.  Note that a class of "*" means that all
   * classes will be removed and debugging disabled.  There is no way to
   * "undo" such a command. </p>
   *
   * @concurrency GUARDED
   * @modifies threadMap, classMap
   * @param className the name of the class to remove.
   */
  //@ requires 0 < className.length();
  public synchronized void removeClass(/*@ non_null @*/ String className)
  {
    //  Get a reference to the global class map.
    Map classMap = 
      (Map)(my_thread_map.get("GLOBAL_CLASSES"));

    Utilities.removeClassFromMap(classMap, 
                                       className);
  }

  /**
   * <p> Get the context for a specific thread. </p>
   *
   * @concurrency GUARDED
   * @modifies QUERY
   * @modifies threadMap
   * @param thread the thread that we are interested in.
   * @return the <code>Context</code> corresponding to thread, or
   * <code>null</code> if no such context exists.
   */

  public synchronized Context getContext(/*@ non_null @*/ Thread thread)
  {
    if (my_thread_map.containsKey(thread))
      return (Context)(my_thread_map.get(thread));
    else return null;
  }

  /**
   * <p> Adds a context to the the class-global database of threads that
   * have debugging context. </p>
   *
   * @concurrency GUARDED
   * @modifies threadMap
   * @param the_debug_context is the context that we are interested in
   * adding.
   * @return a boolean indicating if the context was added to the
   * database sucessfully or that the thread was already in the
   * database.  A false indicates that the context was invalid.
   */

  public synchronized boolean addContext(/*@ non_null @*/ Context the_debug_context)
  {
    // @review kiniry Why is a null value being checked given the precondition?
    if (the_debug_context == null)
      return false;

    my_thread_map.put(the_debug_context.getThread(), the_debug_context);
    return true;
  }

  /**
   * <p> Removes a context from the the class-global database of
   * threads that have debugging context. </p>
   *
   * @concurrency GUARDED
   * @modifies threadMap
   * @param debugContext is the context that we are interested in
   * removing.
   * @return a boolean indicating if the context was removed from
   * the database sucessfully or that the thread was not in the
   * database at all.  A false indicates that the context was
   * invalid or not in the table.
   */

  public synchronized boolean removeContext(/*@ non_null @*/ Context debugContext)
  {
    // @review kiniry Why is a null value being checked given the precondition?
    if ((debugContext != null) && 
        (my_thread_map.containsKey(debugContext))) {
      my_thread_map.remove(debugContext);
      return true;
    } else return false;
  }

  /**
   * <p> Returns an <code>Enumeration</code> that is the list of
   * class-global classes that have debugging enabled. </p>
   *
   * @concurrency GUARDED
   * @modifies QUERY
   * @return an <code>Enumeration</code> that is the list of class-global
   * classes that currently have debugging enabled (they are in the class
   * database). Returns a null if a null is passed, otherwise a zero-length
   * Enumeration will be returned if there is no information on the thread
   * at all.
   * @see Map#elements
   */

  public synchronized Iterator listClasses()
  {
    // Get global category map.
    Map map = 
      (Map)(my_thread_map.get("GLOBAL_CLASSES"));
    
    return (map.values().iterator());
  }
  
  /**
   * <p> Set a new class-global debugging level. </p>
   *
   * @concurrency GUARDED
   * @modifies level
   * @param level the new debugging level.
   * @return a boolean indicating whether the level change succeeded.
   * The only reason why a setLevel might fail is if the level passed
   * is out of range.
   */

  public synchronized boolean setLevel(int level)
  {
    if ((level >= my_debug_constants.LEVEL_MIN) && 
        (level <= my_debug_constants.LEVEL_MAX)) {
      this.my_level = level;
      return true;
    } else return false;
    
  }

  /**
   * <p> Returns the current class-global debugging level. </p>
   *
   * @concurrency GUARDED
   * @modifies QUERY
   * @return the current class-global debugging level.
   */

  public synchronized int getLevel()
  {
    return my_level;
  }

  /**
   * <p> Returns an <code>Enumeration</code> that is the list of
   * class-global threads that have debugging enabled. </p>
   *
   * @concurrency GUARDED
   * @modifies QUERY
   * @return an <code>Enumeration</code> that is the list of class-global
   * threads that currently have debugging enabled (they are in the thread
   * database).
   * @see Map#keys
   */

  public synchronized Iterator listThreads()
  {
    return my_thread_map.keySet().iterator();
  }

  // Protected Methods
  // Package Methods
  // Private Methods

  /**
   * <p> Initialize all the static data-structures used by the
   * <code>Debug</code> class.  Note that the <code>initCategories()</code>
   * method is automatically called as necessary to initialize the default
   * categories database of the <code>Debug</code> class. </p>
   *
   * @concurrency CONCURRENT
   * @modifies threadMap, debugConstants, assert, collect,
   *           debugUtilities
   * @param the_debug_constants an implementation of the <code>DebugConstants</code> that
   * defines the semantics of this debug context.
   * @param the_collect an implementation of the <code>Collect</code> class.
   */
  //@ ensures threadMap != null;
  //@ ensures getAssert() != null;
  //@ ensures getCollect() == the_collect;
  //@ ensures the_debug_utilities != null;
  //@ ensures getDebugConstants() == the_debug_constants;
  private void init(DebugConstants the_debug_constants,
                    AbstractCollect the_collect)
  {
    my_thread_map = new ConcurrentHashMap();
    Map categoryMap = new ConcurrentHashMap();
    my_thread_map.put("GLOBAL_CATEGORIES", categoryMap);
    this.my_debug_constants = the_debug_constants;
    my_debug_constants.initCategories(categoryMap);
    Map classMap = new ConcurrentHashMap();
    my_thread_map.put("GLOBAL_CLASSES", classMap);
    classMap.put("*", Boolean.TRUE);

    // Note that we need to actually initialize our own debugging context!
    this.my_assert = new Assert(this);
    this.my_collect = the_collect;

    my_debug_utilities = new Utilities(this);

    /** changeonly{threadMap, debugConstants, assert, collect, 
                   debugUtilities}; **/
  }

  /**
   * <p> Adds a category to a map of legal debugging categories.
   * Once a category exists in the database, its debugging level cannot be
   * changed without removing and re-adding the category to the
   * database. </p>
   *
   * @concurrency GUARDED
   * @modifies QUERY
   * @param map the map to remove the class from.
   * @param category the category to add to the set of defined
   * categories.
   * @param level the debugging level associated with the passed
   * category.
   * @return a boolean indicating if the category was sucessfully
   * added to the database.  A false indicates either the category was
   * already in the database at a different level or the parameters
   * were invalid.
   */
  //@ requires 0 < category.length();
  private synchronized boolean 
    addCategoryToMap(/*@ non_null @*/ Map map, 
                     /*@ non_null @*/ String category, int level)
  {
    // See if an entry for the passed category exists.
    if (map.containsKey(category)) {
      return (((Integer)(map.get(category))).intValue() == level);
    }

    // Add a new entry for the passed category.
    map.put(category, Integer.valueOf(level));
    return true;
  }

  /**
   * <p> Removes a category from a database of legal debugging
   * categories. </p>
   *
   * @concurrency GUARDED
   * @modifies threadMap, categoryMap
   * @param map is the thread that we are interested in.
   * @param category the category to remove.
   * @return a boolean indicating if the category was sucessfully
   * removed from the database.  A false indicates that the parameters
   * were invalid.
   */
  //@ requires 0 < category.length();
  private synchronized boolean 
    removeCategoryFromMap(/*@ non_null @*/ Map map, 
                          /*@ non_null @*/ String category)
  {
     // If is in the map, remove it.
    if (map.containsKey(category))
      map.remove(category);
    
    return true;
  }
  
} // end of class Debug

/*
 * Local Variables:
 * Mode: Java
 * fill-column: 75
 * End:
 */

