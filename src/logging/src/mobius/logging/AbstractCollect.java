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

import java.util.concurrent.ConcurrentHashMap;
import java.util.Map;

/**
 * <p> The core interface to gathering statistics. </p>
 *
 * <p> Users of the Mobius logging framework wishing to keep statistics
 * on their system need to inherit from this abstract class and implement
 * the protected methods.  The simplest means to collect statistics are to
 * use a map keyed on statistic (since their key is valid) and store Double
 * objects corresponding to the current value of that statistic.  See
 * <code>mobius.logging.SimpleCollect</code> for an example of this
 * implementation which you can reuse. </p>
 *
 * @idea Alternative implementations that have some or all of the following
 * characteristics are encouraged.  Ideas include collectors that:
 * <ul>
 * <li> send logging information at certain time intervals or trigger
 * values. </li>
 * <li> log statistic trace sets to do data analysis over long time
 * intervals. </li>
 * <li> compute means and variances so that accurate characterization of
 * the data is available. </li>
 * <li> detect significant changes in system behavior or performance and
 * can initiate early warning systems or preventive maintenence. </li>
 * <li> utilize system debugging context to log certain statistics and not
 * others (using the level and type of <code>Event</code> and the
 * <code>isValidCategory()</code> and <code>isValidLevel()</code> methods
 * herein). </li>
 * </ul>
 *
 * @version alpha-1
 * @author Joseph R. Kiniry (kiniry@acm.org)
 * @see Statistic
 * @see mobius.logging.examples.SimpleCollect
 */
//@ non_null_by_default
public abstract class AbstractCollect
{
  // Attributes

  /**
   * <p> A <code>Map</code> used to track statistics
   * definitions. </p>
   */
  private /*@ non_null @*/ Map my_statistics;

  /**
   * <p> The <code>Debug</code> object associated with this
   * <code>Collect</code> object. </p>
   *
   * @modifies SINGLE-ASSIGNMENT
   */
  //@ constraint (my_debug != null) ==> (my_debug == \old(my_debug));
  private /*@ non_null @*/ Debug my_debug;

  // Inherited Methods
  // Constructors

  /**
   * <p> Construct a new <code>Collect</code> class. </p>
   */
  public AbstractCollect() {
    this.my_statistics = new ConcurrentHashMap();
  }

  // Public Methods

  /**
   * <p> Checks a debug instance to make sure its <code>collect</code>
   * attribute references this <code>Collect</code> object. </p>
   *
   * @concurrency CONCURRENT
   * @modifies QUERY
   * @param a_debug the debug instance to check.
   * @return true iff <code>a_debug</code>'s collect field references
   * <code>this</code>.
   */
  //@ ensures \result <==> (a_debug.collect == this);
  public boolean checkDebugCollectRef(Debug a_debug) {
    return (a_debug.getCollect() == this);
  }

  /**
   * <p> Set the debug instance associated with this collect instance.
   * This method <strong>must</strong> be called with the correct debug
   * instance prior to using <strong>any</strong> of the methods of this
   * <code>Collect</code> instance. </p>
   *
   * @concurrency CONCURRENT
   * @param a_debug the debug object associated with this <code>Collect</code>
   * object.
   */
  //@ requires checkDebugCollectRef(a_debug);
  //@ assignable my_debug;
  //@ ensures my_debug == a_debug;
  public final void setDebug(final Debug a_debug) {
    my_debug = a_debug;
  }

  /**
   * <p> Register a statistic with the collector. </p>
   *
   * @concurrency CONCURRENT
   * @param a_statistic the statistic to register.
   */
  //@ requires checkStatisticID(a_statistic);
  //@ assignable my_statistics;
  //@ ensures isRegistered(a_statistic);
  public void register(final Statistic a_statistic) {
    my_statistics.put(a_statistic, a_statistic);
  }

  /**
   * <p> Check the ID of a statistic and make sure that it hasn't changed
   * since it was registered. </p>
   *
   * @concurrency CONCURRENT
   * @modifies QUERY
   * @param a_statistic the statistic to check.
   * @return a boolean indicating if the value of the statistic
   * <code>a_statistic</code> has changed at all.
   */
  public boolean checkStatisticID(/*@ non_null @*/ Statistic a_statistic) {
    final Object the_old_value = my_statistics.get(a_statistic);
    if (the_old_value != null) {
      // make sure value hasn't changed.
      return (the_old_value == a_statistic);
    }
    return true;
  }

  /**
   * <p> Unregister a statistic with the collector. </p>
   *
   * @concurrency CONCURRENT
   * @param a_statistic the statistic to unregister.
   */
  //@ assignable my_statistics;
  //@ ensures !isRegistered(a_statistic);
  public void unregister(final Statistic a_statistic) {
    my_statistics.remove(a_statistic);
  }

  /**
   * <p> Check to see if a statistic is registered yet. </p>
   *
   * @param a_statistic the statistic to check.
   * @return whether or not <code>a_statistic</code> has been registered.
   * @postcondition (Result == true) iff register(statistic) took place at
   * some point in time in the execution trace of this collect instance.
   * @modifies QUERY
   */
  //@ ensures \result <==> my_statistics.get(a_statistic) == a_statistic;
  public boolean isRegistered(Statistic a_statistic) {
    return (my_statistics.get(a_statistic) == a_statistic);
  }

  /**
   * <p> What is the current value for specific statistic? </p>
   *
   * @param a_statistic the statistic being modified.
   * @return the old value of the statistic.
   */
  public abstract double currentValue(Statistic a_statistic);

  /**
   * <p> Report on a particular statistic. </p>
   *
   * @param a_statistic the statistic being reported on.
   * @return a report on the statistic, typically encapsulated in some type
   * of <code>Report</code> object or just a simple <code>String</code>
   * textual report.
   */
  public abstract Object report(Statistic a_statistic);

  /**
   * <p> Report on all statistics. </p>
   *
   * @return a report on all statistics, typically encapsulated in some
   * type of Report object or just a simple String textual report.
   */
  public abstract Object reportAll();

  /**
   * <p> Increment a statistic by a specified value. </p>
   *
   * @param the_statistic the statistic being modified.
   * @param the_value the amount to increment the statistic.
   * @return the old value of the statistic.
   */
  public abstract double increment(Statistic the_statistic, double the_value);

  /**
   * <p> Increment a statistic by the default value. </p>
   *
   * @param the_statistic the statistic being modified.
   * @return the old value of the statistic.
   */
  public abstract double increment(Statistic the_statistic);

  /**
   * <p> Decrement a statistic by a specified value. </p>
   *
   * @param the_statistic the statistic being modified.
   * @param the_value the amount to decrement the statistic.
   * @return the old value of the statistic.
   */
  public abstract double decrement(Statistic the_statistic, double the_value);

  /**
   * <p> Decrement a statistic by the default value. </p>
   *
   * @param the_statistic the statistic being modified.
   * @return the old value of the statistic.
   */
  public abstract double decrement(Statistic the_statistic);

  /**
   * <p> Reset a statistic to the default start value. </p>
   *
   * @param the_statistic the statistic to reset.
   * @return the old value of the statistic.
   */
  public abstract double reset(Statistic the_statistic);

  /**
   * <p> Set a statistic to a specific value. </p>
   *
   * @param the_statistic the statistic being modified.
   * @param the_value the new value of the statistic.
   * @return the old value of the statistic.
   */
  public abstract double set(Statistic the_statistic, double the_value);

  // Protected Methods

  /**
   * <p> Tests to see if the current debug context is interested in a given
   * category. </p>
   *
   * @param the_category the category to inspect.
   * @return a boolean indicating if the category in question is valid at
   * this time for this context (i.e. debugging framework state, thread,
   * class invoking the method, etc.)
   * @see Context
   * @modifies QUERY
   */
  protected final /*@ pure @*/ boolean isValidCategory(final String the_category) {
    return my_debug.my_debug_utilities.categoryTest(the_category);
  }

  /**
   * <p> Tests to see if the current debug context is interested in a given
   * level. </p>
   *
   * @param level the level to inspect.
   * @return a boolean indicating if the level in question is valid at this
   * time for this context (i.e. debugging framework state, thread, class
   * invoking the method, etc.)
   * @see Context
   */
  protected final boolean isValidLevel(int level) {
    return my_debug.my_debug_utilities.levelTest(level);
  }

  // Package Methods
  // Private Methods

} // end of class Collect

/*
 * Local Variables:
 * Mode: Java
 * fill-column: 75
 * End:
 */
