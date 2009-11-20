package mobius.logging;

/**
 * <p> The core interface to gathering statistics. </p>
 *
 * <p> Users of the Mobius logging framework wishing to keep statistics
 * on their system need to inherit from the abstract class
 * {@link AbstractCollect} and implement its protected methods.
 * The simplest means to collect statistics are to use a map keyed on
 * statistic (since their key is valid) and store Double
 * objects corresponding to the current value of that statistic.  See
 * {@link SimpleCollect} for an example of this
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
 * can initiate early warning systems or preventive maintenance. </li>
 * <li> utilize system debugging context to log certain statistics and not
 * others (using the level and type of <code>Event</code> and the
 * <code>isValidCategory()</code> and <code>isValidLevel()</code> methods
 * herein). </li>
 * </ul>
 *
 * @version alpha-1
 * @author Joseph R. Kiniry (kiniry@acm.org)
 * @see AbstractCollect
 * @see mobius.logging.examples.SimpleCollect
 */
//+@ nullable_by_default
interface Collector {
  //@ public model non_null instance JMLDataGroup collectorObjectState;
  //@ public model non_null instance Debug the_debug_model; in collectorObjectState;

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
  //@ ensures \result <==> (a_debug.getCollect() == this);
  /*@ pure @*/ boolean checkDebugCollectRef(/*@ non_null @*/ Debug a_debug);

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
  //@ public normal_behavior
  //@   requires checkDebugCollectRef(a_debug);
  //@   assignable collectorObjectState;
  //@   ensures the_debug_model == a_debug;
  void setDebug(/*@ non_null @*/ final Debug a_debug);

  /**
   * <p> Register a statistic with the collector. </p>
   *
   * @concurrency CONCURRENT
   * @param a_statistic the statistic to register.
   */
  //@ public normal_behavior
  //@   requires checkStatisticID(a_statistic);
  //@   assignable collectorObjectState;
  //@   ensures isRegistered(a_statistic);
  void register(/*@ non_null @*/ final Statistic a_statistic);

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
  /*@ pure @*/ boolean checkStatisticID(/*@ non_null @*/ Statistic a_statistic);

  /**
   * <p> Unregister a statistic with the collector. </p>
   *
   * @concurrency CONCURRENT
   * @param a_statistic the statistic to unregister.
   */
  //@ public normal_behavior
  //@   assignable collectorObjectState;
  //@   ensures !isRegistered(a_statistic);
  void unregister(final /*@ non_null @*/ Statistic a_statistic);

  /**
   * <p> Check to see if a statistic is registered yet. </p>
   *
   * @param a_statistic the statistic to check.
   * @return whether or not <code>a_statistic</code> has been registered.
   * @postcondition (Result == true) iff register(statistic) took place at
   * some point in time in the execution trace of this collect instance.
   * @modifies QUERY
   */
  /*@ pure @*/ boolean isRegistered(/*@ non_null @*/ Statistic a_statistic);

  /**
   * <p> What is the current value for specific statistic? </p>
   *
   * @param a_statistic the statistic being modified.
   * @return the old value of the statistic.
   */
  /*@ pure @*/ double currentValue(/*@ non_null @*/ Statistic a_statistic);

  /**
   * <p> Report on a particular statistic. </p>
   *
   * @param a_statistic the statistic being reported on.
   * @return a report on the statistic, typically encapsulated in some type
   * of <code>Report</code> object or just a simple <code>String</code>
   * textual report.
   */
  /*@ pure @*/ Object report(/*@ non_null @*/ Statistic a_statistic);

  /**
   * <p> Report on all statistics. </p>
   *
   * @return a report on all statistics, typically encapsulated in some
   * type of Report object or just a simple String textual report.
   */
  /*@ pure @*/ Object reportAll();

  /**
   * <p> Increment a statistic by a specified value. </p>
   *
   * @param the_statistic the statistic being modified.
   * @param the_value the amount to increment the statistic.
   * @return the old value of the statistic.
   */
  //@ public normal_behavior
  //@   assignable collectorObjectState;
  double increment(/*@ non_null @*/ Statistic the_statistic,
                   double the_value);

  /**
   * <p> Increment a statistic by the default value. </p>
   *
   * @param the_statistic the statistic being modified.
   * @return the old value of the statistic.
   */
  //@ public normal_behavior
  //@   assignable collectorObjectState;
  double increment(/*@ non_null @*/ Statistic the_statistic);

  /**
   * <p> Decrement a statistic by a specified value. </p>
   *
   * @param the_statistic the statistic being modified.
   * @param the_value the amount to decrement the statistic.
   * @return the old value of the statistic.
   */
  //@ public normal_behavior
  //@   assignable collectorObjectState;
  double decrement(/*@ non_null @*/ Statistic the_statistic,
                   double the_value);

  /**
   * <p> Decrement a statistic by the default value. </p>
   *
   * @param the_statistic the statistic being modified.
   * @return the old value of the statistic.
   */
  //@ public normal_behavior
  //@   assignable collectorObjectState;
  double decrement(/*@ non_null @*/ Statistic the_statistic);

  /**
   * <p> Reset a statistic to the default start value. </p>
   *
   * @param the_statistic the statistic to reset.
   * @return the old value of the statistic.
   */
  //@ public normal_behavior
  //@   assignable collectorObjectState;
  double reset(/*@ non_null @*/ Statistic the_statistic);

  /**
   * <p> Set a statistic to a specific value. </p>
   *
   * @param the_statistic the statistic being modified.
   * @param the_value the new value of the statistic.
   * @return the old value of the statistic.
   */
  //@ public normal_behavior
  //@   assignable collectorObjectState;
  double set(/*@ non_null @*/ Statistic the_statistic,
             double the_value);

}