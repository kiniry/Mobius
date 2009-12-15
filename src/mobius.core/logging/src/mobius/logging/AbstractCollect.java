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

import java.util.Map;
import java.util.HashMap;

/**
 * <p> The core interface to gathering statistics. </p>
 *
 * <p> Users of the Mobius logging framework wishing to keep statistics
 * on their system need to inherit from this abstract class and implement
 * the protected methods.  The simplest means to collect statistics are to
 * use a map keyed on statistic (since their key is valid) and store Double
 * objects corresponding to the current value of that statistic.  See
 * {@link SimpleCollect} for an example of this
 * implementation which you can reuse. </p>
 *
 * @version alpha-1
 * @author Joseph R. Kiniry (kiniry@acm.org)
 * @see Statistic
 * @see mobius.logging.examples.SimpleCollect
 */
//+@ nullable_by_default
/*#thread_shared*/ public abstract class AbstractCollect implements Collector {
  // Attributes

  /**
   * <p> A <code>Map</code> used to track statistics
   * definitions. </p>
   */
  private final /*@ non_null spec_public @*/
      Map my_statistics /*#guarded_by this*/; //@ in collectorObjectState;
  //@ maps my_statistics.mapObjectState \into collectorObjectState;

  /**
   * <p> The <code>Debug</code> object associated with this
   * <code>Collect</code> object. </p>
   *
   * @modifies SINGLE-ASSIGNMENT
   */
  private /*@ spec_public @*/ Debug my_debug /*#guarded_by this */ = null; //@ in collectorObjectState;
  //@ represents the_debug_model = my_debug;
  //@ private constraint \old(my_debug) != null ==> my_debug != null;
  
  // Inherited Methods
  // Constructors

  /**
   * <p> Construct a new <code>Collect</code> class. </p>
   */
  // @ assignable my_statistics;
  // @ ensures my_statistics.keyType == \type(Statistic);
  // @ ensures my_statistics.elementType == \type(Statistic);
  // @ ensures my_statistics.containsNull == false;
  public AbstractCollect() {
    my_statistics = new HashMap();
    //@ set my_statistics.keyType = \type(Statistic);
    //@ set my_statistics.elementType = \type(Statistic);
    //@ set my_statistics.containsNull = false;
  }

  // Public Methods

  /** {@inheritDoc} */
  public /*@ pure @*/ boolean checkDebugCollectRef(final /*@ non_null @*/ Debug a_debug) {
    return (a_debug.getCollect() == this);
  }

  /** {@inheritDoc} */
  //@ also
  //@ public normal_behavior
  //@  requires my_debug == null;
  //@  assignable my_debug;
  //@  ensures my_debug == a_debug;
  public final void setDebug(final /*@ non_null @*/ Debug a_debug) {
    my_debug = a_debug;  
  }

  /** {@inheritDoc} */
  //@ also
  //@ public normal_behavior
  //@   assignable collectorObjectState;
  //@   ensures isRegistered(a_statistic);
  public void register(final /*@ non_null @*/ Statistic a_statistic) {
    my_statistics.put(a_statistic, a_statistic);
  }

  /** {@inheritDoc} */
  public /*@ pure @*/ boolean checkStatisticID(final /*@ non_null @*/ Statistic a_statistic) {
    final Object the_old_value = my_statistics.get(a_statistic);
    if (the_old_value != null) {
      // make sure value hasn't changed.
      return (the_old_value == a_statistic);
    }
    return true;
  }

  /** {@inheritDoc} */
  public synchronized void unregister(final /*@ non_null @*/ Statistic a_statistic) {
    my_statistics.remove(a_statistic);
  }

  /** {@inheritDoc} */
  public /*@ pure @*/ boolean isRegistered(final /*@ non_null @*/ Statistic a_statistic) {
    return (my_statistics.get(a_statistic) == a_statistic);
  }

  /** {@inheritDoc} */
  public abstract double currentValue(/*@ non_null @*/ Statistic a_statistic);

  /** {@inheritDoc} */
  public abstract Object report(/*@ non_null @*/ Statistic a_statistic);

  /** {@inheritDoc} */
  public abstract Object reportAll();

  /** {@inheritDoc} */
  public abstract double increment(/*@ non_null @*/ Statistic the_statistic, double the_value);

  /** {@inheritDoc} */
  public abstract double increment(/*@ non_null @*/ Statistic the_statistic);

  /** {@inheritDoc} */
  public abstract double decrement(/*@ non_null @*/ Statistic the_statistic, double the_value);

  /** {@inheritDoc} */
  public abstract double decrement(/*@ non_null @*/ Statistic the_statistic);

  /** {@inheritDoc} */
  //@ also
  //@ public normal_behavior
  //@   assignable collectorObjectState;
  public abstract double reset(/*@ non_null @*/ Statistic the_statistic);

  /** {@inheritDoc} */
  public abstract double set(/*@ non_null @*/ Statistic the_statistic, double the_value);

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
  //@ requires 0 < the_category.length();
  //@ requires my_debug != null;
  protected final synchronized boolean isValidCategory(final /*@ non_null @*/ String the_category) {
    synchronized (my_debug) { /*#no_warn*/
      return my_debug.my_debug_utilities.categoryTest(the_category);
    }
  }

  /**
   * <p> Tests to see if the current debug context is interested in a given
   * level. </p>
   *
   * @param a_level the level to inspect.
   * @return a boolean indicating if the level in question is valid at this
   * time for this context (i.e. debugging framework state, thread, class
   * invoking the method, etc.)
   * @see Context
   */
  //@ requires my_debug != null;
  //@ requires my_debug.my_debug_utilities != null;
  protected synchronized final boolean isValidLevel(final int a_level) {
    synchronized (my_debug) { /*#no_warn*/
      return my_debug.my_debug_utilities.levelTest(a_level);
    }
  }

  // Package Methods
  // Private Methods

} // end of class AbstractCollect

/*
 * Local Variables:
 * Mode: Java
 * fill-column: 75
 * End:
 */
