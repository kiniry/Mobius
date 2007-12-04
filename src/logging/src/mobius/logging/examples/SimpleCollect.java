/*
 * Software Engineering Tools.
 *
 * $Id: SimpleCollect.jass,v 1.1.1.1 2002/12/29 12:36:18 kiniry Exp $
 *
 * Copyright (c) 1997-2001 Joseph Kiniry
 * Copyright (c) 2000-2001 KindSoftware, LLC
 * Copyright (c) 1997-1999 California Institute of Technology
 * 
 * All rights reserved.
 * 
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
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

package mobius.logging.examples;

import mobius.logging.*;
import java.util.Iterator;
import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;

/**
 * <p> A default simple core interface to gathering statistics. </p>
 *
 * <p> Users of IDebug wishing to keep statistics on their system need to
 * inherit from this abstract class and implement the protected methods.
 * The simplest means to collect statistics are to use a hashtable keyed on
 * statistic (since their <code>hashCode</code> is valid) and store
 * <code>Double</code> objects corresponding to the current value of that
 * statistic.  This class implements this method as an example and for
 * use. </p>
 *
 * <p> Note that this class performs <strong>no filtering
 * whatsoever</strong>.  Regardless of the current debug context, etc.,
 * this class will keep track of all statistics. </p>
 *
 * @version $Revision: 1.1.1.1 $ $Date: 2002/12/29 12:36:18 $
 * @author Joseph R. Kiniry <kiniry@acm.org>
 * @see Statistic
 * @see AbstractCollect 
 */

public class SimpleCollect extends AbstractCollect implements Cloneable
{
  // Attributes

  /**
   * <p> A map used to hold the data being collected. </p>
   */

  private /*@ non_null @*/ Map data;

  // Constructors

  /**
   * <p> Construct a new <code>SimpleCollect</code> class. </p>
   */
  public SimpleCollect()
  {
    data = new ConcurrentHashMap();
  }

  // Inherited methods

  public Object clone() throws CloneNotSupportedException
  {
    try {
      return super.clone();
    } catch (CloneNotSupportedException cnse) {
      throw new RuntimeException(cnse.getMessage());
    }
  }

  /**
   * <p> Register a statistic with the collector. </p>
   *
   * @param statistic the statistic to register.
   */

  public void register(/*@ non_null @*/ Statistic statistic)
  {
    super.register(statistic);
    reset(statistic);

    /** ensure [statistic_registered] isRegistered(statistic); **/
  }

  /**
   * <p> Unregister a statistic with the collector. </p>
   *
   * @param statistic the statistic to unregister.
   */

  public void unregister(Statistic statistic)
  {
    super.unregister(statistic);
    data.remove(statistic);

    /** ensure [statistic_registered] !isRegistered(statistic); **/
  }

  /**
   * <p> What is the current value for specific statistic? </p>
   *
   * @param statistic the statistic being modified.
   * @return the old value of the statistic.
   */

  public double currentValue(/*@ non_null @*/ Statistic statistic)
  {
    return ((Double)data.get(statistic)).doubleValue();
  }

  /**
   * <p> Report on a particular statistic. </p>
   *
   * @param statistic the statistic being reported on.
   * @return a simple <code>String</code> textual report.
   */

  public Object report(Statistic statistic)
  {
    return "[" + statistic.getID() + "]" + 
     (((Double)data.get(statistic)).doubleValue() * statistic.getScale()) +
      " " + statistic.getUnits();
  }

  /**
   * <p> Report on all statistics. </p>
   *
   * @return a report on all statistics as a concatented
   * <code>String</code> textual report.
   * @see #report(Statistic)
   */

  public Object reportAll()
  {
    String fullReport = "";
    Iterator keys = data.keySet().iterator();

    while (keys.hasNext()) {
      fullReport = fullReport + report((Statistic)keys.next()) + "\n";
    }
    return fullReport;
  }

  /**
   * <p> Increment a statistic by a specified value. </p>
   *
   * @param statistic the statistic being modified.
   * @param value the amount to increment the statistic.
   * @return the old value of the statistic.
   */

  public double increment(Statistic statistic, double value)
  {
    double oldValue = currentValue(statistic);

    data.put(statistic, new Double(oldValue + value));
    return oldValue;
  }

  /**
   * <p> Increment a statistic by the default value. </p>
   *
   * @param statistic the statistic being modified.
   * @return the old value of the statistic.
   */

  public double increment(Statistic statistic)
  {
    double oldValue = currentValue(statistic);

    data.put(statistic, new Double(oldValue + statistic.getIncrement()));
    return oldValue;
  }

  /**
   * <p> Decrement a statistic by a specified value. </p>
   *
   * @param statistic the statistic being modified.
   * @param value the amount to decrement the statistic.
   * @return the old value of the statistic.
   */

  public double decrement(Statistic statistic, double value)
  {
    double oldValue = currentValue(statistic);

    data.put(statistic, new Double(oldValue - value));
    return oldValue;
  }

  /**
   * <p> Decrement a statistic by the default value. </p>
   *
   * @param statistic the statistic being modified.
   * @return the old value of the statistic.
   */

  public double decrement(Statistic statistic)
  {
    double oldValue = currentValue(statistic);

    data.put(statistic, new Double(oldValue + statistic.getDecrement()));
    return oldValue;
  }

  /**
   * <p> Reset a statistic to the default start value. </p>
   *
   * @param statistic the statistic to reset.
   * @return the old value of the statistic.
   */

  public double reset(Statistic statistic)
  {
    double oldValue = currentValue(statistic);

    data.put(statistic, new Double(statistic.getStart()));
    return oldValue;
  }

  /**
   * <p> Set a statistic to a specific value. </p>
   *
   * @param statistic the statistic being modified.
   * @param value the new value of the statistic.
   * @return the old value of the statistic.
   */

  public double set(Statistic statistic, double value)
  {
    double oldValue = currentValue(statistic);

    data.put(statistic, new Double(value));
    return oldValue;
  }

  // Public Methods
  // Protected Methods
  // Package Methods
  // Private Methods

} // end of class SimpleCollect

/*
 * Local Variables:
 * Mode: Java
 * fill-column: 75
 * End:
 */
