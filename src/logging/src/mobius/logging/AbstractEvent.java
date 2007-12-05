/*
 * Software Engineering Tools.
 *
 * $Id: Event.jass,v 1.1.1.1 2002/12/29 12:36:15 kiniry Exp $
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
import java.util.Date;

/**
 * <p> Event is a utility base class from which all log/monitoring events
 * can derive or have embedded. </p>
 *
 * @version alpha-1
 * @author Joseph Kiniry (kiniry@acm.org)
 * @bon Represents a single important event of any kind. The event includes
 * a source, description, importance, and time, among other things.
 *
 * @concurrency (CONCURRENT) All methods are getters, thus there are no
 * concurrency issues.
 * @modifies (SINGLE-ASSIGNMENT-FIELDS) All attributes are set only on
 * construction.
 * @modifies (QUERY-METHODS) All methods are functions.
 *
 * @design The class invariants covers the legal values of all attributes,
 * thus no values tag is necessary in the specification.
 * @design Events cannot be cloned.
 */
//@ non_null_by_default
public abstract class AbstractEvent extends Object implements Serializable, Cloneable
{
  // Attributes

  /**
   * The source host for this event.
   *
   * @see #getSourceHost
   * @example sourceHost = "joe.kindsoftware.com"
   */
  private final String my_source_host;

  /**
   * The source component for this event.
   *
   * @see #getSourceComponent
   * @example sourceComponent = "Monitoring System, version 0.1.0"
   */
  private final String my_source_component;

  /**
   * The date on which this event was created.
   *
   * @see #getCreationDate
   */
  private final Date my_creation_date;

  /**
   * The text description of this event.
   *
   * @see #getDescription
   * @example description = "Available memory is beneath 1.0 MB."
   */
  private final String my_description;

  /**
   * The "type" of this event.
   *
   * @see #getType
   * @example type = "MEMORY_WARNING"
   */
  private final String my_type;

  /**
   * The "level" of this event.
   *
   * @see #getLevel
   * @see DebugConstants
   * @example level = debugConstants.WARNING
   */
  private final int my_level;

  // Constructors

  /**
   * <p> This the standard constructor for Event.  No other constructor can
   * be legally used. </p>
   *
   * @param the_source_host The source host for the event.
   * @param the_source_component The source component for the event.
   * @param the_description An English description of the event.
   * @param the_event_type The type of the event.
   * @param the_event_level The level of the event.
   *
   * @bon Create a new event with the following specification.
   * @ensures Result.getCreationDate() returns a time that is between the
   * time in which this method is called and it returns.
   * @generates A new, valid instance of Event.
   */
  //@ ensures \result.getSourceHost().equals(the_source_host);
  //@ ensures \result.getSourceComponent().equals(the_source_component);
  //@ ensures \result.getCreationDate() != null;
  //@ ensures \result.getDescription().equals(the_description);
  //@ ensures \result.getType().equals(the_event_type);
  //@ ensures \result.getLevel() == the_event_level;
  public AbstractEvent(final /*@ non_null @*/ String the_source_host,
                       final /*@ non_null @*/ String the_source_component,
                       final /*@ non_null @*/ String the_description,
                       final /*@ non_null @*/ String the_event_type,
                       final int the_event_level) {
    super();
    this.my_source_host = the_source_host;
    this.my_source_component = the_source_component;
    this.my_creation_date = new Date();
    this.my_description = the_description;
    this.my_type = the_event_type;
    this.my_level = the_event_level;
  }

  // Inherited methods

  /**
   * <p> What is a printable representation of this event? </p>
   *
   * @ensures Result = "[short-date/time-form | sourceHost |
   *                     sourceComponent] type : level -\n\tDescription"
   * @overrides java.lang.Object.toString()
   * @return a printable representation of the event.
   * @complexity O(1) - Note that String catenation is very expensive, so
   * use this method sparingly.  Also, the length of the output is directly
   * proportional to the event description. 
   */

  public String toString()
  {
    return "[" + my_creation_date.toString() + " | " + my_source_host + " | " +
      my_source_component + "] " + my_type + ":" + my_level + " - " + my_description;
  }

  // @todo kiniry Implement hashCode.
  public int hashCode() {
    assert false;
    //@ assert false;
    return 0;
  }

  /**
   * <p> Is this event equal to another one? </p>
   *
   * @param obj the event with which to compare.
   * @return if two Events are equal.
   * @ensures (Result == true) iff 
   *          (for_all attributes of Event : attributes of the objects
   *          being compared have identical values)
   * @overrides java.lang.Object.equals()
   */
  //@ requires (obj instanceof Event);
  public boolean equals(/*@ non_null @*/ Object obj) {
    if (obj instanceof AbstractEvent) {
      AbstractEvent an_event = (AbstractEvent)obj;
      return (my_source_host.equals(an_event.getSourceHost()) &&
       my_source_component.equals(an_event.getSourceComponent()) && 
       my_creation_date.equals(an_event.getCreationDate()) &&
       my_description.equals(an_event.getDescription()) && 
       my_type.equals(an_event.getType()) && my_level == an_event.getLevel());
    } else return false;
  }

  public Object clone() throws CloneNotSupportedException {
    try {
      return super.clone();
    } catch (CloneNotSupportedException cnse) {
      throw new RuntimeException(cnse.getMessage(), cnse);
    }
  }

  // Public Methods

  /**
   * <p> What is the source system of this event? </p>
   *
   * @design Original examples show source host being a textual machine
   * name and/or port number, but this isn't a requirement.
   * @return the source system for this event.
   */
  
  public String getSourceHost()
  {
    return my_source_host;
  }
  
  /**
   * <p> What is the source component of this event? </p>
   *
   * @design Original examples show source component being a textual name
   * of a component and a version number, but this isn't a requirement.
   * @return the source component of this event.
   */
  
  public String getSourceComponent()
  {
    return my_source_component;
  }

  /**
   * <p> When was this event generated? </p>
   *
   * @return the time at which this event was generated.
   */
  
  public Date getCreationDate()
  {
    return my_creation_date;
  }

  /**
   * <p> What is the description of this event? </p>
   *
   * @return the description of this event.
   */
  
  public String getDescription()
  {
    return my_description;
  }

  /**
   * <p> What type of event is this? </p>
   *
   * @return the type of this event.
   * @see DebugConstants
   */
  
  public String getType()
  {
    return my_type;
  }

  /**
   * <p> How important is this event? </p>
   *
   * @return the level of importance of this event.
   */
  
  public int getLevel()
  {
    return my_level;
  }

  // Protected Methods
  // Package Methods
  // Private Methods
} // end of class Event

/*
 * Local Variables:
 * Mode: Java
 * fill-column: 75
 * End:
 */
