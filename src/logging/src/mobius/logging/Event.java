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
 * <p> Event is the type of all log/monitoring events. </p>
 *
 * @version alpha-1
 * @author Joseph Kiniry (kiniry@acm.org)
 * @bon Represents a single important event of any kind. The event includes
 * a source, description, importance, and time, among other things.
 */
//@ nullable_by_default
interface Event extends Serializable, Cloneable {

  // Public Methods

  /**
   * <p> What is the source system of this event? </p>
   *
   * @design Original examples show source host being a textual machine
   * name and/or port number, but this isn't a requirement.
   * @return the source system for this event.
   */
  String getSourceHost();

  /**
   * <p> What is the source component of this event? </p>
   *
   * @design Original examples show source component being a textual name
   * of a component and a version number, but this isn't a requirement.
   * @return the source component of this event.
   */
  String getSourceComponent();

  /**
   * <p> When was this event generated? </p>
   *
   * @return the time at which this event was generated.
   */
  Date getCreationDate();

  /**
   * <p> What is the description of this event? </p>
   *
   * @return the description of this event.
   */
  String getDescription();
  /**
   * <p> What type of event is this? </p>
   *
   * @return the type of this event.
   * @see DebugConstants
   */
  String getType();

  /**
   * <p> How important is this event? </p>
   *
   * @return the level of importance of this event.
   */
  int getLevel();

} // end of class Event

/*
 * Local Variables:
 * Mode: Java
 * fill-column: 75
 * End:
 */
