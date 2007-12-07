/*
 * Software Engineering Tools.
 *
 * $Id: FailedAssertionException.jass,v 1.1.1.1 2002/12/29 12:36:15 kiniry Exp $
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

/**
 * <p> The runtime exception thrown when an assertion is violated. </p>
 *
 * @version alpha-1
 * @author Joseph R. Kiniry (kiniry@acm.org)
 * @see Assert
 */
//@ nullable_by_default
public class FailedAssertionException extends Error {
  // Attributes
  // Constructors

  /** A placeholder serialVersionUID. */
  private static final long serialVersionUID = 1L;

  /** Create a new, empty exception. */
  public FailedAssertionException() {
    super();
  }

  /**
   * Create a new exception with the given message.
   *
   * @param a_message the message to embed in the exception.
   */
  public FailedAssertionException(final String a_message) {
    super(a_message);
  }

  // Inherited Methods
  // Public Methods
  // Protected Methods
  // Package Methods
  // Private Methods

} // end of class FailedAssertionException

/*
 * Local Variables:
 * Mode: Java
 * fill-column: 75
 * End:
 */
