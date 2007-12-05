/*
 * Software Engineering Tools.
 *
 * $Id: ConsoleOutput.jass,v 1.1.1.1 2002/12/29 12:36:09 kiniry Exp $
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

import java.io.PrintWriter;
import java.io.Writer;

/**
 * <p> The primary class used to send debugging messages to the Java
 * console via the stderr file descriptor. </p> 
 *
 * @version $Revision: 1.1.1.1 $ $Date: 2002/12/29 12:36:09 $
 * @author Joseph R. Kiniry (kiniry@acm.org)
 * @concurrency (GUARDED) All methods are synchronized.
 * @see Context
 * @see Debug
 */
//@ non_null_by_default
public class ConsoleOutput extends AbstractDebugOutputBase 
  implements DebugOutput, Cloneable
{
  // Attributes

  // Constructors

  /**
   * <p> Construct a new ConsoleOutput class. </p>
   *
   * @param the_debug the Debug class associated with this ConsoleOutput.
   */
  //@ assignable my_debug;
  //@ ensures my_debug == the_debug;
  public ConsoleOutput(final /*@ non_null @*/ Debug the_debug) {
    super();
    my_debug = the_debug;
  }

  // Inherited Methods

  /** {@inheritDoc} */
  public synchronized void printMsg(String category, String message) {
    System.err.print("<" + category + ">: " + message);
  }

  /** {@inheritDoc} */
  public synchronized void printMsg(int level, String message) {
    System.err.print("[" + level + "]: " + message);
  }

  /** {@inheritDoc} */
  public synchronized void printMsg(String message) {
    System.err.print(message);
  }

  /** {@inheritDoc} */
  public synchronized /*@ non_null @*/ Writer getWriter() {
    return new PrintWriter(System.err, true);
  }

  /** {@inheritDoc} */
  public Object clone() throws CloneNotSupportedException {
    try {
      return super.clone();
    } catch (CloneNotSupportedException cnse) {
      throw new RuntimeException(cnse.getMessage(), cnse);
    }
  }

  // Public Methods
  // Protected Methods
  // Package Methods
  // Private Methods

} // end of class ConsoleOutput

/*
 * Local Variables:
 * Mode: Java
 * fill-column: 75
 * End:
 */
