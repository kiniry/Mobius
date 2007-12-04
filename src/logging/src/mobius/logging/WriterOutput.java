/*
 * Software Engineering Tools.
 *
 * $Id: WriterOutput.jass,v 1.1.1.1 2002/12/29 12:36:17 kiniry Exp $
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
 * <p> The primary class used to send debugging messages to a
 * <code>PrintWriter</code> output channel. </p>
 *
 * @version alpha-0
 * @author Joseph R. Kiniry (kiniry@acm.org)
 * @concurrency (GUARDED) All methods are synchronized.
 * @see Context
 * @see Debug
 */

public class WriterOutput extends AbstractDebugOutputBase
  implements DebugOutput, Cloneable
{
  // Attributes

  /**
   * <p> The output channel used by this <code>WriterOutput</code>
   * object. </p>
   */
  private PrintWriter my_print_writer = new PrintWriter(System.err);

  // Constructors

  //@ assignable my_debug;
  //@ ensures my_debug == a_debug;
  /**
   * <p> Constructor for <code>WriterOutput</code>. </p>
   *
   * @param a_debug the <code>Debug</code> object associated with this
   * <code>WriterOutput</code>.
   */
  public WriterOutput(final Debug a_debug)
  {
    my_debug = a_debug;
  }

  //@ assignable my_debug, my_print_writer;
  //@ ensures my_debug == a_debug;
  //@ ensures getWriter() == a_print_writer;
  /**
   * <p> Constructor for <code>WriterOutput</code>. </p>
   *
   * @param a_debug the <code>Debug</code> class associated with this
   * <code>WriterOutput</code>.
   * @param a_print_writer the new <code>PrintWriter</code> for this
   * <code>WriterOutput</code>.
   */
  public WriterOutput(final Debug a_debug,
                      final PrintWriter a_print_writer)
  {
    my_debug = a_debug;
    my_print_writer = a_print_writer;
  }

  // Public Methods

  //@ assignable my_print_writer;
  //@ ensures getWriter() == the_new_print_writer;
  /**
   * <p> Set a new <code>PrintWriter</code>.
   *
   * @param the_new_print_writer the new <code>PrintWriter</code>.
   */
  public void setPrintWriter(final PrintWriter the_new_print_writer)
  {
    my_print_writer = the_new_print_writer;
  }

  // Inherited Methods

  /**
   * {@inheritDoc}
   * @modifies QUERY
   */
  public synchronized void printMsg(final String a_category, final String a_message)
  {
    my_print_writer.print("<" + a_category + ">: " + a_message);
    my_print_writer.flush();
  }

  /**
   * {@inheritDoc}
   * @modifies QUERY
   */
  public synchronized void printMsg(int a_level, String a_message)
  {
    my_print_writer.print("[" + a_level + "]: " + a_message);
    my_print_writer.flush();
  }

  /**
   * {@inheritDoc}
   * @modifies QUERY
   */
  public synchronized void printMsg(String a_message)
  {
    my_print_writer.print(a_message);
    my_print_writer.flush();
  }

  /**
   * {@inheritDoc}
   * @modifies QUERY
   */
  public /*@ pure @*/ synchronized Writer getWriter()
  {
    return my_print_writer;
  }

  /**
   * {@inheritDoc}
   * @modifies QUERY
   */
  public Object clone() throws CloneNotSupportedException
  {
    try {
      return super.clone();
    } catch (CloneNotSupportedException cnse) {
      throw new RuntimeException(cnse.getMessage());
    }
  }

  // Protected Methods
  // Package Methods
  // Private Methods

} // end of class WriterOutput

/*
 * Local Variables:
 * Mode: Java
 * fill-column: 75
 * End:
 */
