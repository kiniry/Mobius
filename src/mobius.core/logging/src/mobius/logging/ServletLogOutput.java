/*
 * Software Engineering Tools.
 *
 * $Id: ServletLogOutput.jass,v 1.1.1.1 2002/12/29 12:36:15 kiniry Exp $
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

import java.io.InputStream;
import java.io.Writer;
import java.net.MalformedURLException;
import java.net.URL;
import java.util.Enumeration;
import java.util.Set;

import javax.servlet.*;

/**
 * <p> The class used to send debugging messages from within Java
 * servlets. </p>
 *
 * @version alpha-1
 * @author Joseph R. Kiniry (kiniry@acm.org)
 * @concurrency (GUARDED) All methods are synchronized.
 */
//+@ nullable_by_default
/*#thread_shared*/ public class ServletLogOutput extends AbstractDebugOutputBase
  implements DebugOutput, Cloneable {
  // Attributes

  /**
   * <p> The <code>ServletContext</code> instance associated with this
   * instance of ServletLogOutput. </p>
   */
  private transient final /*@ non_null spec_public @*/ ServletContext my_servlet_context;

  // Constructors

  /**
   * <p> Construct a new <code>ServletLogOutput</code> object for debugging
   * purposes. A dummy <code>ServletContext</code> will be created and
   * output will go to <code>System.err</code>. </p>
   *
   * @param the_debug the <code>Debug</code> class associated with this
   * <code>ServletLogOutput</code>.
   */
  //@ ensures my_servlet_context != null;
  //@ ensures my_debug == the_debug;
  public ServletLogOutput(final /*@ non_null @*/ Debug the_debug) {
    super();
    my_debug = the_debug;
    my_servlet_context = new DummyServletContext();
  }

  /**
   * <p> Construct a new <code>ServletLogOutput</code> object. </p>
   *
   * @param the_debug the <code>Debug</code> class associated with this
   * <code>ServletLogOutput</code>.
   * @param the_servlet_context the <code>ServletContext</code> associated with this instance
   * of <code>ServletLogOutput</code>.
   */
  //@ ensures my_debug == the_debug;
  //@ ensures my_servlet_context == the_servlet_context;
  public
  ServletLogOutput(final /*@ non_null @*/ Debug the_debug,
                   final /*@ non_null @*/ ServletContext the_servlet_context) {
    super();
    my_debug = the_debug;
    my_servlet_context = the_servlet_context;
  }

  // Inherited Methods

  /**
   * {@inheritDoc}
   */
  public /*@ non_null */ Object clone() throws CloneNotSupportedException {
    try {
      return super.clone();
    } catch (CloneNotSupportedException cnse) {
      throw new RuntimeException(cnse.getMessage(), cnse);
    }
  }

  /**
   * {@inheritDoc}
   */
  public synchronized void printMsg(final /*@ non_null */ String a_category,
                                    final String a_message) {
    my_servlet_context.log("<" + a_category + ">: " + a_message);
  }

  /**
   * {@inheritDoc}
   */
  public synchronized void printMsg(final int a_level, final String a_message) {
    my_servlet_context.log("[" + a_level + "]: " + a_message);
  }

  /**
   * {@inheritDoc}
   */
  public synchronized void printMsg(final String a_message) {
    my_servlet_context.log(a_message == null ? "null" : a_message);
  }

  /**
   * {@inheritDoc}
   */
  public synchronized Writer getWriter() {
    return null;
  }

  // Public Methods
  // Protected Methods
  // Package Methods
  // Private Methods
  // Inner Classes

  /**
   * <p> <code>DummyServletContext</code> is a dummy placeholder
   * <code>ServletContext</code> used during white and blackbox testing.  It
   * includes just enough code so that utilization of <code>log()</code> and
   * <code>getRealPath()</code> work.  All other methods return
   * <code>null</code>. </p>
   *
   * @history This class comes from the Jiki.
   */
  private static class DummyServletContext implements ServletContext {
    /** A default empty constructor. */
    DummyServletContext() {
      super();
    }
    /** {@inheritDoc} */
    public Servlet getServlet(final String a_servlet_name) throws ServletException {
      return null;
    }
    /** {@inheritDoc} */
    public Enumeration getServlets() {
      return null;
    }
    /** {@inheritDoc} */
    public Enumeration getServletNames() {
      return null;
    }
    /** {@inheritDoc} */
    public void log(final String a_msg) {
      System.err.print(a_msg);
    }
    /** {@inheritDoc} */
    public void log(final Exception an_exception, final String a_msg) {
      System.err.print(a_msg);
      if (an_exception != null)
        an_exception.printStackTrace(System.err);
    }
    /** {@inheritDoc} */
    public String getRealPath(final String a_path) {
      return a_path;
    }
    /** {@inheritDoc} */
    public String getMimeType(final String a_file) {
      return null;
    }
    /** {@inheritDoc} */
    public String getServerInfo() {
      return "DummyServletContext, originally a part of Jiki " +
        "- http://www.jiki.org/.";
    }
    /** {@inheritDoc} */
    public Object getAttribute(final String a_name) {
      return null;
    }
    /** {@inheritDoc} */
    public Enumeration getAttributeNames() {
      // todo Auto-generated method stub
      return null;
    }
    /** {@inheritDoc} */
    public ServletContext getContext(final String the_context_name) {
      // todo Auto-generated method stub
      return null;
    }
    /** {@inheritDoc} */
    public String getInitParameter(final String the_parameter_name) {
      // todo Auto-generated method stub
      return null;
    }
    /** {@inheritDoc} */
    public Enumeration getInitParameterNames() {
      // todo Auto-generated method stub
      return null;
    }
    /** {@inheritDoc} */
    public int getMajorVersion() {
      // todo Auto-generated method stub
      return 0;
    }
    /** {@inheritDoc} */
    public int getMinorVersion() {
      // todo Auto-generated method stub
      return 0;
    }
    /** {@inheritDoc} */
    public RequestDispatcher getNamedDispatcher(final String the_dispatcher_name) {
      // todo Auto-generated method stub
      return null;
    }
    /** {@inheritDoc} */
    public RequestDispatcher getRequestDispatcher(final String the_dispatcher_name) {
      // todo Auto-generated method stub
      return null;
    }
    /** {@inheritDoc} */
    public URL getResource(final String the_resource_name) throws MalformedURLException {
      // todo Auto-generated method stub
      return null;
    }
    /** {@inheritDoc} */
    public InputStream getResourceAsStream(final String the_resource_name) {
      // todo Auto-generated method stub
      return null;
    }
    /** {@inheritDoc} */
    public Set getResourcePaths(final String the_resource_name) {
      // todo Auto-generated method stub
      return null;
    }
    /** {@inheritDoc} */
    public String getServletContextName() {
      // todo Auto-generated method stub
      return null;
    }
    /** {@inheritDoc} */
    public void log(final String the_message, final Throwable a_throwable) {
      // todo Auto-generated method stub
    }
    /** {@inheritDoc} */
    public void removeAttribute(final String the_attribute) {
      // todo Auto-generated method stub
    }
    /** {@inheritDoc} */
    public void setAttribute(final String the_attribute, final Object a_value) {
      // todo Auto-generated method stub
    }
  }
} // end of class ServletLogOutput

/*
 * Local Variables:
 * Mode: Java
 * fill-column: 75
 * End:
 */
