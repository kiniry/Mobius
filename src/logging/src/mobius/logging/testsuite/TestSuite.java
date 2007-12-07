/*
 * Software Engineering Tools.
 *
 * $Id: TestSuite.jass,v 1.1.1.1 2002/12/29 12:36:19 kiniry Exp $
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

package mobius.logging.testsuite;

/**
 * <p> TestSuite is a black-box test suite for the Debug class. </p>
 *
 * <p> This program accepts the following arguments:
 * <dl>
 *  <dt><sample>--console</sample></dt>
 *  <dd>Exercise the <code>ConsoleOutput</code> implementation of the
 *      <code>DebugOutput</code> interface.  This is the default test
 *      mode.</dd>
 *  <dt><sample>--servletlog</sample></dt>
 *  <dd>Exercise the <code>ServletLogOutput</code> implementation of the
 *      <code>DebugOutput</code> interface.</dd>
 *  <dt><sample>--window</sample></dt>
 *  <dd>Exercise the <code>WindowOutput</code> implementation of the
 *      <code>DebugOutput</code> interface.</dd>
 *  <dt><sample>--writer</sample></dt>
 *  <dd>Exercise the <code>WriterOutput</code> implementation of the
 *      <code>DebugOutput</code> interface.</dd>
 * </dl>
 * </p>
 *
 * <p> If TestSuite is not passed any parameters then the default test mode
 * will be executed (currently, ConsoleOutput). </p>
 *
 * @version alpha-1
 * @author Joseph R. Kiniry (kiniry@acm.org)
 *
 * @history Tests originally were located in a main() method of the
 * Debug class.  They were moved to this class as of version 0.15 (or
 * so) of Debug to reduce Debug's (already large) code size.  The
 * tests were then rewritten to conform to the new debug interface as
 * of debug version 0.18.  Real version is (0.05 + Id - 1) at this
 * point in time.  Switches to test different DebugOutput implementations
 * were added in v1.3 of this class.
 * @design The success boolean is a running indicator of the success
 * of the test suite.  The return value of every method in Debug is
 * checked and and-ed, as appropriate, with success.  I.e. If any one
 * such method returns a value we didn't expect, we would be and-ing
 * with a false and the final value would be a false.
 *
 * @note The top-level class of the IDebug test suite.
 */
//@ non_null_by_default
public class TestSuite {
  // Attributes
  // Constructors
  // Inherited Methods
  // Public Methods

  /**
   * A main() that contains the test code for the Debug class.
   *
   * @param the_arguments the arguments passed to this program from the command-line.
   * @design Since the debug package now is non-static, we have to
   * start up our own thread of control.
   */
  public static void main(final String [] the_arguments) {
    // Check for --help argument.
    if (showHelp(the_arguments))
      System.exit(0);

    // Check for --version argument.
    if (showVersion(the_arguments))
      System.exit(0);

    // Check validity of test mode argument.
    String the_test_mode = null;
    try {
      the_test_mode = testArgs(the_arguments);
    } catch (IllegalArgumentException iae) {
      System.err.println("Illegal argument: " + iae.getMessage());
      System.err.println("Run with the '--help' argument for help.");
      System.exit(-1);
    }

    // Run tests.
    final TestSuiteThread the_test_suite_thread = new TestSuiteThread(the_test_mode);
    the_test_suite_thread.start();
  }

  // Protected Methods
  // Package Methods
  // Private Methods

  /**
   * Find first use of a legal test mode string in parameter list and
   * return it.  If no legal string exists and the argument list is
   * non-null, throw an <code>IllegalArgumentException</code>.  Otherwise, return
   * the default test mode string "console".
   *
   * @param the_arguments the arguments passed to this program from the command-line.
   * @return a string representing which test mode is in operation.
   */
  private static String testArgs(final String [] the_arguments) {
    if (the_arguments == null)
      return "console";
    if (the_arguments.length == 0)
      return "console";

    for (int i = 0; i < the_arguments.length; i++) {
      if (the_arguments[i].equals("--console") ||
          the_arguments[i].equals("--servletlog") ||
          the_arguments[i].equals("--window") ||
          the_arguments[i].equals("--writer"))
        return the_arguments[i].substring("--".length());
    }
    throw new IllegalArgumentException("Argument list is non-null and " +
                         "erroneous.\nUse --help for more information.");
  }

  /**
   * <p> Test parameter list <code>argv</code> for string "--version".  If
   * this string exists then show a version message via System.out
   * and return the value true.  Otherwise, return a false.
   *
   * @param argv the arguments passed to this program from the command-line.
   * @return true iff we have shown the version information on the console.
   * @postcondition (("--version" in argv) implies show version info)
   * @postcondition (Result == ("--version" in argv))
   */
  private static boolean showVersion(String [] argv) {
    if (argv == null)
      return false;
    if (argv.length == 0)
      return false;

    for (int i = 0; i < argv.length; i++) {
      if (argv[i].indexOf("--version") != -1) {
        System.out.println("The Mobius Logging test suite.\n");
        System.out.println("Copyright (c) 1997-2007 Joseph Kiniry");
        System.out.println("Copyright (c) 2000-2001 KindSoftware, LLC");
        System.out.println("Copyright (c) 1997-1999 " +
                           "California Institute of Technology");
        System.out.println("Copyright (c) 2007 University College Dublin");
        System.out.println("All rights reserved.");
        System.out.println("See accompanying LICENSE files for more " +
                           "information.");
        return true;
      }
    }
    return false;
  }

  /**
   * <p> Test parameter list <code>argv</code> for string "--help".  If
   * this string exists in the parameter then show a help message on
   * System.out and return the value true.  Otherwise, return a false.
   *
   * @param argv the arguments passed to this program from the command-line.
   * @return true iff a help message ws printed.
   * @postcondition (("--help" in argv) implies show help)
   * @postcondition (Result == ("--help" in argv))
   */
  private static boolean showHelp(String [] argv) {
    if (argv == null)
      return false;
    if (argv.length == 0)
      return false;

    for (int i = 0; i < argv.length; i++) {
      if (argv[i].indexOf("--help") != -1) {
        System.out.println("Usage: TestSuite [TESTOPTION]...");
        System.out.println("Test the IDebug debugging framework according to TESTOPTION.");
        System.out.println("Example: java idebughc.testsuite.TestSuite --window\n");
        System.out.println("TESTOPTION is exactly one of the following:");
        System.out.println("  --console      " +
                           "exercise the ConsoleOutput implementation of the");
        System.out.println("                 " +
                           "DebugOutput interface.  This is the default test mode.");
        System.out.println("  --servletlog   exercise the ServletLogOutput implementation");
        System.out.println("  --window       exercise the WindowOutput implementation");
        System.out.println("  --writer       exercise the WriterOutput implementation\n");
        System.out.println("Miscellaneous:");
        System.out.println("  --version      print version information and exit");
        System.out.println("  --help         display help and exit");
        return true;
      }
    }
    return false;
  }

  // Inner Classes

}
// end of class TestSuite

/*
 * Local Variables:
 * Mode: Java
 * fill-column: 75
 * End:
 */

