/*
 * Software Engineering Tools.
 *
 * $Id: TestSuiteThread.jass,v 1.1.1.1 2002/12/29 12:36:20 kiniry Exp $
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

import mobius.logging.*;

/**
 * <p> TestSuite is the black-box testsuite for the Debug class. </p>
 *
 * @version alpha-1
 * @author Joseph R. Kiniry (kiniry@acm.org)
 *
 * @note The actual code of the IDebug test suite.
 */
//@ non_null_by_default
public class TestSuiteThread extends Thread {
  // Attributes

  /** A flag used to track the success or failure of all tests in this class. */
  private boolean my_success = true;
  /** Which test mode are we in? */
  private String my_test_mode;

  // Constructors

  /**
   * Create a new TestSuiteThread with the specified test mode.
   *
   * @param the_test_mode the test mode for this test suite thread.  Exactly one
   * of the following strings: "console", "servletlog", "window", "writer".
   */
  /*@ requires (tm.equals("console") || tm.equals("servletlog") ||
    @          tm.equals("window") || tm.equals("writer"));
    @ ensures testMode == tm;
    @*/
  TestSuiteThread(final String the_test_mode) {
    super();
    this.my_test_mode = the_test_mode;
  }

  // Inherited Methods
  // Public Methods

  /** {@inheritDoc} */
  public void run() {
    final Debug the_debug = new Debug();

    System.out.println("TESTING MOBIUS LOGGING PACKAGE.\n");
    System.out.println("Using test mode " + my_test_mode + ".\n");

    System.out.println("Class-global testing\n" +
                       "====================");

    // Collect all the necessary references to the debugging modules.

    // Assert assert = debug.getAssert();
    final DebugConstants the_debug_constants = the_debug.getDebugConstants();

    // Build the appropriate DebugOutput implementation depending upon the
    // value of testMode.
    DebugOutput the_debug_output = null;
    if (my_test_mode.equals("console")) {
      the_debug_output = new ConsoleOutput(the_debug);
    } else if (my_test_mode.equals("servletlog")) {
      the_debug_output = new ServletLogOutput(the_debug);
    } else if (my_test_mode.equals("window")) {
      the_debug_output = new WindowOutput(the_debug);
    } else if (my_test_mode.equals("writer")) {
      the_debug_output = new WriterOutput(the_debug);
    } else
      throw new RuntimeException("Illegal test mode: " + my_test_mode);

    // Set up the output interface of our debug instance.
    the_debug.setOutputInterface(the_debug_output);

    // First we will test the default configuration (console output,
    // no new levels or categories.

    // Class-global testing.

    // Test 0
    my_success &= (!the_debug_output.println(the_debug_constants.ASSERTION_LEVEL, "FAILED"));
    if (!my_success)
      System.err.println("FALURE #0");
    // Test 1
    my_success &= (!the_debug_output.println(the_debug_constants.ASSERTION, "FAILED"));
    if (!my_success)
      System.err.println("FALURE #1");

    the_debug.turnOn();
    // Test 2
    my_success &= the_debug_output.println(the_debug_constants.FAILURE_LEVEL, "PASSED");
    if (!my_success)
      System.err.println("FALURE #2");

    // Test 3
    my_success &= the_debug_output.println(the_debug_constants.FAILURE, "PASSED");
    if (!my_success)
      System.err.println("FALURE #3");

    // Test 4
    the_debug.setLevel(the_debug_constants.LEVEL_MIN - 1);
    my_success &= (the_debug.getLevel() != (the_debug_constants.LEVEL_MIN - 1));
    if (!my_success)
      System.err.println("FALURE #4");

    the_debug.setLevel(the_debug_constants.ERROR_LEVEL);

    // Test 5
    my_success &= (!the_debug_output.println(the_debug_constants.ERROR_LEVEL - 1, "FAILED"));
    if (!my_success)
      System.err.println("FALURE #5");

    // Test 6
    my_success &= (!the_debug_output.println(the_debug_constants.WARNING, "FAILED"));
    if (!my_success)
      System.err.println("FALURE #6");

    // Test 7
    my_success &= the_debug_output.println(the_debug_constants.ERROR_LEVEL, "PASSED");
    if (!my_success)
      System.err.println("FALURE #7");

    // Test 8
    my_success &= the_debug_output.println(the_debug_constants.ERROR, "PASSED");
    if (!my_success)
      System.err.println("FALURE #8");

    // Test 9
    my_success &= the_debug_output.println(the_debug_constants.ERROR_LEVEL + 1, "PASSED");
    if (!my_success)
      System.err.println("FALURE #9");

    // Test 10
    my_success &= the_debug_output.println(the_debug_constants.CRITICAL, "PASSED");
    if (!my_success)
      System.err.println("FALURE #10");

    // Test 11
    my_success &= the_debug_output.println(the_debug_constants.ASSERTION_LEVEL, "PASSED");
    if (!my_success)
      System.err.println("FALURE #11");

    // Test 12
    my_success &= the_debug_output.println(the_debug_constants.ASSERTION, "PASSED");
    if (!my_success)
      System.err.println("FALURE #12");

    // Test 13
    the_debug.setLevel(the_debug_constants.LEVEL_MAX + 1);
    my_success &= (the_debug.getLevel() != (the_debug_constants.LEVEL_MIN + 1));
    if (!my_success)
      System.err.println("FALURE #13");

    the_debug.setLevel(0);

    // Test 14
    my_success &= the_debug_output.println(0, "PASSED");
    if (!my_success)
      System.err.println("FALURE #14");

    // Test 15
    my_success &= the_debug_output.println(the_debug_constants.NOTICE_LEVEL, "PASSED");
    if (!my_success)
      System.err.println("FALURE #15");

    // Test 16
    my_success &= the_debug_output.println(the_debug_constants.NOTICE, "PASSED");
    if (!my_success)
      System.err.println("FALURE #16");

    // Test 17
    my_success &= the_debug_output.println(the_debug_constants.ASSERTION_LEVEL, "PASSED");
    if (!my_success)
      System.err.println("FALURE #17");

    // Test 18
    my_success &= the_debug_output.println(the_debug_constants.ASSERTION, "PASSED");
    if (!my_success)
      System.err.println("FALURE #18");

    // Test 19
    final int network_six_level = 6;
    my_success &= the_debug.addCategory("NETWORK_6", network_six_level);
    if (!my_success)
      System.err.println("FALURE #19");

    // Test 20
    final int network_five_level = 5;
    my_success &= the_debug.addCategory("NETWORK_5", network_five_level);
    if (!my_success)
      System.err.println("FALURE #20");

    // Test 21
    final int network_four_level = 4;
    my_success &= the_debug.addCategory("NETWORK_4", network_four_level);
    if (!my_success)
      System.err.println("FALURE #21");

    // Test 22
    the_debug.setLevel(network_five_level);
    // System.err.println("FALURE #22");

    // Test 23
    my_success &= the_debug_output.println(network_five_level, "PASSED");
    if (!my_success)
      System.err.println("FALURE #23");

    // Test 24
    my_success &= the_debug_output.println("NETWORK_5", "PASSED");
    if (!my_success)
      System.err.println("FALURE #24");

    // Test 25
    my_success &= (!the_debug_output.println("NETWORK_4", "FAILED"));
    if (!my_success)
      System.err.println("FALURE #25");

    // Test 26
    my_success &= the_debug_output.println("NETWORK_6", "PASSED");
    if (!my_success)
      System.err.println("FALURE #26");

    // Test 27
    my_success &= the_debug.removeCategory("NETWORK_5");
    if (!my_success)
      System.err.println("FALURE #27");

    // Test 28
    my_success &= (!the_debug_output.println("NETWORK_5", "FAILED"));
    if (!my_success)
      System.err.println("FALURE #28");

    // Test 29
    my_success &= !the_debug_output.println(the_debug_constants.LEVEL_MIN - 1, "FAILED");
    if (!my_success)
      System.err.println("FALURE #29");

    // Test 30
    my_success &= !the_debug_output.println(the_debug_constants.LEVEL_MAX + 1, "FAILED");
    if (!my_success)
      System.err.println("FALURE #30");

    the_debug.turnOff();

    System.out.println("\nPer-thread testing\n" +
                       "====================");

    // Per-thread testing begins.

    final Context the_debug_context =
      new Context(new DefaultDebugConstants(),
                  new ConsoleOutput(the_debug));

    // Note that we have turned off global debugging, so all of the
    // following is testing the case when a thread has debugging on
    // and global debugging is off.  A bit later, we'll turn global
    // debugging back on and the various "fall-back" scenarios.

    the_debug_context.turnOn();

    the_debug_context.setLevel(the_debug_constants.ERROR_LEVEL);

    // Test 31
    my_success &= the_debug_context.addCategory("PERTHREAD-1",
                                        the_debug_constants.ERROR_LEVEL - 1);
    if (!my_success)
      System.err.println("FALURE #31");

    // Test 32
    my_success &= the_debug_context.addCategory("PERTHREAD+1",
                                        the_debug_constants.ERROR_LEVEL + 1);
    if (!my_success)
      System.err.println("FALURE #32");

    // Install the new context.

    the_debug.addContext(the_debug_context);

    // Test 33
    my_success &= the_debug_output.println(the_debug_constants.ERROR_LEVEL, "SUCCESS");
    if (!my_success)
      System.err.println("FALURE #33");

    // Test 34
    my_success &= the_debug_output.println(the_debug_constants.ERROR_LEVEL + 1, "SUCCESS");
    if (!my_success)
      System.err.println("FALURE #34");

    // Test 35
    my_success &= (!the_debug_output.println(the_debug_constants.ERROR_LEVEL - 1, "FAILURE"));
    if (!my_success)
      System.err.println("FALURE #35");

    // Test 36
    my_success &= (!the_debug_output.println("PERTHREAD-1", "FAILURE"));
    if (!my_success)
      System.err.println("FALURE #36");

    // Test 37
    my_success &= the_debug_output.println("PERTHREAD+1", "SUCCESS");
    if (!my_success)
      System.err.println("FALURE #37");

    // Test 38
    the_debug_context.setLevel(the_debug_constants.ERROR_LEVEL - 1);
    // System.err.println("FALURE #38");

    // Test 39
    my_success &= the_debug_output.println(the_debug_constants.ERROR_LEVEL + 1, "SUCCESS");
    if (!my_success)
      System.err.println("FALURE #39");

    // Test 40
    my_success &= the_debug_output.println(the_debug_constants.ERROR_LEVEL - 1, "SUCCESS");
    if (!my_success)
      System.err.println("FALURE #40");

    // Test 41
    my_success &= the_debug_output.println("PERTHREAD-1", "SUCCESS");
    if (!my_success)
      System.err.println("FALURE #41");

    // Test 42
    my_success &= the_debug_output.println("PERTHREAD+1", "SUCCESS");
    if (!my_success)
      System.err.println("FALURE #42");

    // Now, we'll turn back on global debugging and try some tricky
    // combinations.

    the_debug.turnOn();

    // Global level is where we left it (5).  Current thread level is
    // ERROR_LEVEL-1, which is 4.  So, let's change the global to
    // ERROR_LEVEL and the per-thread to CRITICAL_LEVEL and see if we
    // can still get a rise out of the system.

    the_debug.setLevel(the_debug_constants.ERROR_LEVEL);
    the_debug_context.setLevel(the_debug_constants.CRITICAL_LEVEL);

    // Test 43
    my_success &= the_debug_output.println(the_debug_constants.CRITICAL, "SUCCESS");
    if (!my_success)
      System.err.println("FALURE #43");

    // Test 44
    my_success &= (!the_debug_output.println(the_debug_constants.NOTICE, "FAILURE"));
    if (!my_success)
      System.err.println("FALURE #44");

    // Test 45
    // This should succeed because the global level is ERROR_LEVEL.
    my_success &= the_debug_output.println(the_debug_constants.ERROR, "SUCCESS");
    if (!my_success)
      System.err.println("FALURE #45");

    // Test 46
    my_success &= the_debug_output.println(the_debug_constants.FAILURE, "SUCCESS");
    if (!my_success)
      System.err.println("FALURE #46");

    // End of tests
    System.out.println("Testing concluded.");

    final int end_of_test_pause_time_in_milliseconds = 30000;
    if (my_success) {
      System.out.println("Debugging tests succeeded!\n\n");
      if (my_test_mode.equals("window"))
        try {
          Thread.currentThread().sleep(end_of_test_pause_time_in_milliseconds);
        } catch (InterruptedException ie) {
          ; // empty
        }
      System.exit(0);
    } else {
      System.out.println("Debugging tests failed!\n\n");
      System.exit(-1);
    }

  } // end of inner class DummyServletContext

  // Protected Methods
  // Package Methods
  // Private Methods
  // Inner Classes

}
// end of class TestSuiteThread

/*
 * Local Variables:
 * Mode: Java
 * fill-column: 75
 * End:
 */
