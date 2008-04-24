/**
 * 2008, Systems Research Group, University College Dublin
 * https://mobius.ucd.ie/wiki/ParallelTesting
 * 
 * This test suite only runs on my local machine and not on the usual test 
 * servers; it is used only to debug and find memory leaks in the test
 * infrastructure and is not part of the continuous integration cycle i.e. this
 * is used to 'test' the tests.
 */

import java.util.Iterator;
import java.util.Random;

import junit.framework.*;
import junitutils.*;

public class MemoryLeakTest extends junitutils.TestFilesTestSuite {

  static public junit.framework.Test suite() {

    String hostName = "";
    try {
      java.net.InetAddress localMachine = java.net.InetAddress.getLocalHost();
      hostName = localMachine.getHostName();
    } catch (java.net.UnknownHostException uhe) {
      throw new RuntimeException(uhe.toString());
    }
    //@ assert 0 < hostName.length();

    String listOfFiles = "src/test/list.txt";
    String listOfOptions = "src/test/options.txt";
    String listOfSecondOptions = "src/test/secondOptions.txt";
    String testSuiteName = "MemoryLeakTest-" + hostName;
    int numberOfServers = 0;
    int serverIndex = -1; // run no tests unless a server is found 

    // Add your hostname here if you need to debug the tests on your local
    // server. This needs to be a server that is available for testing and is
    // not being used for other essential services such as mail, LDAP or SVN.
    if (hostName.equalsIgnoreCase("voting.ucd.ie")) {
      numberOfServers = 1;
      serverIndex = 0;
    }

    junit.framework.TestSuite suite = new AbstractDistributedTestSuite(
                                                                       testSuiteName,
                                                                       listOfFiles,
                                                                       listOfOptions,
                                                                       listOfSecondOptions,
                                                                       escjava.Main.class,
                                                                       serverIndex,
                                                                       numberOfServers) {
      public int expectedIntegerStatus(String f, String o) {
        if (javafe.util.ErrorSet.errors > 0)
          return 2;

        return 0;
      }

      public String expectedStatusReport(String fileToTest, int ecode,
                                         String expectedOutput) {
        int ret = expectedIntegerStatus(fileToTest, expectedOutput);
        if ((ecode > 0) == (ret > 0))
          return null;
        return super.expectedStatusReport(fileToTest, ecode, expectedOutput);
      }
    };
    return suite;
  }
}
