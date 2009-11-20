/**
 * Copyright (c) 2007-2009, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.tests;

import ie.ucd.bon.tests.testcase.TestCase;
import ie.ucd.bon.util.NullOutputStream;

import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.PrintStream;
import java.util.Collection;

import org.antlr.runtime.ANTLRInputStream;
import org.antlr.runtime.CommonTokenStream;
import org.antlr.runtime.Lexer;
import org.antlr.runtime.RecognitionException;

public class Tester {

  public static void test(String testsDir, String testCasesFile, String logFile) throws IOException, RecognitionException {
    FileInputStream fis = new FileInputStream(testCasesFile);
    ANTLRInputStream input = new ANTLRInputStream(fis);
    Lexer lexer = new TesterLexer(input);
    CommonTokenStream tokens = new CommonTokenStream(lexer);
    TesterParser parser = new TesterParser(tokens);
    parser.setTestsDir(testsDir);
    parser.testGrammar();
    fis.close();

    PrintStream logs;
    if (logFile == null) {
      logs = NullOutputStream.getNullPrintStreamInstance();
    } else {
      logs = new PrintStream(new FileOutputStream(logFile));
    }

    Collection<TestCase> testCases = parser.getTestCases();

    int countFailed = 0;
    for (TestCase testCase : testCases) {
      if (!testCase.runTest(logs, logs)) {
        countFailed++;
      }
    }

    int countPassed = testCases.size() - countFailed;

    System.out.println("***** All tests completed. *************");
    System.out.println("****************************************");
    System.out.println("Summary:");
    System.out.println("\tTests Passed: " + countPassed);
    System.out.println("\tTests Failed: " + countFailed);
    if (logFile != null) {
      logs.flush();
      logs.close();
      System.out.println("\tLogfile created at: " + logFile);
    }
  }

  public static void main(String[] args) {
    if (args.length != 2 && args.length != 3) {
      System.out.println("Invalid arguments for running tests. Usage: java ie.ucd.bon.test.Tester <test-dir> <test-file> [<log-file> <clops-log-file>]");
    } else {
      try {
        if (args.length == 2) {
          test(args[0], args[1], null);
        } else {
          test(args[0], args[1], args[2]);
        }
      } catch (Exception e) {
        System.out.println("Error processing test file: " + args[1]);
        e.printStackTrace();
      }
    }
  }

}
