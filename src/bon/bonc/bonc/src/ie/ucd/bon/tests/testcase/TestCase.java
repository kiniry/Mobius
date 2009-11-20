/**
 * Copyright (c) 2007-2009, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.tests.testcase;

import ie.ucd.bon.Main;
import ie.ucd.bon.errorreporting.BONProblem;
import ie.ucd.bon.errorreporting.Problems;

import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.PrintStream;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.LinkedList;
import java.util.List;

public class TestCase {

  private String location;
  private String testName;
  private final Collection<String> inputFiles;
  private final Collection<TestOutput> outputs;
  private List<String> progArgs;
  private final int testNumber;

  public TestCase(final int testNumber) {
    inputFiles = new ArrayList<String>();
    outputs = new ArrayList<TestOutput>();
    progArgs = new LinkedList<String>();
    this.testNumber = testNumber;
    location = null;
    testName = null;
  }

  public void setLocation(String location) {
    this.location = location;
  }

  public void setTestName(String testName) {
    this.testName = testName;
  }

  public void addInputFile(String input) {
    inputFiles.add(input);
  }

  public void addOutput(TestOutput to) {
    outputs.add(to);
  }

  public void setProgramArguments(String arguments) {
    String[] args = arguments.split("\\s+");
    progArgs = Arrays.asList(args);
  }

  public boolean checkValid() {
    boolean valid = true;

    if (!new File(location).exists()) {
      System.out.println("Error: Input location " + location + " is not valid.");
      return false;
    }

    for (String inputFile : inputFiles) {
      if (!new File(location + inputFile).exists()) {
        System.out.println("Error: " + inputFile + " does not exist");
        valid = false;
      }
    }

    return valid;
  }

  public boolean runTest(PrintStream out, PrintStream err) {
    StringBuilder runString = new StringBuilder();
    for (String arg : progArgs) {
      runString.append(arg);
      runString.append(' ');
    }
    for (String inputFile : inputFiles) {
      runString.append(location);
      runString.append(inputFile);
      runString.append(' ');
    }

    //We don't want to print any output from the test run
    PrintStream oldOut = System.out;
    PrintStream oldErr = System.err;
    //It would probably be even faster to have a NullPrintStream here
    System.setOut(out);
    System.setErr(err);

    String runStringS = runString.toString().trim();
    Problems foundProblems;
    if (runStringS.equals("")) {
      foundProblems = Main.main2(new String[0], false);
    } else {
      foundProblems = Main.main2(runStringS.split("\\s+"), false);
    }

    System.setOut(oldOut);
    System.setErr(oldErr);

    if (foundProblems == null) {
      //Avoid NPE
      foundProblems = new Problems("Test(Found)");
    }
    Problems desiredProblems = new Problems("Test(Desired)");
    for (TestOutput output : outputs) {
      BONProblem problem = output.getProblem();
      if (problem != null) {
        desiredProblems.addProblem(problem);
      }
    }
    
    ByteArrayOutputStream baos = new ByteArrayOutputStream();

    boolean passed = foundProblems.testEquality(desiredProblems, new PrintStream(baos));
    if (!passed) {
      System.out.print("***Test #" + testNumber);
      if (testName != null) {
        System.out.print(" (" + testName + ")");
      }
      System.out.println(" failed.");
      System.out.println(baos.toString());
      System.out.println("****************************************");
    }

    return passed;
  }

  @Override
  public String toString() {
    return testName + ", " + testNumber + ", " + progArgs + ", " + outputs;
  }
}
