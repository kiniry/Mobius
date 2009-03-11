/**
 * Copyright (c) 2007-2009, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.tests.testcase;

import ie.ucd.bon.Main;
import ie.ucd.bon.errorreporting.BONProblem;
import ie.ucd.bon.errorreporting.Problems;
import ie.ucd.bon.util.NullOutputStream;

import java.io.File;
import java.io.PrintStream;
import java.util.ArrayList;
import java.util.Collection;

public class TestCase {
  
  private String location;
  private String testName;
  private final Collection<String> inputFiles;
  private final Collection<TestOutput> outputs;
  private final Collection<String> progArgs;
  private final int testNumber;
    
  public TestCase(final int testNumber) {
    inputFiles = new ArrayList<String>();
    outputs = new ArrayList<TestOutput>();
    progArgs = new ArrayList<String>();
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
  
  public void addProgramArgument(String argument) {
    progArgs.add(argument);
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
  
  public boolean runTest() {
    StringBuilder runString = new StringBuilder("-tc ");
    for (String arg: progArgs) {
      runString.append(arg);
      runString.append(' ');
    }
    for (String inputFile : inputFiles) {
      runString.append(location);
      runString.append(inputFile);
      runString.append(' ');
    }    

    System.out.print("Test #" + testNumber);
    if (testName != null) {
      System.out.print(" (" + testName + ")");
    }
    System.out.println();
    //System.out.println("Runstring: *" + runString + "*");
    
    //We don't want to print any output from the test run
    PrintStream oldOut = System.out;
    PrintStream oldErr = System.err;
    //TODO It would probably be even faster to have a NullPrintStream here
    System.setOut(NullOutputStream.getNullPrintStreamInstance());
    System.setErr(NullOutputStream.getNullPrintStreamInstance());
    
    Main.main2(runString.toString().trim().split("\\s+"), false);

    System.setOut(oldOut);
    System.setErr(oldErr);
    
    Problems foundProblems = Main.getProblems();  
    Problems desiredProblems = new Problems();
    for (TestOutput out : outputs) {
      BONProblem problem = out.getProblem();
      if (problem != null) {
        desiredProblems.addProblem(problem);
      } 
    }

    boolean passed = foundProblems.testEquality(desiredProblems, System.out);
    if (!passed) {
      System.out.print("***Test #" + testNumber);
      if (testName != null) {
        System.out.print(" (" + testName + ")");
      }
      System.out.println(" failed.");
    } else {
      System.out.print("Test #" + testNumber);
      if (testName != null) {
        System.out.print(" (" + testName + ")");
      }
      System.out.println(" passed successfully.");
    }
    
    return passed;
  }
}
