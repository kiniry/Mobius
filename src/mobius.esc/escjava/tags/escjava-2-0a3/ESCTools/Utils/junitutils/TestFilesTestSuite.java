/*
 * Copyright (C) 2000-2001 Iowa State University
 *
 * This file is part of mjc, the MultiJava Compiler.
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307 USA
 *
 * $Id$
 * Author: David R. Cok
 */
package junitutils;
import junit.framework.*;
import java.io.*;
import java.util.ArrayList;
import java.util.Iterator;
import java.lang.reflect.Method;

/** This is a JUnit TestSuite that is created from a number of tests as follows.
    Each TestCase is an instance of the inner class Helper, instantiated with
    a name of a file.  The file names are read from the file named by the
    parameter 'fileOfTestFilenames'.  The argument to the constructor named
    'args' provides a set of command-line arguments; the filename for the TestCase
    is added on to the end of the list of command-line arguments.  Then the static
    compile method of the given class is called on those command-line arguments.
<P>
    The standard output and error output is captured from the execution of the
    compile method.  This is compared to the output in filename + "-expected".
    The TestCase succeeds if these match; if they do not match, the test fails and
    the actual output is saved in filename + "-ckd".
<P>
    The test must be run from the directory in which it resides - because
    it creates and opens files in the current directory.

    @author David R. Cok
*/
public class TestFilesTestSuite  extends TestSuite {

    protected TestFilesTestSuite() {}
    /*
    Create derived classes with alternate tests by deriving a class from this 
    one. It should contain an inner Helper class derived from 
    TestFilesTestSuite.Helper.  The method TestFilesTestSuite.makeHelper 
    should be overridden to return an instance of the derived Helper class.  
    The derived Helper class should override Helper.dotest to do the actual 
    test.
    */
    
    // -------------------------------------------------------------
    // DATA MEMBERS
    // -------------------------------------------------------------

    /** The name of this test suite. */
    protected String testName;

    /** The method that is to be executed on the command-line arguments. */
    protected Method method;

    final static String SAVED_SUFFIX = "-ckd";
    final static String ORACLE_SUFFIX = "-expected";

    // -------------------------------------------------------------
    // CONSTRUCTOR
    // -------------------------------------------------------------

    /** A constructor for this test suite.
	@param testName	The name of the test suite
	@param fileOfTestFilenames The file to be read for filenames of tests
	@param args	The command-line arguments that the static compile 
                        method will be applied to, with the filename added on
	@param cls	The class in which to find the static compile method
    */
    public TestFilesTestSuite(String testName, String fileOfTestFilenames,
				String[] args, // Ignored!
				Class cls
				) { 
	super(testName);
	this.testName = testName;
	try {
	    method = cls.getMethod("compile", new Class[] { String[].class });
	    //System.out.println("METHOD " + method);
	} catch (NoSuchMethodException e) {
	    throw new RuntimeException(e.toString());
        }

	try { 
	    Iterator i = new LineIterator(fileOfTestFilenames);
	    while (i.hasNext()) {
		String s = (String)i.next();
		String[] allargs = Utils.parseLine(s);
		s = allargs[allargs.length-1];
		addTest(makeHelper(s,allargs));	    
	    }
	} catch (java.io.IOException e) {
	    throw new RuntimeException(e.toString());
	}
    }


    /** Factory method for the helper class object. */
    protected Helper makeHelper(String filename, String[] args) {
	return new Helper(filename,args);
    }


    // FIXME - This test does not do the equivalent of FIXTILT or PATHTOFILES
    // that is performed in the Makefile to canonicalize the outputs.  So far we
    // have not needed it.

    /** This is a helper class that is actually a TestCase; it is run repeatedly
	with different constructor arguments.
    */
    public class Helper extends TestCase {
    
	/** 
	    The first argument is used as the name of the test as well as 
	    the name of the file to be tested.
	*/
	public Helper(String testname, String[] args) {
	    super(testname);
	    this.fileToTest = testname;
	    this.args = args;
	}
	
	/** Filename of comparison files */
	protected String fileToTest;

	/** Result of test */
	protected Object returnedObject;

	/** Command-line arguments (including filename) for this test. */
	protected String[] args;
    
	/** This is the framework around the test.  It sets up the streams to
	    capture output, and catches all relevant exceptions.
	*/
	public void runTest() throws java.io.IOException {
	    //System.out.println("\nTest suite " + testName + ": "  + fileToTest);
	    //for (int kk=0; kk<args.length; ++kk) System.out.println(args[kk]);
	    //System.out.println();
    
	    PrintStream ps = null;
	    ByteArrayOutputStream ba = new ByteArrayOutputStream(10000);
	    try {
		// Redirect the output to a file, and then do the compile
		ps = new PrintStream(ba);
		Utils.setStreams(ps);
		
		returnedObject = dotest(fileToTest,args);
		
	    } catch (IllegalAccessException e) {
		Utils.restoreStreams();
		fail(e.toString());
	    } catch (IllegalArgumentException e) {
		Utils.restoreStreams();
		fail(e.toString());
	    } catch (java.lang.reflect.InvocationTargetException e) {
		Utils.restoreStreams();
		java.io.StringWriter sw = new StringWriter();
		sw.write(e.toString());
		e.printStackTrace(new PrintWriter(sw));
		fail(sw.toString());
	    } catch (Throwable e) {  // THIS JUST FOR DEBUG
		Utils.restoreStreams(); // Have to have this before the use of System.out on the next line
		System.out.println(e);
		e.printStackTrace();
	    } finally {
		Utils.restoreStreams();
		if (ps != null) ps.close();
	    }
	    String err = doOutputCheck(fileToTest,ba.toString(),returnedObject);
	    if (err != null) fail(err);
	    //System.out.println("COMPLETED: " + fileToTest);
	}
    }
     
    /** This is the actual test; it compiles the given file and compares its 
	output to the expected result (in fileToTest+ORACLE_SUFFIX); the 
	output is expected to 
	match and the result of the compile to be true or false, depending on
	whether errors or warnings were reported.  Override this method in derived tests.
	
	@param ba contains stuff written to the output stream in this test
    */
    protected Object dotest(String fileToTest, String[] args) 
	    throws IllegalAccessException, IllegalArgumentException, 
			    java.lang.reflect.InvocationTargetException {
					    
	return method.invoke(null,new Object[]{args});
    }
	    
    
    protected String doOutputCheck(String fileToTest, String output, 
				Object returnedValue) {
      try {
	String expectedOutput = Utils.readFile(fileToTest+ORACLE_SUFFIX);
	Diff df = new Diff("expected", expectedOutput, "actual", output);

	if (!df.areDifferent()) {
	    // If the two strings match, the test succeeds and we make sure
	    // that there is no -ckd file to confuse anyone.
	    (new File(fileToTest+SAVED_SUFFIX)).delete();
	} else {
	    // If the strings do not match, we save the actual string and
	    // fail the test.
	    FileWriter f = new FileWriter(fileToTest+SAVED_SUFFIX);
	    f.write(output);
	    f.close();
	    
	    return (df.result());
	}
	return checkReturnValue(fileToTest,expectedOutput,returnedValue);
      } catch (java.io.IOException e) { 
	return (e.toString()); 
      }
    }

    public String checkReturnValue(String fileToTest, String expectedOutput,
					Object returnedValue) {
	if (returnedValue instanceof Boolean) {
		return expectedStatusReport(fileToTest,
				((Boolean)returnedValue).booleanValue(),
				expectedOutput);
        } else if (returnedValue instanceof Integer) {
		return expectedStatusReport(fileToTest,
				((Integer)returnedValue).intValue(),
				expectedOutput);
        } else {
	    return ("The return value is of type " + returnedValue.getClass()
		+ " instead of int or boolean");
        }
    }


    /** Returns null if ok, otherwise returns failure message. */
    public String expectedStatusReport(String fileToTest,
				int ecode, String expectedOutput) {
	int ret = expectedIntegerStatus(fileToTest,expectedOutput);
	if (ecode == ret) return null;
	return "The compile produced an invalid return value.  It should be " + ret + " but instead is " + ecode;
    }

    public String expectedStatusReport(String fileToTest,
				boolean b, String expectedOutput) {
	boolean status = expectedBooleanStatus(fileToTest,expectedOutput);
	if (status == b) return null;
	return ("The compile produced an invalid return value.  It should be "
		+ (!b) + " since there was " +
		(b?"no ":"") + "error output but instead is " + b);
    }

    public boolean expectedBooleanStatus(String fileToTest, String expectedOutput) {
	return expectedOutput.length()==0;
    }

    public int expectedIntegerStatus(String fileToTest, String expectedOutput) {
	return 0;
    }

}


