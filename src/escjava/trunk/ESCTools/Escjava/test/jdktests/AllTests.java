
import junit.framework.Test;
import junit.framework.TestSuite;

/*
 * This file is part of the Esc/Java2 project. Copyright 2004 David R.
 * Cok
 * 
 * Created on Feb 13, 2005
 */

/**
 * TODO Fill in class description
 * 
 * @author David R. Cok
 */
public class AllTests {

  public static void main(String[] args) {
    junit.textui.TestRunner.run(AllTests.suite());
  }

  public static Test suite() {
    TestSuite suite = new TestSuite("Test for default package");
    //$JUnit-BEGIN$
    suite.addTestSuite(TestThrowable.class);
    suite.addTestSuite(TestException.class);
    //$JUnit-END$
    return suite;
  }
}
