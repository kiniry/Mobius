/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) 2006-2009 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.instructions.ast;

import junit.framework.Test;
import junit.framework.TestSuite;

/**
 * @author Tomasz Olejniczak (to236111@students.mimuw.edu.pl)
 * @version a-01
 *
 */
public class CPAllTests {

  public static Test suite() {
    TestSuite suite =
      new TestSuite("Test for umbra.instructions.ast (constant pool parsing)");
    //$JUnit-BEGIN$
    suite.addTestSuite(NameAndTypeCPLineControllerTest.class);
    suite.addTestSuite(IntegerCPLineControllerTest.class);
    suite.addTestSuite(StringCPLineControllerTest.class);
    suite.addTestSuite(MethodrefCPLineControllerTest.class);
    suite.addTestSuite(Utf8CPLineControllerTest.class);
    suite.addTestSuite(LongCPLineControllerTest.class);
    suite.addTestSuite(DoubleCPLineControllerTest.class);
    suite.addTestSuite(InterfaceMethodrefCPLineControllerTest.class);
    suite.addTestSuite(FloatCPLineControllerTest.class);
    suite.addTestSuite(FieldrefCPLineControllerTest.class);
    suite.addTestSuite(ClassCPLineControllerTest.class);
    //$JUnit-END$
    return suite;
  }

}
