/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) 2006-2008 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.instructions;

import static org.junit.Assert.*;

import org.junit.Assert.*;

import org.junit.After;
import org.junit.AfterClass;
import org.junit.Before;
import org.junit.BeforeClass;
import org.junit.Test;

import umbra.instructions.ClassHeaderParser;
import umbra.instructions.ast.FieldInstruction;

/**
 * @author alx
 * @version a-01
 *
 */
public class ClassHeaderParserTest {

  /**
   * @throws java.lang.Exception
   */
  @BeforeClass
  public static void setUpBeforeClass() throws Exception {
  }

  /**
   * @throws java.lang.Exception
   */
  @AfterClass
  public static void tearDownAfterClass() throws Exception {
  }

  private ClassHeaderParser classtest;
  private ClassHeaderParser extendstest;
  private ClassHeaderParser implementstest;

  /**
   * @throws java.lang.Exception
   */
  @Before
  public void setUp() throws Exception {
    classtest = new ClassHeaderParser("class");
    extendstest = new ClassHeaderParser("extends Some");
    implementstest = new ClassHeaderParser("implements Some, java.lang.Some");
  }

  /**
   * @throws java.lang.Exception
   */
  @After
  public void tearDown() throws Exception {
  }

  /**
   * Test method for {@link umbra.instructions.ClassHeaderParser#swallowClass()}.
   */
  @Test
  public void testSwallowClass() {
    assertEquals(true, classtest.swallowClass());
  }

  /**
   * Test method for {@link umbra.instructions.ClassHeaderParser#swallowExtendsClause()}.
   */
  @Test
  public void testSwallowExtendsClause() {
    assertEquals(true, extendstest.swallowExtendsClause());
  }

  /**
   * Test method for {@link umbra.instructions.ClassHeaderParser#swallowImplementsClause()}.
   */
  @Test
  public void testSwallowImplementsClause() {
    assertEquals(true, implementstest.swallowImplementsClause());
  }

}
