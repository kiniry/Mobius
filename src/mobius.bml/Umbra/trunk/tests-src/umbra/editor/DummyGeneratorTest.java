/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) 2006-2009 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.editor;

import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;

import org.apache.bcel.classfile.ConstantUtf8;
import org.junit.After;
import org.junit.Before;
import org.junit.Test;

import umbra.instructions.DummyGenerator;

/**
 * @author Tomasz Olejniczak (to236111@students.mimuw.edu.pl)
 * @version a-01
 *
 */
public class DummyGeneratorTest {

  private String lines[] = {
    "[[[[D", "J", "B", "[[Ljava/lang/Object;", "Ljava/lang/Object;"
  };
                          
  private String lines_incorrect[] = {
    "K", "L", "[[J[D", "[", "L/java;", "Ljava/lang/Object", "L3",
    "Ljava//lang/Object"
  };
  
  private DummyGenerator gen;

  /**
   *
   */
  @Before
  public void setUp() {
    gen = new DummyGenerator(null, null, null);
  }
                          
  /**
   *
   */
  @After
  public void tearDown() {

  }

  /**
   * Test method for {@link DummyGenerator#isFieldDescriptor()}.
   */
  @Test
  public void testConstantNumber() {
    for (int i = 0; i < lines.length; i++) {
      assertTrue("correct field descriptor, line number " + i,
        gen.isFieldDescriptor(new ConstantUtf8(lines[i])));
    }
    for (int i = 0; i < lines_incorrect.length; i++) {
      assertFalse("incorrect field descriptor, line number " + i,
        gen.isFieldDescriptor(new ConstantUtf8(lines_incorrect[i])));
    }
  }
  
}
