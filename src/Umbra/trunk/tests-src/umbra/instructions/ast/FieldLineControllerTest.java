/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) 2006-2008 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.instructions.ast;

import static org.junit.Assert.*;

import org.junit.After;
import org.junit.Before;
import org.junit.Test;

/**
 * @author alx
 * @version a-01
 *
 */
public class FieldLineControllerTest {


  String[] lines = {
      "private  int[] keyIds;",
  };

  FieldLineController[] instructions;
  
  /**
   * @throws java.lang.Exception
   */
  @Before
  public void setUp() throws Exception {
    instructions = new FieldLineController[lines.length];
    for (int i = 0; i < lines.length; i++) {
      instructions[i] = new FieldLineController(lines[i]);
    }
  }

  /**
   * @throws java.lang.Exception
   */
  @After
  public void tearDown() throws Exception {
  }

  /**
   * Test method for {@link umbra.instructions.ast.FieldLineController#correct()}.
   */
  @Test
  public void testCorrect() {
    for (int i = 0; i < lines.length; i++) {
      assertTrue("line number " + i, instructions[i].correct());
    }
  }

  /**
   * Test method for {@link umbra.instructions.ast.FieldLineController#isFieldLineStart(java.lang.String)}.
   */
  @Test
  public void testIsFieldLineStart() {
    for (int i = 0; i < lines.length; i++) {
      assertTrue("filed line start for number " + i,
                 FieldLineController.isFieldLineStart(instructions[i].
                                                        getLineContent()));
    }
  }

}
