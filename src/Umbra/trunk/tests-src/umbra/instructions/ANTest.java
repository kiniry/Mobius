/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) 2006-2009 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.instructions;

import static org.junit.Assert.assertTrue;

import org.junit.After;
import org.junit.Before;
import org.junit.Test;

/**
 * @author Tomasz Olejniczak (to236111@students.mimuw.edu.pl)
 * @version a-01
 *
 */
public class ANTest {

  
  private String lines[] = {
    "2.1",
    "2e+5",
    ".23",
    "3.",
    "+.34E-2",
    "-0.324e4546",
    "00.3424",
    "-2.e3f",
    "2.d",
    "-3D",
    "4d",
  };
  
  private String lines_incorrect[] = {
    "2e+",
    "34",
    "34E",
    "-e4546",
    ".f",
    "765.e-f"
  };
  
  private AN automaton;
  
  /**
   * @throws java.lang.Exception
   */
  @Before
  public void setUp() throws Exception {
    automaton = AN.constructAutomaton();
  }
  
  /**
   * @throws java.lang.Exception
   */
  @After
  public void tearDown() {
    
  }
  
  /**
   * Test method for {@link umbra.instructions.ast.FloatCPLineController#correct()}.
   * Note that automaton recognizes the number "3.-4" as 3. (correct).
   */
  @Test
  public void testCorrect() {
    for (int i = 0; i < lines.length; i++) {
      assertTrue("correct lines, ins number " + i, automaton.exec(lines[i], 0));
    }
    for (int i = 0; i < lines_incorrect.length; i++) {
      assertTrue("incorrect lines, ins number " + i,
                 !automaton.exec(lines_incorrect[i], 0));
    }
  }

  
}
