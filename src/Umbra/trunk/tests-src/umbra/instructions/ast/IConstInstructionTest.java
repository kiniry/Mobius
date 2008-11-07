package umbra.instructions.ast;


import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

import org.apache.bcel.generic.Instruction;
import org.junit.After;
import org.junit.Before;
import org.junit.Test;

import umbra.lib.BytecodeStrings;

/**
 * @author alx
 * @version a-01
 *
 */
public class IConstInstructionTest {

  
  private IConstInstruction instr;
  
  private static String instrname = "iconst_0";
  private static String line = 
    "22:   iconst_0";
  
  /**
   * @throws java.lang.Exception
   */
  @Before
  public void setUp() throws Exception {
    instr = new IConstInstruction(line, instrname);
  }

  /**
   * @throws java.lang.Exception
   */
  @After
  public void tearDown() throws Exception {
    instr = null;
  }

  /**
   * Test method for {@link umbra.instructions.ast.IConstInstruction#getInstruction()}.
   */
  @Test
  public void testGetInstruction() {
    Instruction bcel = instr.getInstruction();
    assertEquals(instrname, bcel.getName());
  }

  /**
   * Test method for {@link umbra.instructions.ast.IConstInstruction#correct()}.
   */
  @Test
  public void testCorrect() {
    assertEquals(true, instr.correct());
  }

  /**
   * Test method for {@link umbra.instructions.ast.IConstInstruction#getMnemonics()}.
   */
  @Test
  public void testGetMnemonics() {
    final String [] strings = IConstInstruction.getMnemonics();
    for (int i = 0; i < BytecodeStrings.ICONST_INS.length; i++) {
      assertEquals(true, BytecodeStrings.ICONST_INS[i].equals(strings[i]));
    }
  }

  /**
   * Test method for {@link umbra.instructions.ast.IConstInstruction#IConstInstruction(java.lang.String, java.lang.String)}.
   */
  @Test
  public void testIConstInstruction() {
    assertTrue(instr.getName().equals(instrname));
  }

}
