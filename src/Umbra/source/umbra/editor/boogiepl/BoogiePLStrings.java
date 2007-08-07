/*
 * @title       "BoogiePL in Umbra"
 * @description "BoobiePL support for Umbra bytecode editor"
 * @copyright   ""
 * @license     ""
 */
package umbra.editor.boogiepl;

/**
 * Some string arrays used to identify keywords and instruction
 * names in bytecode.
 *
 * @author Samuel Willimann (wsamuel@student.ethz.ch)
 * @version a-01
 */
public class BoogiePLStrings {

  /**
   * TODO.
   */
  public static final String[] INSTRUCTIONS = new String[] {"assume",
                                                            "assert", ":=",
                                                            "goto", "return",
                                                            "call",
                                                            "procedure",
                                                            "implementation",
                                                            "returns", "int",
                                                            "ref"};

  /**
   * TODO.
   */
  public static final String[] JUMP_INS = new String[] {"goto", "return"};

  /**
   * TODO.
   */
  public static final String[] CALL_INS = new String[] {"call"};

  /**
   * TODO.
   */
  public static final String[] UNARY_INS = new String[] {"assume", "assert"};

  /**
   * TODO.
   */
  public static final String[] BINARY_INS = new String[] {":="};

  /**
   * TODO.
   */
  public static final String[] BOOGIEPL_KEYWORDS =
                                            new String[] {"procedure",
                                                          "implementation",
                                                          "returns",
                                                          "int", "ref" };
}
