/*
 * Created on 2005-04-30
 */
package umbra.editor.boogiepl;

/**
 * Some string arrays used to identify keywords and instruction
 * names in bytecode
 *
 * @author Samuel Willimann
 */
public interface IBoogiePLStrings {

  /**
   * TODO
   */
  String[] instructions = new String[] { "assume", "assert", ":=", "goto", "return", "call",
                             "procedure", "implementation", "returns", "int", "ref"};

  /**
   * TODO
   */
  String[] jump = new String[] { "goto", "return" };

  /**
   * TODO
   */
  String[] call = new String[] { "call" };

  /**
   * TODO
   */
  String[] unary = new String[] { "assume", "assert" };

  /**
   * TODO
   */
  String[] binary = new String[] { ":=" };

  /**
   * TODO
   */
  String[] boogiePLKeywords = new String[] { "procedure", "implementation", "returns", "int", "ref" };
}
