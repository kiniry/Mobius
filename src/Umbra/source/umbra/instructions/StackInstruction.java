/*
 * Created on 2005-05-19
 *
 */
package umbra.instructions;

import org.apache.bcel.generic.ALOAD;
import org.apache.bcel.generic.ASTORE;
import org.apache.bcel.generic.DLOAD;
import org.apache.bcel.generic.DSTORE;
import org.apache.bcel.generic.FLOAD;
import org.apache.bcel.generic.FSTORE;
import org.apache.bcel.generic.ILOAD;
import org.apache.bcel.generic.ISTORE;
import org.apache.bcel.generic.Instruction;
import org.apache.bcel.generic.LLOAD;
import org.apache.bcel.generic.LSTORE;

import umbra.UmbraHelper;
import umbra.editor.parsing.IBytecodeStrings;


/**
 * This class is related to some subset of instructions
 * depending on parameters. It redefines some crucial while
 * handling with single instruction methods(correctness, getting handle).
 * Load and store instrucions.
 *
 * @author Jarosław Paszek (jp209217@students.mimuw.edu.pl)
 * @version a-01
 */
public class StackInstruction extends NumInstruction {

  /**
   * This creates an instance of an instruction
   * named as <code>a_name</code> in a line the text of which is
   * <code>a_line</code>. Currently it just calls the constructor of the
   * superclass.
   *
   * @param a_line_text the line number of the instruction
   * @param a_name the mnemonic name of the instruction
   * @see InstructionLineController#InstructionLineController(String, String)
   */
  public StackInstruction(final String a_line_text, final String a_name) {
    super(a_line_text, a_name);
  }

  /**
   * Stack instruction line is correct if it has
   * one number parameter preceded with %.
   *
   *@see InstructionLineController#correct()
   */
  public final boolean correct()
  {
    String s;
    s = UmbraHelper.stripAllWhitespace(my_line_text);
    final String[] s2 = IBytecodeStrings.stack;
    int j;
    int y;
    if (s.indexOf("%") < s.indexOf(":") + 1)
      return false;
    for (j = 0; j < s2.length; j++) {
      if ((s.indexOf(s2[j]) > 0) && (s.indexOf(s2[j]) < s.indexOf(":") + 2))
        if (s.indexOf(s2[j]) + (s2[j].length()) + 1 > s.indexOf("%")) {
          for (y = (s.indexOf("%") + 1); y < s.length(); y++) {
            if (!(Character.isDigit(s.charAt(y))))
              return false;
          }
          int a, b, d, e, f, g;
          a = (s.length() - s.indexOf("%"));
          int c = 0;
          e = my_line_text.length() - my_line_text.indexOf("%");
          f = 0;
          g = my_line_text.length();
          for (d = 0; d < e; d++) {
            if (Character.isDigit(my_line_text.charAt(g - d - 1))) {
              f = 1;
            }
            if (f == 0) {
              if (Character.isWhitespace(my_line_text.charAt(g - d - 1))) {
                c++;
              }
            }
          }

          b = e - c;
          if (a == b)
            return true;
        }
    }
    return false;
  }


  /**
   * TODO
   */
  private int getInd() {
    boolean isd;
    final String licznik = "0123456789";
    int liczba;

    isd = true;
    int dokad = my_line_text.length();
    for (int i = my_line_text.lastIndexOf("%") + 1; i < my_line_text.length(); i++) {
      if (!Character.isDigit(my_line_text.charAt(i))) {
        dokad = i;
        break;
      }
    }
    if (isd) {
      liczba = 0;
      for (int i = my_line_text.lastIndexOf("%") + 1; i < dokad; i++) {
        liczba = 10 * liczba + licznik.indexOf(my_line_text.substring(i, i + 1));
      }
      return liczba;
    }
    return 0;
  }

  /**
   * TODO
   *
   * @see BytecodeLineController#getInstruction()
   */
  public final Instruction getInstruction() {
    int index = 0;
    Instruction res = null;
    //&*
    if (!correct())
      return null;
    index = getInd();

    if (name.compareTo("aload") == 0) {
      res = new ALOAD(index);
    }
    if (name.compareTo("astore") == 0) {
      res = new ASTORE(index);
    }
    if (name.compareTo("dload") == 0) {
      res = new DLOAD(index);
    }
    if (name.compareTo("dstore") == 0) {
      res = new DSTORE(index);
    }
    if (name.compareTo("fload") == 0) {
      res = new FLOAD(index);
    }
    if (name.compareTo("fstore") == 0) {
      res = new FSTORE(index);
    }
    if (name.compareTo("iload") == 0) {
      res = new ILOAD(index);
    }
    if (name.compareTo("istore") == 0) {
      res = new ISTORE(index);
    }
    if (name.compareTo("lload") == 0) {
      res = new LLOAD(index);
    }
    if (name.compareTo("lstore") == 0) {
      res = new LSTORE(index);
    }

    return res;
  }
}
