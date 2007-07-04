/*
 * Created on 2005-05-19
 *
 */
package umbra.instructions;

import org.apache.bcel.generic.GETFIELD;
import org.apache.bcel.generic.GETSTATIC;
import org.apache.bcel.generic.Instruction;
import org.apache.bcel.generic.PUTFIELD;
import org.apache.bcel.generic.PUTSTATIC;

import umbra.UmbraHelper;
import umbra.editor.parsing.IBytecodeStrings;


/**
 * This class is related to some subset of instructions
 * depending on parameters. It redefines some crucial while
 * handling with single instruction methods (correctness, getting handle).
 * This subset is similar to ordinary Java subset.
 *
 * @author Jarosław Paszek (jp209217@students.mimuw.edu.pl)
 * @version a-01
 */
public class FieldInstruction extends StringInstruction {

  /**
   * This creates an instance of an instruction
   * named as <code>a_name</code> in a line the text of which is
   * <code>a_line_text</code>. Currently it just calls the constructor of the
   * superclass.
   *
   * @param a_line_text the line number of the instruction
   * @param a_name the mnemonic name of the instruction
   * @see InstructionLineController#InstructionLineController(String, String)
   */
  public FieldInstruction(final String a_line_text, final String a_name) {
    super(a_line_text, a_name);
  }


  /**
   * Field instruction line is correct if its
   * parameter contains a number in ().
   *
   *@see InstructionLineController#correct()
   */
  public final boolean correct()
  {
    String s;
    s = UmbraHelper.stripAllWhitespace(my_line_text);
    final String[] s2 = IBytecodeStrings.field;
    int j;
    for (j = 0; j < s2.length; j++) {
      if ((s.indexOf(s2[j]) > 0) && (s.indexOf(s2[j]) < s.indexOf(":") + 2)) {

        if (s.lastIndexOf("(") < 2) return false;
        if (s.lastIndexOf(")") < 2) return false;
        int m, n, o;
        m = my_line_text.lastIndexOf("(");
        n = my_line_text.lastIndexOf(")");
        //UmbraPlugin.messagelog(m + " " + n + " " + my_line_text);
        if (m + 1 >= n) return false;
        for (o = m + 1; o < n; o++) {
          if (!(Character.isDigit(my_line_text.charAt(o)))) {
            return false;
          }
        }

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
    if (my_line_text.lastIndexOf("(") < my_line_text.lastIndexOf(")")) {
      isd = true;
      for (int i = my_line_text.lastIndexOf("(") + 1; i < my_line_text.lastIndexOf(")"); i++) {
        if (!Character.isDigit(my_line_text.charAt(i))) {
          isd = false;
        }
      }
      if (isd) {
        liczba = 0;
        for (int i = my_line_text.lastIndexOf("(") + 1; i < my_line_text.lastIndexOf(")"); i++) {
          liczba = 10 * liczba + licznik.indexOf(my_line_text.substring(i, i + 1));
        }
        return liczba;
      }
    }
    return 0;
  }

  /**
   * TODO
   *
   * @see BytecodeLineController#getInstruction()
   */
  public final Instruction getInstruction() {
    int index;
    index = getInd();

    final boolean isOK = correct();
    if (isOK) {
      if (name.compareTo("getfield") == 0) {
        return new GETFIELD(index);
      }
      if (name.compareTo("getstatic") == 0) {
        return new GETSTATIC(index);
      }
      if (name.compareTo("putfield") == 0) {
        return new PUTFIELD(index);
      }
      if (name.compareTo("putstatic") == 0) {
        return new PUTSTATIC(index);
      }
    }
    return null;
  }
}
