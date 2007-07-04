/*
 * Created on 2005-05-19
 *
 */
package umbra.instructions;

import org.apache.bcel.generic.INVOKESPECIAL;
import org.apache.bcel.generic.INVOKESTATIC;
import org.apache.bcel.generic.INVOKEVIRTUAL;
import org.apache.bcel.generic.Instruction;

import umbra.UmbraHelper;
import umbra.editor.parsing.IBytecodeStrings;


/**
 * This class is related to some subset of instructions
 * depending on parameters. It redefines some crucial while
 * handling with single instruction methods (correctness, getting handle).
 * Instructions of this kind are used to call other methods.
 *
 * @author Jarosław Paszek (jp209217@students.mimuw.edu.pl)
 * @version a-01
 */
public class InvokeInstruction extends StringInstruction {


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
  public InvokeInstruction(final String a_line_text, final String a_name) {
    super(a_line_text, a_name);
  }


  /**
   * Invoke instruction line is correct if its parameter
   * contains class name at the beginning and a number in ()
   * at the end.
   *
   *@see InstructionLineController#correct()
   */
  public final boolean correct()
  {
    String s;
    s = UmbraHelper.stripAllWhitespace(my_line_text);
    final String[] s2 = IBytecodeStrings.invoke;
    int j;
    for (j = 0; j < s2.length; j++) {
      if ((s.indexOf(s2[j]) > 0) && (s.indexOf(s2[j]) < s.indexOf(":") + 2))

        if (s.lastIndexOf("(") < 2) return false; //TODO is it all right
        if (s.lastIndexOf(")") < 2) return false;
        int m, n, o;
        m = my_line_text.lastIndexOf("(");
        n = my_line_text.lastIndexOf(")");
        if (m + 1 >= n) return false;
        for (o = m + 1; o < n; o++) {
          if (!(Character.isDigit(my_line_text.charAt(o)))) {
            return false;
          }
        }
        return true;
    }
    return false;
  }

  /**
   * TODO
   */
  private int getInd() {
    boolean isd;
    final String licznik = "0123456789";
    int number;
    if (my_line_text.lastIndexOf("(") < my_line_text.lastIndexOf(")")) {
      isd = true;
      for (int i = my_line_text.lastIndexOf("(") + 1; i < my_line_text.lastIndexOf(")"); i++) {
        if (!Character.isDigit(my_line_text.charAt(i))) {
          isd = false;
        }
      }
      if (isd) {
        number = 0;
        for (int i = my_line_text.lastIndexOf("(") + 1; i < my_line_text.lastIndexOf(")"); i++) {
          number = 10 * number + licznik.indexOf(my_line_text.substring(i, i + 1));
        }
        return number;
      }
    }
    return 0;
  }

  /**
   * @see BytecodeLineController#getInstruction()
   */
  public final Instruction getInstruction() {
  int index;
  index = getInd();

  if (!correct())
    return null;

  if (name.compareTo("invokespecial") == 0) {
    return new INVOKESPECIAL(index);
  }
  if (name.compareTo("invokestatic") == 0) {
    return new INVOKESTATIC(index);
  }
  if (name.compareTo("invokevirtual") == 0) {
    return new INVOKEVIRTUAL(index);
  }

  return null;

  }
}
