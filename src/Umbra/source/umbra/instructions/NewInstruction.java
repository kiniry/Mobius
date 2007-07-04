/*
 * Created on 2005-05-19
 *
 */
package umbra.instructions;

import org.apache.bcel.generic.ANEWARRAY;
import org.apache.bcel.generic.CHECKCAST;
import org.apache.bcel.generic.INSTANCEOF;
import org.apache.bcel.generic.Instruction;
import org.apache.bcel.generic.NEW;

import umbra.UmbraHelper;
import umbra.editor.parsing.IBytecodeStrings;

/**
 * This class is related to some subset of instructions
 * depending on parameters. It redefines some crucial while
 * handling with single instruction methods(correctness, getting handle).
 * This is a set of various instructions with class name
 * as a parameter.
 *
 * @author Jarosław Paszek (jp209217@students.mimuw.edu.pl)
 * @version a-01
 */
public class NewInstruction extends StringInstruction {


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
  public NewInstruction(final String a_line_text, final String a_name) {
    super(a_line_text, a_name);
  }


  /**
   * New instruction line is correct if it has
   * one parameter that is a class name and
   * another one that is a number in ().
   *
   *@see InstructionLineController#correct()
   */
  public final boolean correct()
  {
    String s;
    s = UmbraHelper.stripAllWhitespace(my_line_text);
    final String[] s2 = IBytecodeStrings.anew;
    int j, y;
    for (j = 0; j < s2.length; j++) {
      if ((s.indexOf(s2[j]) > 0) && (s.indexOf(s2[j]) < s.indexOf(":") + 2)) {
        //zakladam ze zawsze z (number)
        // w <char lub java.costam> wiec tez nie wiadomo co
        if (s.indexOf("<") < 2) return false;
        if (s.indexOf(">") < 2) return false;
        //&*poprawiam
        if (s.lastIndexOf("(") < 2) return false;
        if (s.lastIndexOf(")") < 2) return false;
        int m, n, o;
        m = my_line_text.lastIndexOf("(");
        n = my_line_text.lastIndexOf(")");
        if (m + 1 >= n) {
          return false;
        }
        for (o = m + 1; o < n; o++) {
          if (!(Character.isDigit(my_line_text.charAt(o)))) {
            return false;
          }
        }

        //to dziala dla wszystkich moze by tak isLetter||.
        for (y = (s.indexOf("<") + 1); y < s.indexOf(">"); y++) {
          if (!(Character.isDefined(s.charAt(y)))) return false;
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
    int number;
    if (my_line_text.lastIndexOf("(") < my_line_text.lastIndexOf(")")) {
      isd = true;
      for (int i = my_line_text.lastIndexOf("(") + 1; i < my_line_text.lastIndexOf(")"); i++) {
        if (!Character.isDigit(my_line_text.charAt(i))) {
          //UmbraPlugin.messagelog("to nie jest cyfra zle ");
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
    if (!correct())
      return null;
    index = getInd();
    if (name.compareTo("anewarray") == 0) {
      return new ANEWARRAY(index);
    }
    if (name.compareTo("checkcast") == 0) {
      return new CHECKCAST(index);
    }
    if (name.compareTo("instanceof") == 0) {
      return new INSTANCEOF(index);
    }
    if (name.compareTo("new") == 0) {
      return new NEW(index);
    }
    return null;
  }
}
