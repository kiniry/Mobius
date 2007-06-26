/*
 * Created on 2005-05-19
 *
 */
package umbra.instructions;

import org.apache.bcel.generic.Instruction;
import org.apache.bcel.generic.LDC;
import org.apache.bcel.generic.LDC2_W;
import org.apache.bcel.generic.LDC_W;

import umbra.UmbraHelper;
import umbra.UmbraPlugin;
import umbra.editor.parsing.IBytecodeStrings;


/**
 * This class is related to some subset of instructions
 * depending on parameters. It redefines some crucial while
 * handling with single instruction methods(correctness, getting handle).
 * These instruction are dealing with long data.
 *
 * @author Jarosław Paszek (jp209217@students.mimuw.edu.pl)
 * @version a-01
 */
public class LdcInstruction extends OtherInstruction {


  /**
   * TODO
   */
  public LdcInstruction(final String l, final String n) {
    super(l, n);
  }

  /**
   * TODO
   */
  private int getInd() {
    boolean isd;
    final String licznik = "0123456789";
    int number;
    if (line.lastIndexOf("(") >= line.lastIndexOf(")")) {
      UmbraPlugin.messagelog("linia jest niepoprawna nic nie tworzy " + line.lastIndexOf("(") + " " + line.lastIndexOf(")"));
    } else {
      isd = true;
      for (int i = line.lastIndexOf("(") + 1; i < line.lastIndexOf(")"); i++) {
        if (!Character.isDigit(line.charAt(i))) {
          isd = false;
        }
      }
      if (isd) {
        number = 0;
        for (int i = line.lastIndexOf("(") + 1; i < line.lastIndexOf(")"); i++) {
          number = 10 * number + licznik.indexOf(line.substring(i, i + 1));
        }
        return number;
      }
    }
    return 0;
  }

  /**
   * TODO
   * @see BytecodeLineController#getInstruction()
   */
  public final Instruction getInstruction() {
    int index;

    if (!correct())
      return null;
    index = getInd();
    if (name.compareTo("ldc") == 0) {
      return new LDC(index);
    }
    if (name.compareTo("ldc_w") == 0) {
      return new LDC_W(index);
    }
    if (name.compareTo("ldc2_w") == 0) {
      return new LDC2_W(index);
    }
    return null;
  }

  /**
   * Ldc instruction line is correct if it has
   * one main parameter that may be a simple number
   * as well as a string in "" and another one that
   * is a number in ().
   *
   *@see InstructionLineController#correct()
   */
  public final boolean correct()
  {
    String s, str;
    s = UmbraHelper.stripAllWhitespace(line);
    final String[] s2 = IBytecodeStrings.ldc;
    int j, y, okok, okokok;
    for (j = 0; j < s2.length; j++) {
      if ((s.indexOf(s2[j]) > 0) && (s.indexOf(s2[j]) < s.indexOf(":") + 2))
        if (s.indexOf(s2[j]) + (s2[j].length()) + 1 > s.indexOf("%"))
        {
        //parameter checking
          if (s.lastIndexOf("(") < 2) return false;
          if (s.lastIndexOf(")") < 2) return false;
          int m, n, o;
          m = line.lastIndexOf("(");
          n = line.lastIndexOf(")");
          if (m + 1 >= n) {
            return false;
          }
          for (o = m + 1; o < n; o++) {
            if (!(Character.isDigit(line.charAt(o)))) return false;
          }
          //two types: number and (number) or string and (number)
          okok = 0;
          for (y = (s.indexOf(s2[j]) + s2[j].length()); y < s.lastIndexOf("("); y++) {
            if (!(Character.isDigit(s.charAt(y)))) okok++;
          }
          okokok = 0;
          str = "\"\"";
          if (okok > 0) {
            if (((s.indexOf(s2[j]) + s2[j].length())) == s.indexOf("\"")) {
              //here is null, true or false, true charsetName
              //checking if there is second" and if there are are 2
              if (!(s.indexOf("\"") == (s.lastIndexOf("(") - 1))) {
                if ((s.charAt(s.lastIndexOf("(") - 1)) == str.charAt(1)) {
                  okokok++;
              }
            }
          }
        }

//        //if there are two numbers or one
        int c, d, e;
        int f, g, l;
        f = 0;
        g = 0;
        l = 0;
        e = line.lastIndexOf("(");
        d = line.indexOf(s2[j]) + s2[j].length();
        for (c = d; c < e; c++) {
          l = 0;
          if (Character.isDigit(line.charAt(c))) {
            f = 1;
          }
          if (f == 1) {
            if (!(Character.isDigit(line.charAt(c)))) {
              if (g == 1) {
                l = 0;
              } else {
                g = 1;
                l = 1; 
              }
            }
           }
           if ((l == 0) && (g == 1)) {
             if  (!(Character.isDigit(line.charAt(c)))) {
               okok = 1;
             }
           }
          }

        if ((okok == 0) || (okokok > 0)) {
          for (y = (s.lastIndexOf("(") + 1); y < s.lastIndexOf(")"); y++) {
            if (!(Character.isDigit(s.charAt(y)))) return false;
          }
          return true;
        }

          return false;
        }
    }
    return false;
  }
}
