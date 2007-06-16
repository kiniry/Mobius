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
 * @author Jarosław Paszek
 */
public class FieldInstruction extends StringInstruction {

  /**
   * TODO
   */
  public FieldInstruction(final String l, final String n) {
    super(l, n);
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
    s = UmbraHelper.stripAllWhitespace(line);
    final String[] s2 = IBytecodeStrings.field;
    int j;
    for (j = 0; j < s2.length; j++) {
      if ((s.indexOf(s2[j]) > 0) && (s.indexOf(s2[j]) < s.indexOf(":") + 2)) {

        if (s.lastIndexOf("(") < 2) return false;
        if (s.lastIndexOf(")") < 2) return false;
        int m,n,o;
        m = line.lastIndexOf("(");
        n = line.lastIndexOf(")");
        //System.out.println(m + " " + n + " " + line);
        if (m + 1 >= n) {return false;}
        for (o = m + 1; o < n; o++)
          { if (!(Character.isDigit(line.charAt(o))))
            {return false;}
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
    if (line.lastIndexOf("(") >= line.lastIndexOf(")")){
    } else {
    isd = true;
    for (int i = line.lastIndexOf("(") + 1;i < line.lastIndexOf(")");i++) {
      if (!Character.isDigit(line.charAt(i))){
        isd = false;
      }
    }
    if (isd){
      liczba = 0;
      for (int i = line.lastIndexOf("(") + 1;i < line.lastIndexOf(")");i++) {
        liczba = 10*liczba + licznik.indexOf(line.substring(i,i+1));
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
  if (name.compareTo("getfield")==0) {
    return new GETFIELD(index);
  }
  if (name.compareTo("getstatic")==0) {
    return new GETSTATIC(index);
  }
  if (name.compareTo("putfield")==0) {
    return new PUTFIELD(index);
  }
  if (name.compareTo("putstatic")==0) {
    return new PUTSTATIC(index);
  }
  }
  return null;

  }
}
