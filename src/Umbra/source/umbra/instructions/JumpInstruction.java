/*
 * Created on 2005-05-19
 */
package umbra.instructions;

import org.apache.bcel.generic.BranchInstruction;
import org.apache.bcel.generic.GOTO;
import org.apache.bcel.generic.GOTO_W;
import org.apache.bcel.generic.IFEQ;
import org.apache.bcel.generic.IFGE;
import org.apache.bcel.generic.IFGT;
import org.apache.bcel.generic.IFLE;
import org.apache.bcel.generic.IFLT;
import org.apache.bcel.generic.IFNE;
import org.apache.bcel.generic.IFNONNULL;
import org.apache.bcel.generic.IFNULL;
import org.apache.bcel.generic.IF_ACMPEQ;
import org.apache.bcel.generic.IF_ACMPNE;
import org.apache.bcel.generic.IF_ICMPEQ;
import org.apache.bcel.generic.IF_ICMPGE;
import org.apache.bcel.generic.IF_ICMPGT;
import org.apache.bcel.generic.IF_ICMPLE;
import org.apache.bcel.generic.IF_ICMPLT;
import org.apache.bcel.generic.IF_ICMPNE;
import org.apache.bcel.generic.Instruction;
import org.apache.bcel.generic.InstructionHandle;
import org.apache.bcel.generic.InstructionList;
import org.apache.bcel.generic.JSR;
import org.apache.bcel.generic.JSR_W;

import umbra.UmbraHelper;
import umbra.editor.parsing.IBytecodeStrings;


/**
 * This class is related to some subset of instructions
 * depending on parameters. It redefines some crucial while
 * handling with single instruction methods(correctness, getting handle).
 * Instructions of this class are responsible for jumping in code.
 * Their specificity is having target.
 *
 * @author Jarosław Paszek (jp209217@students.mimuw.edu.pl)
 * @version a-01
 */
public class JumpInstruction extends NumInstruction {



  /**
   * TODO
   */
  public JumpInstruction(final String l, final String n) {
    super(l, n);
  }



  /**
   * Jump instruction line is correct if it has
   * one number parameter preceded by #.
   *
   *@see InstructionLineController#correct()
   */
  public final boolean correct()
  {
    String s;
    s = UmbraHelper.stripAllWhitespace(line);
    final String[] s2 = IBytecodeStrings.jump;
    int j;
    int y;
    if (s.indexOf("#") < s.indexOf(":") + 1) return false;
    for (j = 0; j < s2.length; j++) {
      if ((s.indexOf(s2[j]) > 0) && (s.indexOf(s2[j]) < s.indexOf(":") + 2))
        if (s.indexOf(s2[j]) + (s2[j].length()) + 1 > s.indexOf("#"))
        { for (y = (s.indexOf("#") + 1); y < s.length(); y++)
            {if (!(Character.isDigit(s.charAt(y)))) return false;}
        //checking if there are two numbers or one
        int a,b,d,e,f,g;
        a = (s.length() - s.indexOf("#"));
        int c = 0;
        e = line.length() - line.indexOf("#");
        f = 0; g = line.length();
        for (d = 0; d < e; d++)
          { if (Character.isDigit(line.charAt(g - d - 1)))
             {f = 1;}
          if (f == 0) {
            if (Character.isWhitespace(line.charAt(g - d - 1)))
             {c++;}
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
    final String counter = "0123456789";
    int number;

    isd = true;
    int dokad = line.length();
    for (int i = line.lastIndexOf("#") + 1;i < line.length();i++) {
      if (!Character.isDigit(line.charAt(i))){
        dokad = i;
        break;
      }
    }
    if (isd){
      number = 0;
      for (int i = line.lastIndexOf("#") + 1;i < dokad;i++) {
        number = 10*number + counter.indexOf(line.substring(i,i+1));
      }
      return number;
    }
    return 0;
  }

  /**
   * TODO
   * @see BytecodeLineController#getInstruction()
   */
  public final Instruction getInstruction() {


    final InstructionHandle ih = null;

    if (!correct())
      return null;
    if (name.compareTo("goto")==0) {
      return new GOTO(ih);
    }
    if (name.compareTo("goto_w")==0) {
      return new GOTO_W(ih);
    }
    if (name.compareTo("if_acmpeq")==0) {
      return new IF_ACMPEQ(ih);
    }
    if (name.compareTo("if_acmpne")==0) {
      return new IF_ACMPNE(ih);
    }
    if (name.compareTo("if_icmpeq")==0) {
      return new IF_ICMPEQ(ih);
    }
    if (name.compareTo("if_icmpge")==0) {
      return new IF_ICMPGE(ih);
    }
    if (name.compareTo("if_icmpgt")==0) {
      return new IF_ICMPGT(ih);
    }
    if (name.compareTo("if_icmple")==0) {
      return new IF_ICMPLE(ih);
    }
    if (name.compareTo("if_icmplt")==0) {
      return new IF_ICMPLT(ih);
    }
    if (name.compareTo("if_icmpne")==0) {
      return new IF_ICMPNE(ih);
    }
    if (name.compareTo("ifeq")==0) {
      return new IFEQ(ih);
    }
    if (name.compareTo("ifge")==0) {
      return new IFGE(ih);
    }
    if (name.compareTo("ifgt")==0) {
      return new IFGT(ih);
    }
    if (name.compareTo("ifle")==0) {
      return new IFLE(ih);
    }
    if (name.compareTo("iflt")==0) {
      return new IFLT(ih);
    }
    if (name.compareTo("ifne")==0) {
      return new IFNE(ih);
    }
    if (name.compareTo("ifnonnull")==0) {
      return new IFNONNULL(ih);
    }
    if (name.compareTo("ifnull")==0) {
      return new IFNULL(ih);
    }
    if (name.compareTo("jsr")==0) {
      return new JSR(ih);
    }
    if (name.compareTo("jsr_w")==0) {
      return new JSR_W(ih);
    }
    return null;

    }

  /**
   * Jump instruction requires an instruction number of
   * its target as a parameter. This method is resposible
   * for setting such a number. The case that target line
   * does not exist is not completely solved yet.
   *
   */
  public final void setTarget(final InstructionList il, final Instruction ins) {
    int i = 0;
    i = getInd();
    InstructionHandle iha = null;
    // add parameter to getInstruction
    iha = il.findHandle(i);
    //TODO not generalized !-3
    if (iha == null) iha = il.findHandle(i - 3);
    System.out.println("i = " + i);
    if (il == null) System.out.println("null il");
    else if (iha == null) System.out.println("null iha");
    else if (iha.getInstruction() == null) System.out.println("null ins (drugie)");
    else System.out.println(iha.getInstruction().getName());
    if (ins == null) System.out.println("null ins");
    else System.out.println(ins.getName());
    ((BranchInstruction)ins).setTarget(iha);
    //System.out.println("Just failed");
  }
}
