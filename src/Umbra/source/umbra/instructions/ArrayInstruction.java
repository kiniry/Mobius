/*
 * Created on 2005-05-19
 */
package umbra.instructions;

import org.apache.bcel.generic.Instruction;
import org.apache.bcel.generic.NEWARRAY;
import org.apache.bcel.generic.Type;

import umbra.UmbraHelper;
import umbra.editor.parsing.IBytecodeStrings;



/**
 * This class is a superclass for a subset of instructions
 * depending on parameters. It redefines some crucial while
 * handling with single instruction methods(correctness, getting handle).
 * There is only one array instruction used to create new
 * array of a particular type.
 * TODO
 *
 * @author Jarosław Paszek
 */
public class ArrayInstruction extends StringInstruction {

  /**
   * The names of base bytecode types relevant for
   * array instructions. It correspond to the types
   * in the array {@ref types}.
   */
  private static final String[] names =
  {"VOID", "BOOLEAN","INT", "SHORT", "BYTE", "LONG",
    "DOUBLE", "FLOAT", "CHAR"};

  /**
   * The types of the bytecode types relevant for
   * array instructions. It correspond to the types
   * in the array {@ref names}.
   */
  private static final Type[] types =
  {Type.VOID, Type.BOOLEAN, Type.INT, Type.SHORT,
      Type.BYTE, Type.LONG, Type.DOUBLE,
      Type.FLOAT, Type.CHAR};

  /**
   * The number of types relevant to the array
   * instructions. It is correlated with the arrays
   * <code>names</code> and <code>types</code>
   */
  private static final int typeCount = types.length;

  /**
   * This method returns the type that corresponds to
   * the given name
   *
   * @param the string for which the type
   */
  private static Type getType(final String insName) {
    for (int i = 0; i < typeCount; i++) {
      if ((names[i].startsWith(insName)) && (insName.startsWith(names[i])))
        return types[i];
    }return null;
  }

  /**
   * TODO
   */
  public ArrayInstruction(final String l, final String n) {
    super(l, n);
  }

  /**
   * @see BytecodeLineController#getInstruction()
   */
  public final Instruction getInstruction() {
    //System.out.println("ArrayInstruction->getInstruction...");
    String insType = line.substring(line.indexOf("<") + 1, line.indexOf(">"));
    insType = insType.toUpperCase();
    if (getType(insType) == null) {
      //System.out.println("   Wrong instruction argument!");
      return null;
    }
    final byte r = getType(insType).getType();
    //&*
    final boolean isOK = correct();
    if (isOK) {
    if (name.compareTo("newarray")==0)
      return new NEWARRAY(r);
    }
    //System.out.println("   Failed!");
    return null;
  }


  /**
   * Array instruction line is correct if it has
   * one parameter that is class (or non-classed type) name.
   *
   *@see InstructionLineController#correct()
   */
  public final boolean correct()
  {
    String s;
    s = UmbraHelper.stripAllWhitespace(line);
    final String[] s2 = IBytecodeStrings.array;
    int j,y;
    for (j = 0; j < s2.length; j++) {
      if ((s.indexOf(s2[j]) > 0) && (s.indexOf(s2[j]) < s.indexOf(":") + 2)) {
        //System.out.println(s);
        //System.out.println("array " + s);
        if (s.indexOf("<") < 2) return false;
        if (s.indexOf(">") < 2) return false;
        // zmienione 7.26.15
        String insType = s.substring(s.indexOf("<") + 1, s.indexOf(">"));
        insType = insType.toUpperCase();
        if (getType(insType) == null) {
          System.out.println("E04");
          return false;
        }

        for (y = (s.indexOf("<") + 1); y < s.indexOf(">"); y++)
           {if (!(Character.isDefined(s.charAt(y)))) return false;}
        return true;
      }
    }

    return false;
  }
}
