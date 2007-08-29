/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) ${date} University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.instructions;

import org.apache.bcel.generic.Instruction;
import org.apache.bcel.generic.NEWARRAY;
import org.apache.bcel.generic.Type;

import umbra.UmbraHelper;
import umbra.UmbraPlugin;
import umbra.editor.parsing.BytecodeStrings;



/**
 * This class is a superclass for a subset of instructions
 * depending on parameters. It redefines some crucial while
 * handling with single instruction methods(correctness, getting handle).
 * There is only one array instruction used to create new
 * array of a particular type.
 * TODO
 *
 * @author Jarosław Paszek (jp209217@students.mimuw.edu.pl)
 * @version a-01
 */
public class ArrayInstruction extends StringInstruction {

  /**
   * A position before which the '>' character cannot occur in a correct line.
   */
  private static final int GREATER_FORBIDDEN_BOUND = 2;

  /**
   * A position before which the '<' character cannot occur in a correct line.
   */
  private static final int LESS_FORBIDDEN_BOUND = 2;

  /**
   * The names of base bytecode types relevant for
   * array instructions. It correspond to the types
   * in the array {@ref TYPES}.
   */
  private static final String[] NAMES =
  {"VOID", "BOOLEAN", "INT", "SHORT", "BYTE", "LONG",
    "DOUBLE", "FLOAT", "CHAR"};

  /**
   * The types of the bytecode types relevant for
   * array instructions. It correspond to the types
   * in the array {@ref NAMES}.
   */
  private static final Type[] TYPES =
  {Type.VOID, Type.BOOLEAN, Type.INT, Type.SHORT,
   Type.BYTE, Type.LONG, Type.DOUBLE,
   Type.FLOAT, Type.CHAR};

  /**
   * The number of types relevant to the array
   * instructions. It is correlated with the arrays
   * <code>NAMES</code> and <code>TYPES</code>
   */
  private static final int TYPE_COUNT = TYPES.length;

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
  public ArrayInstruction(final String a_line_text, final String a_name) {
    super(a_line_text, a_name);
  }

  /**
   * This method returns the type that corresponds to
   * the given name.
   *
   * @param an_ins_name the string for which the type
   * @return the type for that name or <code>null</code> when no type
   * corresponds to the name
   */
  private static Type getType(final String an_ins_name) {
    for (int i = 0; i < TYPE_COUNT; i++) {
      if ((NAMES[i].startsWith(an_ins_name)) &&
          (an_ins_name.startsWith(NAMES[i])))
        return TYPES[i];
    }
    return null;
  }


  /**
   * @return TODO
   * @see BytecodeLineController#getInstruction()
   */
  public final Instruction getInstruction() {
    final String my_line_text = getMy_line_text();
    String an_ins_type = my_line_text.substring(my_line_text.indexOf("<") + 1,
                                        my_line_text.indexOf(">"));
    an_ins_type = an_ins_type.toUpperCase();
    if (getType(an_ins_type) == null) {
      return null;
    }
    final byte r = getType(an_ins_type).getType();
    final boolean isOK = correct();
    if (isOK) {
      if (getName().compareTo("newarray") == 0)
        return new NEWARRAY(r);
    }
    return null;
  }


  /**
   * Array instruction line is correct if it has
   * one parameter that is class (or non-classed type) name.
   *
   * @return TODO
   * @see InstructionLineController#correct()
   */
  public final boolean correct()
  {
    final String my_line_text = getMy_line_text();
    final String s = UmbraHelper.stripAllWhitespace(my_line_text);
    final String[] s2 = BytecodeStrings.ARRAY_INS;
    int j, y;
    for (j = 0; j < s2.length; j++) {
      if ((s.indexOf(s2[j]) > 0) &&
          (s.indexOf(s2[j]) <= s.indexOf(":") + 1)) {
        if (s.indexOf("<") < LESS_FORBIDDEN_BOUND) return false;
        if (s.indexOf(">") < GREATER_FORBIDDEN_BOUND) return false;
        // zmienione 7.26.15
        String ins_type = s.substring(s.indexOf("<") + 1, s.indexOf(">"));
        ins_type = ins_type.toUpperCase();
        if (getType(ins_type) == null) {
          return false;
        }

        for (y = (s.indexOf("<") + 1); y < s.indexOf(">"); y++) {
          if (!(Character.isDefined(s.charAt(y)))) return false;
        }
        return true;
      }
    }

    return false;
  }
}
