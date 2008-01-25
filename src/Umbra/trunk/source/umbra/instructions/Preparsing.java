/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) 2006-2008 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.instructions;

import java.lang.reflect.InvocationTargetException;

import umbra.editor.parsing.BytecodeStrings;
import umbra.editor.parsing.BytecodeWhitespaceDetector;
import umbra.instructions.ast.AnnotationLineController;
import umbra.instructions.ast.BytecodeLineController;
import umbra.instructions.ast.CommentLineController;
import umbra.instructions.ast.EmptyLineController;
import umbra.instructions.ast.HeaderLineController;
import umbra.instructions.ast.InstructionLineController;
import umbra.instructions.ast.ThrowsLineController;
import umbra.instructions.ast.UnknownLineController;

/**
 * @author alx
 * @version a-01
 *
 */
public final class Preparsing {


  /**
   * The automaton to pre-parse the lines of the byte code document.
   */
  private static DispatchingAutomaton my_preparse_automaton;


  /**
   * Chooses one of line types that matches the given line
   * contents. This method does a quick pre-parsing of the
   * line content and based on that chooses which particular line controller
   * should be used for the given line. It also uses the context information
   * to return controllers in case the analysis is inside a comment or a
   * BML annotation.
   *
   * @param a_line the string contents of inserted or modified line
   * @param a_context information on the previous lines
   * @return instance of subclass of a line controller
   *     that contents of the given line satisfies
   *     classification conditions (unknown if it does not for all)
   */
  public static BytecodeLineController getType(final String a_line,
                                         final LineContext a_context) {
    if (a_context.isInsideComment()) {
      final CommentLineController lc = new CommentLineController(a_line);
      if (lc.isCommentEnd()) {
        a_context.revertState();
      }
      return lc;
    }

    if (a_context.isInsideAnnotation()) {
      final AnnotationLineController lc = new AnnotationLineController(a_line);
      if (lc.isCommentEnd()) {
        a_context.revertState();
      }
      return lc;
    }
    final DispatchingAutomaton automaton = Preparsing.getAutomaton();
    BytecodeLineController  blc;
    try {
      blc = automaton.execForString(a_line, a_line);
    } catch (CannotCallRuleException e) {
      blc = new UnknownLineController(a_line);
    }
    if (blc instanceof CommentLineController) {
      if (blc instanceof AnnotationLineController) {
        a_context.setInsideAnnotation();
      } else {
        a_context.setInsideComment();
      }
    }
    return blc;
  }


  /**
   * TODO
   * @return
   */
  public static DispatchingAutomaton getAutomaton() {
    if (my_preparse_automaton == null) {
      my_preparse_automaton = new DispatchingAutomaton();
      my_preparse_automaton.addSimple("", EmptyLineController.class);
      addWhitespaceLoop(my_preparse_automaton);
      addSimpleForArray(BytecodeStrings.THROWS_PREFIX,
                        ThrowsLineController.class);
      addSimpleForArray(BytecodeStrings.HEADER_PREFIX,
                        HeaderLineController.class);
      my_preparse_automaton.addSimple(BytecodeStrings.COMMENT_LINE_START,
                                      CommentLineController.class);
      my_preparse_automaton.addSimple(BytecodeStrings.ANNOT_LINE_START,
                                      AnnotationLineController.class);
      final DispatchingAutomaton digitnode = my_preparse_automaton.
               addSimple("0",
                         UnknownLineController.class);
      for (int i = 1; i < 10; i++) {
        my_preparse_automaton.addStarRule(Integer.toString(i), digitnode);
      }
      for (int i = 0; i < 10; i++) {
        my_preparse_automaton.addStarRule("0" + Integer.toString(i), digitnode);
      }
      final DispatchingAutomaton colonnode = digitnode.addSimple(":",
                                               UnknownLineController.class);
      addWhitespaceLoop(colonnode);
      addAllMnemonics(colonnode);
    }
    return my_preparse_automaton;
  }

  private static void addSimpleForArray(final String[] sHeaderInits,
                                 final Class a_class) {
    for (int k = 0; k < sHeaderInits.length; k++) {
      my_preparse_automaton.addSimple(sHeaderInits[k],
                                      a_class);
    }
  }

  private static void addWhitespaceLoop(DispatchingAutomaton an_automaton) {
    for (int i = 0;
         i < BytecodeWhitespaceDetector.WHITESPACE_CHARACTERS.length;
         i++) {
      an_automaton.addStarRule(
        Character.toString(BytecodeWhitespaceDetector.
                           WHITESPACE_CHARACTERS[i]),
        an_automaton);
    }
  }

  private static void addAllMnemonics(final DispatchingAutomaton colonnode) {
    for (int i = 0; i < InstructionLineController.INS_CLASS_HIERARCHY.length;
         i++) {
      try {
        final String[] the_mnemonics = (String[])
            (InstructionLineController.INS_CLASS_HIERARCHY[i].
                getMethod("getMnemonics").invoke(null));
        for (int j = 0; j < the_mnemonics.length; j++) {
          colonnode.addMnemonic(the_mnemonics[j], the_mnemonics[j],
                             InstructionLineController.INS_CLASS_HIERARCHY[i]);
        }
      } catch (IllegalArgumentException e) {
        // TODO Auto-generated catch block
        e.printStackTrace();
      } catch (SecurityException e) {
        // TODO Auto-generated catch block
        e.printStackTrace();
      } catch (IllegalAccessException e) {
        // TODO Auto-generated catch block
        e.printStackTrace();
      } catch (InvocationTargetException e) {
        // TODO Auto-generated catch block
        e.printStackTrace();
      } catch (NoSuchMethodException e) {
        // TODO Auto-generated catch block
        e.printStackTrace();
      }
    }
  }

}
