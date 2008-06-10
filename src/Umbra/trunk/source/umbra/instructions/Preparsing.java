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

import umbra.UmbraPlugin;
import umbra.instructions.ast.AnnotationLineController;
import umbra.instructions.ast.BytecodeLineController;
import umbra.instructions.ast.CommentLineController;
import umbra.instructions.ast.EmptyLineController;
import umbra.instructions.ast.HeaderLineController;
import umbra.instructions.ast.InstructionLineController;
import umbra.instructions.ast.ThrowsLineController;
import umbra.instructions.ast.UnknownLineController;
import umbra.lib.BytecodeStrings;

/**
 * This class handles the preparsing of document lines. It creates an automaton
 * which recognises the particular line kind and creates the line handler. This
 * automaton is used to obtain the line handler for the given string.
 * Additionally, the process of getting of a line handler is controlled by a
 * document context. In particular, the context recognises situation when
 * the parsing is inside of a multi-line comment or a BML annotation.
 *
 * @author Aleksy Schubert (alx@mimuw.edu.pl)
 * @version a-01
 */
public final class Preparsing {

  /**
   * The automaton to pre-parse the lines of the byte code document.
   */
  private static DispatchingAutomaton my_preparse_automaton;

  /**
   * Private constructor added to prevent the creation of objects of this
   * type.
   */
  private Preparsing() {
  }

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
      if (lc.isAnnotationEnd()) {
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
        a_context.setInsideAnnotation(-1);
      } else {
        a_context.setInsideComment();
      }
    }
    return blc;
  }


  /**
   * This method returns the automaton which handles the preparsing of lines
   * and creates appropriate line controllers. In case the automaton has not
   * been created yet, the method creates it.
   *
   * The automaton has the following major states:
   * <ul>
   *   <li>INITIAL - where all the processing starts</li>
   *   <li>DIGIT - where the digits of the byte code instruction number
   *                are recognised,</li>
   *   <li>COLON - after the colon of the byte code instruction is
   *               swallowed,</li>
   *   <li>many MNEMONIC states - to recognise mnemonics,</li>
   *   <li>many THROWS states - to recognise throws lines,</li>
   *   <li>many HEADER states - to recognise throws lines,</li>
   *   <li>COMMENT - to recognise multi-line comment start,</li>
   *   <li>ANNOT - to recognise BML annotation start.</li>
   * </ul>
   * The INITIAL state contains a loop over whitespace characters and outgoing
   * edges (paths) to THROWS, HEADER, COMMENT, ANNOT and DIGIT states. The DIGIT
   * state contains a loop over digits and an outgoing edge to the COLON state.
   * The COLON state contains a loop over whitespace characters and outgoing
   * edges to MNEMONIC states (paths to be precise).
   *
   * Note that this automaton is slightly inefficient as MNEMONIC, THROWS etc.
   * states could be made a single one.
   *
   * @return the automaton to handle preparsing of lines
   * @see DispatchingAutomaton for a description of the way the automaton works
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

  /**
   * This method adds to the initial state of the preparsing automaton the
   * all the paths which are described by characters from the given array.
   * The method associates the given class as the class the objects of which
   * are created when the end of the path is reached in the automaton.
   *
   * @param the_paths the description of paths to be added
   * @param a_class the class the objects of which should be created when the
   *   parsing reaches the terminal nodes created by this method
   */
  private static void addSimpleForArray(final String[] the_paths,
                                 final Class a_class) {
    for (int k = 0; k < the_paths.length; k++) {
      my_preparse_automaton.addSimple(the_paths[k],
                                      a_class);
    }
  }

  /**
   * This method adds a whitespace loop to the given state of an automaton.
   *
   * @param a_state the state of the automaton
   */
  private static void addWhitespaceLoop(final DispatchingAutomaton a_state) {
    for (int i = 0;
         i < BytecodeStrings.WHITESPACE_CHARACTERS.length;
         i++) {
      a_state.addStarRule(
        Character.toString(BytecodeStrings.
                           WHITESPACE_CHARACTERS[i]),
        a_state);
    }
  }

  /**
   * This method adds all the paths to recognise byte code mnemonics to the
   * given node of an automaton.
   *
   * @param a_node the node of the automaton to add the paths to
   */
  private static void addAllMnemonics(final DispatchingAutomaton a_node) {
    for (int i = 0; i < InstructionLineController.INS_CLASS_HIERARCHY.length;
         i++) {
      try {
        final String[] the_mnemonics = (String[])
            (InstructionLineController.INS_CLASS_HIERARCHY[i].
                getMethod("getMnemonics").invoke(null));
        for (int j = 0; j < the_mnemonics.length; j++) {
          a_node.addMnemonic(the_mnemonics[j], the_mnemonics[j],
                             InstructionLineController.INS_CLASS_HIERARCHY[i]);
        }
      } catch (IllegalArgumentException e) {
        UmbraPlugin.messagelog("Impossible IllegalArgumentException in" +
                               " preparsing");
      } catch (SecurityException e) {
        UmbraPlugin.messagelog("Impossible SecurityException in" +
          " preparsing");
      } catch (IllegalAccessException e) {
        UmbraPlugin.messagelog("Impossible IllegalAccessException in" +
          " preparsing");
      } catch (InvocationTargetException e) {
        UmbraPlugin.messagelog("Impossible InvocationTargetException in" +
          " preparsing");
      } catch (NoSuchMethodException e) {
        UmbraPlugin.messagelog("Impossible NoSuchMethodException in" +
          " preparsing");
      }
    }
  }

}
