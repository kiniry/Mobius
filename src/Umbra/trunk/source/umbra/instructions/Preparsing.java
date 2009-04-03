/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) 2006-2009 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.instructions;

import java.lang.reflect.InvocationTargetException;

import umbra.UmbraPlugin;
import umbra.instructions.ast.AnnotationLineController;
import umbra.instructions.ast.BytecodeLineController;
import umbra.instructions.ast.CPHeaderController;
import umbra.instructions.ast.CPLineController;
import umbra.instructions.ast.ClassHeaderLineController;
import umbra.instructions.ast.CommentLineController;
import umbra.instructions.ast.EmptyLineController;
import umbra.instructions.ast.FieldLineController;
import umbra.instructions.ast.HeaderLineController;
import umbra.instructions.ast.InstructionLineController;
import umbra.instructions.ast.ThrowsLineController;
import umbra.instructions.ast.UnknownLineController;
import umbra.lib.BMLParsing;
import umbra.lib.BytecodeStrings;

/**
 * This class handles the preparsing of document lines. It creates an automaton
 * which recognises the particular line kind and creates the line handler. This
 * automaton is used to obtain the line handler for the given string.
 * Additionally, the process of getting of a line handler is controlled by a
 * document context. In particular, the context recognises situation when
 * the parsing is inside of a multi-line comment or a BML annotation.
 *
 * @author Tomasz Olejniczak (to236111@students.mimuw.edu.pl)
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
   * This constant determines whether the constant pool will be parsed. It
   * is intended to be used only during development.
   * 
   * TODO (to236111) remove
   */
  public static final boolean PARSE_CP = true;

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
   * @param a_bmlp the BMLLib representation of the current
   *   class
   * @return instance of subclass of a line controller
   *     that contents of the given line satisfies
   *     classification conditions (unknown if it does not for all)
   */
  public static BytecodeLineController getType(final String a_line,
                                         final LineContext a_context,
                                         final BMLParsing a_bmlp) {
    final BytecodeLineController initial = getTypeForInsides(a_line,
                                                             a_context, a_bmlp);
    if (initial != null) return initial;
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
   * This method checks if the current context is within one of the special
   * areas (i.e. comments, BML annotations, or constant pool area) and if
   * so generates appropriate line within the areas. In case the line
   * represents the end of the particular area, the method changes the
   * state of the context accordingly. In case the context is not in any
   * of the special areas, the method returns <code>null</code>.
   *
   * @param a_line the string representation of the current line in the byte
   *   code
   * @param a_context the context which indicates in what area we are in
   * @param a_bmlp the BMLLib representation of the current
   *   class
   * @return a line controller corresponding to the area we are in or
   *   <code>null</code> in case we are not in any of the areas
   */
  private static BytecodeLineController getTypeForInsides(
      final String a_line,
      final LineContext a_context,
      final BMLParsing a_bmlp) {
    BytecodeLineController lc = null;
    if (a_context.isInsideComment()) {
      lc = new CommentLineController(a_line);
      if (lc.isCommentEnd()) {
        a_context.revertState();
      }
    } else if (a_context.isInsideAnnotation()) {
      lc = new AnnotationLineController(a_line);
      if (((AnnotationLineController)lc).isAnnotationEnd()) {
        a_context.revertState();
      }
    } else if (a_context.isInsideConstantPool()) {
      /* TODO (to236111) automaton here */
      if (!PARSE_CP) {
        if (CPLineController.isCPLineStart(a_line)) {
          return new umbra.instructions.ast.IncorrectCPLineController(a_line, null);
        }
      }
    } else if (a_context.isInFieldsArea()) {
      if (FieldLineController.isFieldLineStart(a_line)) {
        return new FieldLineController(a_line, a_bmlp);
      }
    }
    return lc;
  }

  /**
   * This method initializes the CP node of the automaton.
   * The current implementation uses the same mechanism for handling
   * both constant pool entries and instruction lines. Because the
   * automaton needs a mnemonic to create {@code BytecodeLineController}
   * for given line the constant pool entry keyword is used as surrogate
   * mnemonic.
   * 
   * TODO (to236111) Create separate automaton for constant pool entries which uses
   * IncorrectCPLineController instead of UnknownLineController for
   * incorrect lines to allow generating more specific information about
   * syntax errors inside constant pool.
   * 
   * @param node the CP node of automaton
   */
  private static void initCPNode(DispatchingAutomaton node) {
    addWhitespaceLoop(node);
    node = node.addSimple("#", UnknownLineController.class);
    final DispatchingAutomaton digitnode = node.addSimple("0",
                                                          UnknownLineController.class);
    for (int i = 1; i < 10; i++) {
      node.addStarRule(Integer.toString(i), digitnode);
    }
    for (int i = 0; i < 10; i++) {
      node.addStarRule("0" + Integer.toString(i), digitnode);
    }
    node = digitnode;
    addWhitespaceLoop(node);
    node = node.addSimple("=", UnknownLineController.class);
    addWhitespaceLoop(node);
    for (int i = 0; i < CPLineController.CP_CLASS_HIERARCHY.length;
         i++) {
      try {
        final String entry_type = (String)
            (CPLineController.CP_CLASS_HIERARCHY[i].
                getMethod("getEntryType").invoke(null));
        node.addMnemonic(entry_type, entry_type,
                         CPLineController.CP_CLASS_HIERARCHY[i]);
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
      } catch (Exception e) {
        e.printStackTrace();
      }
    }
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
   *   <li>CP - after the "const" of the constant pool entry is
   *            swallowes,</li>
   *   <li>many MNEMONIC states - to recognise mnemonics,</li>
   *   <li>many THROWS states - to recognise throws lines,</li>
   *   <li>many HEADER states - to recognise header lines,</li>
   *   <li>many CPENTRY states - to recognise constant pool entries,</li>
   *   <li>COMMENT - to recognise multi-line comment start,</li>
   *   <li>ANNOT - to recognise BML annotation start.</li>
   * </ul>
   * The INITIAL state contains a loop over whitespace characters and outgoing
   * edges (paths) to THROWS, HEADER, COMMENT, CP, ANNOT and DIGIT states. The DIGIT
   * state contains a loop over digits and an outgoing edge to the COLON state.
   * The COLON state contains a loop over whitespace characters and outgoing
   * edges to MNEMONIC states (paths to be precise).
   * The CP state contains outgoing edges to CPENTRY states (paths to be precise).
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
      my_preparse_automaton.addSimple(
        BytecodeStrings.JAVA_KEYWORDS[BytecodeStrings.CLASS_KEYWORD_POS],
        ClassHeaderLineController.class);
      my_preparse_automaton.addSimple(
        BytecodeStrings.JAVA_KEYWORDS[BytecodeStrings.CP_KEYWORD_POS],
        CPHeaderController.class);
      my_preparse_automaton.addSimple(
        BytecodeStrings.JAVA_KEYWORDS[BytecodeStrings.SCP_KEYWORD_POS],
        CPHeaderController.class);
      
      if (PARSE_CP) {
        DispatchingAutomaton cpnode = my_preparse_automaton.addSimple(
        BytecodeStrings.JAVA_KEYWORDS[BytecodeStrings.CP_ENTRY_KEYWORD_POS],
        UnknownLineController.class);
      
        initCPNode(cpnode);
      }

      my_preparse_automaton.addSimple(BytecodeStrings.COMMENT_LINE_START,
                                      CommentLineController.class);
      my_preparse_automaton.addSimple(BytecodeStrings.ANNOT_START,
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
