/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) 2007-2009 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.instructions;

import java.lang.reflect.InvocationTargetException;
import java.util.TreeMap;

import umbra.instructions.ast.BytecodeLineController;
import umbra.instructions.ast.UnknownLineController;

/**
 * This class implements an automaton which is used to quickly determine
 * the type of the currently analysed line of the byte code text. The
 * automaton is constructed out of nodes each of which has the outgoing
 * edges labelled with characters ({@link Character}). One can do the
 * following operations on the automaton:
 * <ul>
 *   <li>add a rule to create a {@link BytecodeLineController} when a terminal
 *       node of the automaton is reached,</li>
 *   <li>add a loop rule which allows the automaton to move along star-like
 *       regular expressions,</li>
 *   <li>execute the rule for the given string line.</li>
 * </ul>
 *
 * @author Tomasz Olejniczak (to236111@students.mimuw.edu.pl)
 * @author Aleksy Schubert (alx@mimuw.edu.pl)
 * @version a-01
 */
public class DispatchingAutomaton {

  /**
   * In case no particular rule was set for this node, the automaton
   * creates an object of this class.
   */
  private static final Class DEFAULT_RULE = UnknownLineController.class;

  /**
   * This field represents the set of the outgoing edges from the current
   * node of the automaton.
   */
  private TreeMap my_outgoing;

  /**
   * This is the class which should be created in case the given parsed string
   * points to the current node.
   */
  private Class my_rule;
  //@ invariant (* my_rule is a subclass of BytecodeLineController *);

  /**
   * The string which holds the mnemonic to be used for the instruction
   * lines. It is used only when it is set to be non-null.
   */
  private String my_mnemonic;

  /**
   * The name of the current node for debugging purposes.
   */
  private String my_name;

  /**
   * This constructor creates the automaton such that the default rule is
   * executed and the set of outgoing edges is empty.
   */
  public DispatchingAutomaton() {
    my_rule = DEFAULT_RULE;
    my_outgoing = new TreeMap();
  }

  /**
   * This method adds to the automaton a rule to create given class after the
   * given string has been reached.
   *
   * If the string {@code a_string} is empty we add the rule to the current
   * node. If the string is not empty then we try to find its first character
   * among the outgoing edges. If we succeed, we delegate the setting of the
   * rule to the node at the end of the edge. In case we cannot find, the
   * outgoing edge for the first character, we add a new node and edge which
   * corresponds to the character and delegate the creation of the rule to the
   * fresh node.
   *
   * @param a_string {@link String} which shows where the creation should be
   *   created
   * @param a_rule a {@link Class} which should create a new object in case
   *   the rule is fired
   * @return the automaton node to which the rule {@code a_rule} was added
   */
  public DispatchingAutomaton addSimple(final String a_string,
                                        final Class a_rule) {
    return addMnemonic(a_string, null, a_rule);
  }

  /**
   * This method adds to the automaton a rule to create given class after the
   * given mnemonic string has been reached.
   *
   * If the string {@code a_string} is empty we add the rule to the current
   * node and the mnemonic set in the parameter {@code a_mnemonic}. If the
   * string is not empty then we try to find its first character
   * among the outgoing edges. If we succeed, we delegate the setting of the
   * rule to the node at the end of the edge. In case we cannot find the
   * outgoing edge for the first character, we add a new node and edge which
   * corresponds to the character and delegate the creation of the rule to the
   * fresh node.
   *
   * @param a_string {@link String} which shows where the creation should be
   *   created
   * @param a_mnemonic {@link String} with the mnemonic to associate with
   *   the final node
   * @param a_rule a {@link Class} which should create a new object in case
   *   the rule is fired
   * @return the automaton node to which the rule {@code a_rule} was added
   */
  public DispatchingAutomaton addMnemonic(final String a_string,
                                          final String a_mnemonic,
                                          final Class a_rule) {
    if (a_string.length() == 0) {
      my_rule = a_rule;
      my_mnemonic = a_mnemonic;
      my_name = a_mnemonic;
      return this;
    }
    final Character key = Character.valueOf(a_string.charAt(0));
    final String rest = a_string.substring(1);
    final DispatchingAutomaton next_auto;
    if (my_outgoing.containsKey(key)) {
      next_auto = (DispatchingAutomaton)my_outgoing.get(key);
    } else {
      next_auto = new DispatchingAutomaton();
      my_outgoing.put(key, next_auto);
      next_auto.setName(a_mnemonic + " " + key);
    }
    return next_auto.addMnemonic(rest, a_mnemonic, a_rule);
  }

  /*@ requires a_string.length() > 0;
    @
    @*/
  /**
   * This method adds to the automaton a star-like rule.
   *
   * If the string {@code a_string} is empty we add the rule to the current
   * node. If the string is not empty then we try to find its first character
   * among the outgoing edges. If we succeed, we delegate the setting of the
   * rule to the node at the end of the edge. In case we cannot find, the
   * outgoing edge for the first character, we add a new node and edge which
   * corresponds to the character and delegate the creation of the rule to the
   * fresh node.
   *
   * @param a_string the string which describes the loop, the length of the
   *   string must be at least 1
   * @param a_loop_point the {@link DispatchingAutomaton} point to which we
   *   loop at the end of {@code a_string}
   *
   */
  public void addStarRule(final String a_string,
                          final DispatchingAutomaton a_loop_point) {
    if (a_string.length() == 1) {
      final Character key = new Character(a_string.charAt(0));
      if (my_outgoing.containsKey(key)) {
        my_outgoing.remove(key);
      }
      my_outgoing.put(key, a_loop_point);
      return;
    }
    final Character key = new Character(a_string.charAt(0));
    final String rest = a_string.substring(1);
    final DispatchingAutomaton next_auto;
    if (my_outgoing.containsKey(key)) {
      next_auto = (DispatchingAutomaton)my_outgoing.get(key);
    } else {
      next_auto = new DispatchingAutomaton();
      my_outgoing.put(key, next_auto);
    }
    next_auto.addStarRule(rest, a_loop_point);
    return;
  }

  /**
   * This method executes a rule to create the class using the rules encoded
   * in the automaton.
   *
   * If the string {@code a_string} is empty we execute the rule in the current
   * node. If the string is not empty then we try to find its first character
   * among the outgoing edges. If we succeed, we delegate the setting of the
   * rule to the node at the end of the edge. In case we cannot find, the
   * outgoing edge for the first character, we execute the rule in the
   * current node.
   *
   * Note that this strategy allows to recognise a line such as:
   * <pre>
   *    12:  iinch
   * </pre>
   * as an {@link umbra.instructions.ast.IincInstruction} line.
   *
   * This method may throw {@link SecurityException} in case the security
   * manager forbids to refer to the constructor of the class to be created.
   *
   * @param a_string {@link String} which shows where the creation should be
   *   created
   * @param a_param a {@link String} parameter of the constructor to create
   *   the required object
   * @return {@link BytecodeLineController} corresponding to the string in
   *   {@code a_string}
   * @throws CannotCallRuleException thrown in case something made the call
   *   to the constructor of the result object impossible
   */
  public BytecodeLineController execForString(
                       final String a_string,
                       final String a_param)
    throws CannotCallRuleException {
    if (a_string.length() == 0) {
      return callConstructor(a_param);
    }
    final Character key = Character.valueOf(a_string.charAt(0));
    final String next = a_string.substring(1);
    if (my_outgoing.containsKey(key)) {
      final DispatchingAutomaton nexta =
        (DispatchingAutomaton)my_outgoing.get(key);
      return nexta.execForString(next, a_param);
    } else {
      return callConstructor(a_param);
    }
  }

  /**
   * This method tries to call the constructor from the current rule
   * with the given {@link String} parameter. This method used the field
   * {@link #my_mnemonic} in case it is set to be non-null.
   *
   * @param a_param the {@link String} parameter for the constructor to call
   * @return the called {@link BytecodeLineController}
   * @throws CannotCallRuleException thrown in case the constructor cannot
   *   be called
   */
  private BytecodeLineController callConstructor(final String a_param)
    throws CannotCallRuleException {
    try {
      if (my_mnemonic == null) {
        return (BytecodeLineController) my_rule.getConstructor(String.class).
                                        newInstance(a_param);
      } else {
        return (BytecodeLineController) my_rule.getConstructor(String.class,
                                                               String.class).
                                        newInstance(a_param, my_mnemonic);
      }
    } catch (IllegalArgumentException e) {
      throw new CannotCallRuleException(e);
    } catch (SecurityException e) {
      throw new CannotCallRuleException(e);
    } catch (InstantiationException e) {
      throw new CannotCallRuleException(e);
    } catch (IllegalAccessException e) {
      throw new CannotCallRuleException(e);
    } catch (InvocationTargetException e) {
      throw new CannotCallRuleException(e);
    } catch (NoSuchMethodException e) {
      throw new CannotCallRuleException(e);
    }
  }

  /**
   * Return the name of the node for debugging puropses.
   * @return the name of the node
   */
  public String getName() {
    return my_name;
  }

  /**
   * Sets the name of the node for debugging purposes.
   * @param a_name a name of the node to set
   */
  public void setName(final String a_name) {
    my_name = a_name;
  }

}
