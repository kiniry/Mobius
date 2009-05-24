/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) 2006-2009 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.instructions;

import java.util.HashMap;

/**
 * This is a simple automaton for recognizing floating point numbers
 * in format described in "Textual Representation of Specifications"
 * of "BML Reference Manual".
 *
 * @author Tomasz Olejniczak (to236111@students.mimuw.edu.pl)
 * @version a-01
 */
public class RegExpAutomaton {

  /**
   * Hash map containing outgoing edges.
   */
  private HashMap < Character, RegExpAutomaton > my_edges;

  /**
   * This flag is set if this node is an accepting node.
   */
  private boolean my_is_final;

  /**
   * This objects stores the current position in string
   * which the automaton is processing. It is shared among all
   * nodes.
   */
  private Counter my_index_counter;

  /**
   * Automaton name.
   */
  private String my_symbol;

  /**
   * This creates automaton node named <code>symbol</code>.
   * If <code>isFinal</code> is set it will be an accepting node.
   *
   * @param an_is_final determines whether it is an accepting node
   * @param a_symbol name of the node
   */
  public RegExpAutomaton(final boolean an_is_final, final String a_symbol) {
    my_edges = new HashMap < Character, RegExpAutomaton > ();
    my_index_counter = new Counter(0);
    this.my_is_final = an_is_final;
    this.my_symbol = a_symbol;
  }

  /**
   * Adds node <code>a_node</code> to the automaton. <br>
   * Makes outgoing edge labeled <code>an_edge</code> leading
   * to node <code>a_node</code>. After calling this functions
   * both current node and node <code>a_node</code> shares the
   * same current position counter, which is the original
   * current node counter.
   *
   * @param an_edge edge label
   * @param a_node a node to which the edge leads
   */
  public void set(final char an_edge, final RegExpAutomaton a_node) {
    a_node.setIndexCounter(my_index_counter);
    my_edges.put(an_edge, a_node);
  }

  /**
   * Makes outgoing edges labeled with digits leading to node
   * <code>a_node</code>.
   *
   * @param a_node a node to which the edges leads
   */
  public void setDigit(final RegExpAutomaton a_node) {
    for (int i = 0; i < 10; i++) set(Integer.toString(i).charAt(0), a_node);
  }

   /**
   * Makes outgoing edges labeled with floating point type symbols
   * (d, D, f, F) leading to node <code>a_node</code>.
   *
   * @param a_node a node to which the edges leads
   */
  public void setSymbol(final RegExpAutomaton a_node) {
    set('d', a_node);
    set('D', a_node);
    set('f', a_node);
    set('F', a_node);
  }

  /**
   * Reads character at position <code>an_index</code> from string
   * <code>a_line</code>. If there is outgoing edge labeled with
   * that character it proceeds to the node to which this edge leads.
   * If there is no such edge false is returned if we aren't in
   * accepting node and true otherwise. If the whole string
   * <code>a_line</code> has been read true is returned if we are in
   * accepting node and false otherwise. <br> <br>
   *
   * Note that automaton parses till the first character that does not
   * have outgoing edge from current node, and if that node happens to
   * be accepting, it will accept. So the automaton recognizes the numbers
   * "3.-4" and "3.2e2.1" as 3. and 3.2e2 (correct) + "-4" and ".1" as the
   * rest of string passed to parser that uses AN. However we hope that
   * parser will recognize the error.
   *
   * @param a_line a string which the automaton processes
   * @param an_index current position in <code>a_line</code>
   * @return true if automaton accepts <code>a_line</code>, false
   * otherwise
   */
  public boolean exec(final String a_line, final int an_index) {
    my_index_counter.setValue(an_index);
    if (an_index == a_line.length()) {
      //System.err.println("Node: " + symbol + ", final: " + isFinal);
      return my_is_final;
    }
    for (Character c : my_edges.keySet()) {
      if (c == a_line.charAt(an_index)) {
        //System.err.println("Node: " + symbol + ", read: "
        // + c + ", an_index: " + an_index + ", length: " + a_line.length());
        return my_edges.get(c).exec(a_line, an_index + 1);
      }
    }
    return my_is_final;
  }

  /**
   * This method returns the current position in processed string.
   * After automaton accepted string an
   * {@link RegExpAutomaton#exec(String, int)}
   * returned true it contains the position immediately after last
   * character of accepted floating point number.
   *
   * @return current position in processed string
   */
  public int getIndex() {
    return my_index_counter.getValue();
  }

  /**
   * This method sets the Counter object that represents the current
   * position in processed string and is shared among all nodes.
   * @param a_counter a counter to set
   */
  public void setIndexCounter(final Counter a_counter) {
    my_index_counter = a_counter;
  }

  /**
   * Creates automaton for recognizing floating point numbers
   * in format described in "Textual Representation of Specifications"
   * of "BML Reference Manual". AN stands for 'automaton node'. See
   * Umbra/docs/codedoc/automaton.eps for automaton schema.
   *
   * @return constructed automaton
   */
  public static RegExpAutomaton constructAutomaton() {
    final RegExpAutomaton a = new RegExpAutomaton(false, "a");
    final RegExpAutomaton b = new RegExpAutomaton(false, "b");
    final RegExpAutomaton c = new RegExpAutomaton(false, "c");
    final RegExpAutomaton d = new RegExpAutomaton(false, "d");
    final RegExpAutomaton e = new RegExpAutomaton(false, "e");
    final RegExpAutomaton f = new RegExpAutomaton(true, "f");
    final RegExpAutomaton g = new RegExpAutomaton(true, "g");
    final RegExpAutomaton h = new RegExpAutomaton(false, "h");
    final RegExpAutomaton i = new RegExpAutomaton(false, "i");
    final RegExpAutomaton j = new RegExpAutomaton(true, "j");
    final RegExpAutomaton k = new RegExpAutomaton(true, "k");
    a.set('+', c);
    a.set('-', c);
    a.set('.', b);
    a.setDigit(d);
    b.setDigit(f);
    b.set('+', e);
    b.set('-', e);
    c.setDigit(d);
    c.set('.', b);
    d.setDigit(d);
    d.set('.', k);
    d.setSymbol(g);
    d.set('E', h);
    d.set('e', h);
    e.setDigit(f);
    f.setDigit(f);
    f.set('E', h);
    f.set('e', h);
    f.setSymbol(g);
    h.set('+', i);
    h.set('-', i);
    h.setDigit(j);
    i.setDigit(j);
    j.setDigit(j);
    j.setSymbol(g);
    k.set('E', h);
    k.set('e', h);
    k.setDigit(f);
    k.setSymbol(g);
    return a;
  }

  /**
   * This is simple counter.
   * @author Tomasz Olejniczak (to236111@students.mimuw.edu.pl)
   * @version a-01
   *
   */
  private class Counter {

    /**
     * Counter value.
     */
    private int my_value;

    /**
     * Basic constructor. Sets counter value to a_value.
     *
     * @param a_value a value to set
     */
    public Counter(final int a_value) {
      my_value = a_value;
    }

    /**
     * Returns counter value.
     *
     * @return counter value
     */
    public int getValue() {
      return my_value;
    }

    /**
     * Sets counter value to a_value.
     *
     * @param a_value a value to set
     */
    public void setValue(final int a_value) {
      my_value = a_value;
    }

  }

}
