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
 * of "BML Reference Manual". AN stands for 'automaton node' shortened
 * for the ease of typing.
 *  
 * @author Tomasz Olejniczak (to236111@students.mimuw.edu.pl)
 * @version a-01
 */
public class AN {

  /**
   * Hash map containing outgoing edges.
   */
	private HashMap<Character, AN> edges;
	
	/**
	 * This flag is set if this node is an accepting node.
	 */
	private boolean isFinal;
	
	/**
	 * This objects stores the current position in string
	 * which the automaton is processing. It is shared among all
	 * nodes.
	 */
	private Counter my_index_counter;
	
	/**
	 * Automaton name.
	 */
  private String symbol;
	
	/**
	 * This creates automaton node named <code>symbol</code>.
	 * If <code>isFinal</code> is set it will be an accepting node.
	 * 
	 * @param isFinal determines whether it is an accepting node
	 * @param symbol name of the node
	 */
	public AN(boolean isFinal, String symbol) {
		edges = new HashMap<Character, AN>();
		my_index_counter = new Counter(0);
		this.isFinal = isFinal;
		this.symbol = symbol;
	}
	
	/**
	 * Adds node <code>a</code> to the automaton. <br>
	 * Makes outgoing edge labeled <code>c</code> leading
	 * to node <code>a</code>. After calling this functions
	 * both current node and node <code>a</code> shares the
	 * same current position counter, which is the original
	 * current node counter.
	 * 
	 * @param c edge label
	 * @param a a node to which the edge leads
	 */
	public void set(char c, AN a) {
	  a.setIndexCounter(my_index_counter);
		edges.put(c, a);
	}
	
	/**
	 * Makes outgoing edges labeled with digits leading to node
	 * <code>a</code>.
	 * 
	 * @param a a node to which the edges leads
	 */
	public void setDigit(AN a) {
		for (int i = 0; i < 10; i++) set(Integer.toString(i).charAt(0), a);
	}
	
	 /**
   * Makes outgoing edges labeled with floating point type symbols
   * (d, D, f, F) leading to node <code>a</code>.
   * 
   * @param a a node to which the edges leads
   */
	public void setSymbol(AN a) {
		set('d', a);
		set('D', a);
		set('f', a);
		set('F', a);
	}
	
	/**
	 * Reads character at position <code>index</code> from string
	 * <code>line</code>. If there is outgoing edge labeled with
	 * that character it proceeds to the node to which this edge leads.
	 * If there is no such edge false is returned if we aren't in 
	 * accepting node and true otherwise. If the whole string
	 * <code>line</code> has been read true is returned if we are in
	 * accepting node and false otherwise.
	 * 
	 * @param line a string which the automaton processes
	 * @param index current position in <code>line</code>
	 * @return true if automaton accepts <code>line</code>, false
	 * otherwise
	 */
	public boolean exec(String line, int index) {
	  my_index_counter.setValue(index);
		if (index == line.length()) {
			//System.err.println("Node: " + symbol + ", final: " + isFinal);
			return isFinal;
		}
		for (Character c: edges.keySet()) {
			if (c == line.charAt(index)) {
				//System.err.println("Node: " + symbol + ", read: " + c + ", index: " + index + ", length: " + line.length());
				return edges.get(c).exec(line, index + 1);
			}
		}
		if (isFinal) return true;
		return false;
	}
	
	/**
	 * This method returns the current position in processed string.
	 * After automaton accepted string an {@link AN#exec(String, int)}
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
	public void setIndexCounter(Counter a_counter) {
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
	public static AN constructAutomaton() {
    AN a = new AN(false, "a");
    AN b = new AN(false, "b");
    AN c = new AN(false, "c");
    AN d = new AN(false, "d");
    AN e = new AN(false, "e");
    AN f = new AN(true, "f");
    AN g = new AN(true, "g");
    AN h = new AN(false, "h");
    AN i = new AN(false, "i");
    AN j = new AN(true, "j");
    AN k = new AN(true, "k");
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
	  public Counter(int a_value) {
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
    public void setValue(int a_value) {
      my_value = a_value;
    }
	  
	}
	
}
