package mobius.bico.coq;

import java.io.OutputStream;
import java.io.PrintStream;

import mobius.bico.Util;
/**
 * A stream to use instead of writeln.
 * 
 * @author J. Charles (julien.charles@inria.fr)
 */
class Stream extends PrintStream {
  /** the number of tabs. */
  private int fTab;
  /** the tabulations to add. */
  private String fStrTab = "";
  
  /**
   * Create a new stream from an existing one.
   * 
   * @param out
   *            an already existing stream
   */
  public Stream(final OutputStream out) {
    super(out);
  }
  
  /**
   * Write a line with a given tabulation.
   * 
   * @param tab
   *            the number of tabulation
   * @param s
   *            the string to write
   */
  public void println(final int tab, final String s) {
    if (tab < 0) {
      super.println(s.toString());
    }
    final StringBuffer str = new StringBuffer();
    for (int i = 0; i < tab; i++) {
      str.append(Util.TAB);
    }
    str.append(s);
    super.println(str.toString());
  }
  
  /**
   * Print the given string, but putting tabulations wherever necessary.
   * 
   * @param s
   *            the string to print tabbed
   */
  public void println(final String s) {
    String str = fStrTab + s;
    str = str.replaceAll("\n", "\n" + fStrTab);
    super.println(str);
  }
  
  /**
   * Increments the tabulation.
   */
  public void incTab() {
    fTab++;
    fStrTab += Util.TAB;
  }
  
  /**
   * Does a println and then increments the tabulation level.
   * 
   * @param s
   *            the string to print tabbed
   */
  public void incPrintln(final String s) {
    println(s);
    incTab();
  }
  
  /**
   * Decrements the tabulation and then does a println.
   * 
   * @param s
   *            the string to print tabbed
   */
  public void decPrintln(final String s) {
    decTab();
    println(s);
  }
  
  /**
   * Decrements the tabulations.
   */
  public void decTab() {
    if (fTab > 0) {
      fTab--;
      fStrTab = "";
      for (int i = 0; i < fTab; i++) {
        fStrTab += Util.TAB;
      }
    }
  }
  
  public void flush() {
    super.flush();
  }
  
  public void close() {
    super.close();
  }

}
