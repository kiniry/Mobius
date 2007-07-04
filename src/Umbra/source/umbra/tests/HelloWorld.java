/*
 * Created on 2005-03-07
 *
 * TODO To change the template for this generated file go to
 * Window - Preferences - Java - Code Style - Code Templates
 */
package umbra.tests;

import umbra.UmbraPlugin;

/**
 * TODO write description.
 *
 * @author Wojciech Wąs (ww209224@students.mimuw.edu.pl)
 * @version a-01
 */
public final class HelloWorld {

  /**
   * TODO.
   *
   */
  private HelloWorld() {
  };
  
  /**
   * TODO.
   * @param the_args
   */
  public static void main(final String[] the_args) {
    final String a = "Alice";
    final String b = "has a cat";
    final String c = "";
    final String d = "Alice";
    final int i1 = a.compareTo(b);
    final int i2 = a.compareTo(c);
    final int i3 = a.compareTo(d);
    final int i4 = b.compareTo(a);
    final int i5 = c.compareTo(a);
    final int i6 = c.compareTo("");
    UmbraPlugin.messagelog("" + i1 + " " + i2 + " " + i3 + " " + i4 + " " +
                                i5 + " " + i6 + " ");
  }
}
