package umbra.tests;
/*
 * Created on 2005-03-07
 *
 * TODO To change the template for this generated file go to
 * Window - Preferences - Java - Code Style - Code Templates
 */

/**
 * @author Wojtek W±s
 *
 * TODO write description
 */

public class HelloWorld {

  public static void main(String[] args) {
    String a = "Alice";
    String b = "has a cat";
    String c = "";
    String d = "Alice";
    int i1 = a.compareTo(b);
    int i2 = a.compareTo(c);
    int i3 = a.compareTo(d);
    int i4 = b.compareTo(a);
    int i5 = c.compareTo(a);
    int i6 = c.compareTo("");
    System.out.println("" + i1 + " " + i2 + " " + i3 + " " + i4 + " " + i5 + " " + i6 + " ");

  }
}
