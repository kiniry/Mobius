/*
 * Created on 2005-05-18
 */
package umbra.instructions;

import umbra.UmbraHelper;


/**
 * This is a class for a special Bytecode lines located after
 * the headers or at the end of the method,
 * containing some method data, not to be edited by a user.
 *
 * @author Tomek Batkiewicz (tb209231@students.mimuw.edu.pl)
 * @author Jarosław Paszek (jp209217@students.mimuw.edu.pl)
 * @version a-01
 */
public class CodeLineController extends BytecodeLineController {

  /**
   * TODO
   */
  public CodeLineController(final String l) {
    super(l);
  }

  /**
   * The line is correct if it contains one of four sets of
   * keywords. For lines starting with "Code" there is also
   * checked if all parameters are present reasonably set.
   * It is only for displaying information because modification of
   * these lines is not provided.
   *
   * @return <code>true</code> when the line contained in
   *         {@ref BytecodeLineController#line} contains a correct line from
   *         the bytecode file
   * @see BytecodeLineController#correct()
   */
  public final boolean correct() {
    //Code must exist because otherwise it would not be the class
    boolean res = false;
    if (this.line.startsWith("Code")) {
      res = correctCode();
    }
    if (this.line.startsWith("LineNumber")) {
      res = true;
    }
    if (this.line.startsWith("LocalVariable")) {
      res = correctLocalVariable();
    }
    if (this.line.startsWith("Attribute")) {
      res = correctAttribute();
    }

    return res;
  }

  /**
   * TODO
   */
  private boolean correctAttribute() {
    final String s = UmbraHelper.stripAllWhitespace(line);
    if ((s.indexOf("(s)=")) > -1) {
      return true;
    }
    return false;
  }

  /**
   * TODO
   */
  private boolean correctLocalVariable() {
    final String s = UmbraHelper.stripAllWhitespace(line);
    if ((s.indexOf("start_pc=")) > -1) {
      if ((s.indexOf("length=")) > -1) {
        if ((s.indexOf("index=")) > -1) {
          if ((line.indexOf("start_pc")) > -1) {
            if ((line.indexOf("length")) > -1) {
              if ((line.indexOf("index")) > -1) {
                return true;
              }
            }
          }
        }
      }
    }
    return false;
  }

  /**
   * TODO
   */
  private boolean correctCode() {
    if (!(line.indexOf("(") > 0))
      return false;

    final String s = UmbraHelper.stripAllWhitespace(line);
    int i = 0;
    //czy jest to co trzeba
    if (!(s.indexOf("max_stack=") > 0))
      return false;
    if (!(s.indexOf(",max_locals=") > 0))
      return false;
    if (!(s.indexOf(",code_length=") > 0))
      return false;
    //czy liczby sa poprawne
    for (i = UmbraHelper.getIndexAfter(s, "max_stack=");
         i < (s.indexOf(",max_locals=")); i++) {
      if (!(Character.isDigit(s.charAt(i))))
        return false;
    }
    for (i = UmbraHelper.getIndexAfter(s, ",max_locals=");
         i < (s.indexOf(",code_length=")); i++) {
      if (!(Character.isDigit(s.charAt(i))))
        return false;
    }
    for (i = UmbraHelper.getIndexAfter(s, ",code_length=");
         i < (s.indexOf(")")); i++) {
      if (!(Character.isDigit(s.charAt(i))))
        return false;
    }
    //is the sequence of items right?
    // XXX: probably not necessary because we do the check below
    if ((s.indexOf("Code")) > (s.indexOf("(")))
      return false;
    if ((s.indexOf("(")) > (s.indexOf("max_stack=")))
      return false;
    if ((s.indexOf("max_stack=")) > (s.indexOf(",max_locals=")))
      return false;
    if ((s.indexOf(",max_locals=")) > (s.indexOf(",code_length=")))
      return false;
    if ((s.indexOf(",code_length")) > (s.indexOf(")")))
      return false;
    //are there numbers at all
    if (isOneStrictlyAfterAnother(s, "max_stack=", ",max_locals="))
      return false;
    if (isOneStrictlyAfterAnother(s, ",max_locals=", ",code_length="))
      return false;
    if (isOneStrictlyAfterAnother(s, ",code_length=", ")"))
      return false;
    //czy nawiasy poprawnie tzn jak po ) cos to zle
    if ((s.indexOf(")")) + 1 < (s.length()))
      return false;

    //  czy kolejnosc ok
    if ((s.indexOf("Code")) < (s.indexOf("(")))
      if ((s.indexOf("(")) < (s.indexOf("max_stack=")))
        if ((s.indexOf("max_stack=")) < (s.indexOf(",max_locals=")))
          if ((s.indexOf(",max_locals=")) < (s.indexOf(",code_length=")))
            if ((s.indexOf(",code_length")) < (s.indexOf(")")))
              if ((s.indexOf("(")) < 5)
                if ((s.indexOf("max_stack=")) < 6)
                  return true;
    return false;
  }

  /**
   * TODO
   * @param s
   * @param string
   * @param string2
   * @return
   */
  private boolean isOneStrictlyAfterAnother(final String s,
                                            final String string1,
                                            final String string2) {
    final int len = string1.length() + 1;
    return ((s.indexOf(string1)) + len) > (s.indexOf(string2));
  }
}
