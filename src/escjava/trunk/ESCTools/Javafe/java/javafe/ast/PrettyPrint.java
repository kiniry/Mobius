/* Copyright 2000, 2001, Compaq Computer Corporation */

package javafe.ast;

import java.io.OutputStream;
import java.io.ByteArrayOutputStream;
import java.io.IOException;

import javafe.util.Assert;
import javafe.util.Location;

// FIXME - should this write Strings instead of bytes?
public abstract class PrettyPrint {
  
  /*****************************************************************************
   * * Creation & delegation support: * *
   ****************************************************************************/
  
  /**
   * The only instance front-end code should use to pretty print information.
   * <p>
   * 
   * Will be some subclass of PrettyPrint; defaults to an instance of
   * StandardPrettyPrint. Extensions should replace with an instance that
   * understands how to pretty print the extensions.
   */
  public static/*@ non_null */PrettyPrint inst = new StandardPrettyPrint();
  
  /**
   * When an instance of PrettyPrint wishes to call itself recursively, it does
   * not do so by using this, but rather by using this explicit self instance
   * variable.
   * <p>
   * 
   * This allows instances of PrettyPrint to be extended at runtime (rather than
   * by compile-time static subclassing) using the DelegatingPrettyPrint class.
   * See javafe.tc.TypePrint for an example of how this may be done.
   */
  public /*@ non_null */ PrettyPrint self;
  
  /**
   * Create a normal instance of PrettyPrint that does not have a runtime
   * extension.
   */
  protected PrettyPrint() {
    this.self = this;
  }
  
  /**
   * Create an instance of PrettyPrint that has a runtime extension.
   * <p>
   * 
   * Self should be an instance of DelegatingPrettyPrint that eventually calls
   * us after some amount of filtering.
   */
  protected PrettyPrint(/*@ non_null */ PrettyPrint self) {
    this.self = self;
  }
  
  /*****************************************************************************
   * * Variables controling printing: * *
   ****************************************************************************/
  
  public static int INDENT = 3;
  
  /**
   * Should we display code that is inferred?
   * <p>
   * 
   * E.g., the inferred "this.", superclass constructor calls, etc.
   */
  public static boolean displayInferred = false;
  
  /*****************************************************************************
   * * Procedures to print various things: * *
   ****************************************************************************/
  
  /**
   * Print a compilation onto to a stream. Works best when <code>o</code> is
   * positioned at the start of a new line.
   */
  
  public abstract void print(/*@ non_null */ OutputStream o, CompilationUnit cu);
  
  /**
   * Print a type declaration onto to a stream.
   * <p>
   * 
   * Ends with a newline.
   * <p>
   */
  public void print(/*@ non_null */ OutputStream o, int ind, TypeDecl d) {
    printnoln(o, ind, d);
    writeln(o);
  }
  
  /**
   * Print a type declaration onto to a stream, without a final newline.
   * <p>
   */
  public abstract void printnoln(/*@ non_null */ OutputStream o, int ind, TypeDecl d);
  
  /**
   * Print a statement. Assumes that <code>s</code> should be printed starting
   * at the current position of <code>o</code>. It does <em>not</em> print
   * a new-line at the end of the statement. However, if the statement needs to
   * span multiple lines (for example, because it has embedded statements), then
   * these lines are indented by <code>ind</code> spaces.
   */
  
  public abstract void print(/*@ non_null */ OutputStream o, int ind, Stmt s);
  
  /**
   * Print a member or static initializer of a type declaration. Assumes that
   * <code>s</code> should be printed starting at the current position of
   * <code>o</code>. If the declaration needs to span multiple lines (for
   * example, to print the statements in the body of a method), then these lines
   * are indented by <code>ind</code> spaces. It should leave <code>o</code>
   * at the start of a new-line.
   */
  
  //@ requires o != null && classId != null;
  //@ requires d != null ==> d.hasParent;
  public abstract void print(/*@ non_null */ OutputStream o, int ind, TypeDeclElem d,
      Identifier classId, boolean showBody);
  
  public abstract void print(/*@ non_null */ OutputStream o, TypeNameVec tns);
  
  public abstract void print(/*@ non_null */ OutputStream o, int ind, FormalParaDeclVec fps);
  
  public abstract void print(/*@ non_null */ OutputStream o, int ind, ExprVec es);
  
  public abstract void print(/*@ non_null */ OutputStream o, GenericVarDecl d);
  
  public abstract void print(/*@ non_null */ OutputStream o, int ind, LocalVarDecl d,
      boolean showBody);
  
  public abstract void print(/*@ non_null */ OutputStream o, int ind, FieldDecl d,
      boolean showBody);
  
  public abstract void print(/*@ non_null */ OutputStream o, Type t);
  
  public abstract void print(/*@ non_null */ OutputStream o, Name n);
  
  public abstract void print(/*@ non_null */ OutputStream o, int ind, ObjectDesignator od);
  
  public abstract void print(/*@ non_null */ OutputStream o, int ind, VarInit e);
  
  /**
   * Print a lexical pragma. Assumes <code>o</code> is at the start of the
   * line; should leave <code>o</code> at the start of a new line.
   */
  
  //@ requires o != null && lp != null;
  public abstract void print(/*@ non_null */ OutputStream o, LexicalPragma lp);
  
  //@ requires o != null && tp != null;
  public abstract void print(/*@ non_null */ OutputStream o, int ind, TypeDeclElemPragma tp);
  
  /**
   * TODO Fill in class description
   * 
   * @author David R. Cok
   */

  /**
   * Print a member or static initializer of a type declaration. Assumes that
   * <code>s</code> should be printed starting at the current position of
   * <code>o</code>. If the declaration needs to span multiple lines (for
   * example, to print the statements in the body of a method), then these lines
   * are indented by <code>ind</code> spaces. It should leave <code>o</code>
   * at the start of a new-line.
   */
  
  //@ requires o != null && mp != null;
  public abstract void print(/*@ non_null */ OutputStream o, int ind, ModifierPragma mp);
  
  //@ requires o != null && sp != null;
  public abstract void print(/*@ non_null */ OutputStream o, int ind, StmtPragma sp);
  
  //@ requires o != null && tp != null;
  public abstract void print(/*@ non_null */ OutputStream o, int ind, TypeModifierPragma tp);
  
  /**
   * Writes an Object (a type of ASTNode) to the given PrintStream, followed by
   * an end-of-line.
   * 
   * @param out The PrintStream to write to
   * @param e The expression to write
   */
  public void println(/*@ non_null */ java.io.PrintStream out, Object e) {
    out.println(e.toString());
  }
  
  /**
   * Writes an Expr (a type of ASTNode) to the given PrintStream, followed by an
   * end-of-line.
   * 
   * @param out The PrintStream to write to
   * @param e The expression to write
   */
  public void println(/*@ non_null */ java.io.PrintStream out, Expr e) {
    print(out, 0, e);
    out.println("");
  }
  
  /**
   * Writes an ObjectDesignator (a type of ASTNode) to the given PrintStream,
   * followed by an end-of-line.
   * 
   * @param out The PrintStream to write to
   * @param e The expression to write
   */
  public void println(/*@ non_null */ java.io.PrintStream out, ObjectDesignator e) {
    print(out, 0, e);
    out.println("");
  }
  
  //// toString methods
  
  /**
   * Returns a canonical text representation for literal values. Requires
   * <code>tag</code> is one of constants on the left of this table:
   * 
   * <center><code><table>
   <tr> <td> TagConstants.BOOLEANLIT </td> <td> Boolean </td> </tr>
   <tr> <td> TagConstants.CHARLIT </td>   <td> Integer </td> </tr>
   <tr> <td> TagConstants.DOUBLELIT </td> <td> Double </td> </tr>
   <tr> <td> TagConstants.FLOATLIT </td>  <td> Float </td> </tr>
   <tr> <td> TagConstants.INTLIT </td>    <td> Integer </td> </tr>
   <tr> <td> TagConstants.LONGLIT </td>   <td> Long </td> </tr>
   <tr> <td> TagConstants.STRINGLIT </td> <td> String </td> </tr>
   </center></code> </table>
   * 
   * and that <code>val</code> is an instance of the corresponding type on the
   * right.
   */
  
  /*
   * @ requires ( (tag==TagConstants.BOOLEANLIT) || (tag==TagConstants.INTLIT) ||
   * (tag==TagConstants.LONGLIT) || (tag==TagConstants.FLOATLIT) ||
   * (tag==TagConstants.DOUBLELIT) || (tag==TagConstants.STRINGLIT) ||
   * (tag==TagConstants.CHARLIT) );
   */
  /*
   * @ requires ( ((tag==TagConstants.BOOLEANLIT) ==> (val instanceof Boolean)) &&
   * ((tag==TagConstants.INTLIT) ==> (val instanceof Integer)) &&
   * ((tag==TagConstants.LONGLIT) ==> (val instanceof Long)) &&
   * ((tag==TagConstants.FLOATLIT) ==> (val instanceof Float)) &&
   * ((tag==TagConstants.DOUBLELIT) ==> (val instanceof Double)) &&
   * ((tag==TagConstants.STRINGLIT) ==> (val instanceof String)) &&
   * ((tag==TagConstants.CHARLIT) ==> (val instanceof Integer)) );
   */
  //@ ensures \result != null;
  public static String toCanonicalString(int tag, Object val) {
    if (tag == TagConstants.BOOLEANLIT) return val.toString();
    if (tag == TagConstants.DOUBLELIT) return val.toString() + "D";
    if (tag == TagConstants.FLOATLIT) return val.toString() + "F";
    
    if (tag == TagConstants.INTLIT) {
      //@ assert val instanceof Integer;
      int v = ((Integer)val).intValue();
      if (v == Integer.MIN_VALUE) return "0x80000000";
      else if (v < 0) return "0x" + Integer.toHexString(v);
      else return Integer.toString(v);
    }
    
    if (tag == TagConstants.LONGLIT) {
      long v = ((Long)val).longValue();
      if (v == Long.MIN_VALUE) return "0x8000000000000000L";
      else if (v < 0) return "0x" + Long.toHexString(v) + "L";
      else return Long.toString(v) + "L";
    }
    
    if (tag == TagConstants.CHARLIT || tag == TagConstants.STRINGLIT) {
      char quote;
      if (tag == TagConstants.CHARLIT) {
        quote = '\'';
        val = new Character((char)((Integer)val).intValue());
      } else quote = '\"';
      String s = val.toString();
      StringBuffer result = new StringBuffer(s.length() + 2);
      result.append(quote);
      for (int i = 0, len = s.length(); i < len; i++) {
        char c = s.charAt(i);
        switch (c) {
          case '\b':
            result.append("\\b");
            break;
          case '\t':
            result.append("\\t");
            break;
          case '\n':
            result.append("\\n");
            break;
          case '\f':
            result.append("\\f");
            break;
          case '\r':
            result.append("\\r");
            break;
          case '\"':
            result.append("\\\"");
            break;
          case '\'':
            result.append("\\'");
            break;
          case '\\':
            result.append("\\\\");
            break;
          default:
            if (32 <= c && c < 128) result.append(c);
            else {
              result.append("\\u");
              for (int j = 12; j >= 0; j -= 4)
                result.append(Character.forDigit((c >> j) & 0xf, 16));
            }
        }
      }
      result.append(quote);
      return result.toString();
    }
    
    Assert.precondition(false);
    return null; // Dummy
  }
  
  //@ ensures \result != null;
  public String toString(int tag) {
    // Best version available in the front end:
    return javafe.tc.TagConstants.toString(tag);
  }
  
  //@ ensures \result != null;
  public final String toString(TypeNameVec tns) {
    ByteArrayOutputStream result = new ByteArrayOutputStream(20);
    print(result, tns);
    return result.toString();
  }
  
  //@ ensures \result != null;
  public final String toString(FormalParaDeclVec fps) {
    ByteArrayOutputStream result = new ByteArrayOutputStream(20);
    print(result, 0, fps);
    return result.toString();
  }
  
  //@ ensures \result != null;
  public final String toString(ExprVec es) {
    ByteArrayOutputStream result = new ByteArrayOutputStream(20);
    print(result, 0, es);
    return result.toString();
  }
  
  //@ ensures \result != null;
  public final String toString(GenericVarDecl d) {
    ByteArrayOutputStream result = new ByteArrayOutputStream(20);
    print(result, d);
    return result.toString();
  }
  
  //@ ensures \result != null;
  public final String toString(LocalVarDecl d, boolean showBody) {
    ByteArrayOutputStream result = new ByteArrayOutputStream(20);
    print(result, 0, d, showBody);
    return result.toString();
  }
  
  //@ ensures \result != null;
  public final String toString(FieldDecl d, boolean showBody) {
    ByteArrayOutputStream result = new ByteArrayOutputStream(20);
    print(result, 0, d, showBody);
    return result.toString();
  }
  
  //@ ensures \result != null;
  public final String toString(Type t) {
    ByteArrayOutputStream result = new ByteArrayOutputStream(20);
    print(result, t);
    return result.toString();
  }
  
  //@ ensures \result != null;
  public final String toString(Name n) {
    ByteArrayOutputStream result = new ByteArrayOutputStream(20);
    print(result, n);
    return result.toString();
  }
  
  //@ ensures \result != null;
  public final String toString(VarInit e) {
    ByteArrayOutputStream result = new ByteArrayOutputStream(20);
    print(result, 0, e);
    return result.toString();
  }
  
  //@ ensures \result != null;
  public final String toString(ObjectDesignator od) {
    ByteArrayOutputStream result = new ByteArrayOutputStream(20);
    print(result, 0, od);
    return result.toString();
  }
  
  //// Helper methods
  
  //@ requires o != null;
  public static void writeln(OutputStream o) {
    write(o, '\n');
  }
  
  //@ requires o != null && s != null;
  public static void writeln(OutputStream o, String s) {
    write(o, s);
    write(o, '\n');
  }
  
  //@ requires o != null;
  public static void write(OutputStream o, char c) {
    try {
      o.write((byte)c);
    } catch (IOException e) {
      Assert.fail("IO exception");
    }
  }
  
  //@ requires o != null && s != null;
  public static void write(OutputStream o, String s) {
    byte[] outBuf = s.getBytes();
    try {
      o.write(outBuf);
    } catch (IOException e) {
      Assert.fail("IO Exception");
    }
  }
  
  //@ requires o != null;
  public static void spaces(/*@ non_null */ OutputStream o, int number) {
    try {
      while (number > 0) {
        int i = Math.min(number, _spaces.length);
        o.write(_spaces, 0, i);
        number -= i;
      }
    } catch (IOException e) {
      Assert.fail("IO Exception");
    }
  }
  
  //@ private invariant _spaces != null;
  private static byte[] _spaces = { (byte)' ', (byte)' ', (byte)' ', (byte)' ',
                                    (byte)' ', /* 5 spaces */
                                    (byte)' ', (byte)' ', (byte)' ', (byte)' ',
                                    (byte)' ', /* 5 spaces */
                                    (byte)' ', (byte)' ', (byte)' ', (byte)' ',
                                    (byte)' ', /* 5 spaces */
                                    (byte)' ', (byte)' ', (byte)' ', (byte)' ',
                                    (byte)' ', /* 5 spaces */
                                    (byte)' ', (byte)' ', (byte)' ', (byte)' ',
                                    (byte)' ', /* 5 spaces */
                                   (byte)' ', (byte)' ', (byte)' ', (byte)' ',
                                   (byte)' ' /* 5 spaces */
  };
}
