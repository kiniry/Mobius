package test;

import java.io.BufferedReader;
import java.io.CharArrayReader;
import java.io.IOException;

import annot.bcclass.BCClass;
import annot.io.ReadAttributeException;
import annot.textio.CodeFragment;

public class ParserTest {

  /**
   * @param args
   */
  public static void main(String[] args) {
    BCClass bcc;
    try {
      bcc = new BCClass(
            "/home/alx/workspace/BmlLib/bin/test",
            "Empty");
      String code = bcc.printCode();
      System.out.println(code);
      code = preProcess(code);
      System.out.println("--------------------------------");
      System.out.println(code);
      CodeFragment fgm = new CodeFragment(bcc, code);
      fgm.performChanges();
      if (!fgm.isCorrect())
        System.out.println("ERROR:" + fgm.getErrMsg());
    } catch (ClassNotFoundException e) {
      // TODO Auto-generated catch block
      e.printStackTrace();
    } catch (ReadAttributeException e) {
      // TODO Auto-generated catch block
      e.printStackTrace();
    }

  }

  /**
   * This method strips out the one-line comments and BML signs @ at the
   * beginning of a line, but inside a BML comment.
   *
   * @param code
   * @return
   */
  private static String preProcess(String code) {
      StringBuffer buf = new StringBuffer(code.length());
      int i = 0;
      while ( i < code.length()) {
        char ch = code.charAt(i);
        if ( ch == '"') {
          int opos = i;
          i = readString(i, code);
          buf.append(code.substring(opos, i));
          continue;
        } else if ( ch == '/') {
          i++;
          ch = code.charAt(i);
          if ( ch == '/') {
            i = readOneLineComment(i, code);
            continue;
          } else if ( code.substring(i).startsWith("*@") ) {
            buf.append('/');
            i = readBMLComment(i, code, buf);
            continue;
          } else {
            buf.append('/');
          }
        }
        buf.append(ch);
        i++;
      }
      return buf.toString();
  }

  private static int readBMLComment(int pos, String code, StringBuffer buf) {
    int i = pos;
    boolean newline = false;
    while (i < code.length()) {
      char ch = code.charAt(i);
      if ( ch == '@' && newline ) {
        newline = false;
        if (code.substring(i).startsWith("@*/")) {
          buf.append("@*/");
          return i + 3;
        } else {
          i++;
          continue;
        }
      } else if ( ch == '\n' ) {
        newline = true;
      } else if ( !Character.isWhitespace(ch) && newline ) {
        newline = false;
      }
      buf.append(ch);
      i++;
    }
    return 0;
  }

  private static int readOneLineComment(int pos, String code) {
    int i = ++pos;
    while (i < code.length()) {
      char ch = code.charAt(i);
      if ( ch == '\n' ) {
        return i;
      }
      i++;
    }
    return i;
  }

  private static int readString(int pos, String code) {
    int i = ++pos;
    while (i < code.length()) {
      char ch = code.charAt(i);
      if ( ch == '\\' ) {
        i++;
        ch = code.charAt(i);
        continue;
      } else if ( ch == '"' ) {
        return ++i;
      }
      i++;
    }
    return i;
  }

}
