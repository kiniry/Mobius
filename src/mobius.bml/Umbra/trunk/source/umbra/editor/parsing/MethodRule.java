/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) 2006-2009 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.editor.parsing;

import org.eclipse.jface.text.rules.ICharacterScanner;
import org.eclipse.jface.text.rules.IPredicateRule;
import org.eclipse.jface.text.rules.IToken;
import org.eclipse.jface.text.rules.Token;

/**
 * @author alx
 * @version a-01
 *
 */
public class MethodRule implements IPredicateRule {


  /**
   * The cached success token.
   */
  private IToken my_token;

  /**
   * The constructor which defines the success token.
   *
   * @param a_head the success token for this rule
   */
  public MethodRule(final IToken a_head) {
    my_token = a_head;
  }

  /**
   * Evaluates the rule by examining the characters available from
   * the provided character scanner. If the text that the rule investigated
   * does not match the rule's requirements the method returns
   * {@link Token#UNDEFINED}. Otherwise, this method returns this rule's success
   * token.
   * If this rules relies on a text pattern comprising a opening and a closing
   * character sequence this method can also be called when the scanner is
   * positioned already between the opening and the closing sequence.
   * In this case, <code>resume</code> must be set to <code>true</code>.
   *
   * @param a_scanner the character scanner to be used by this rule
   * @param a_resume indicates that the rule starts working between the
   *   opening and the closing character sequence
   * @return the token computed by the rule
   */
  public IToken evaluate(final ICharacterScanner a_scanner,
                         final boolean a_resume) {
    boolean dot = false;
    int c;
    if (a_resume) {
      return scanClosingParen(a_scanner);
    }
    while (true) {
      if (scanIdent(a_scanner)) {
        c = a_scanner.read();
        if (Character.isWhitespace(c)) {
          scanWhitespace(a_scanner);
          dot = false;
          continue;
        } else if (c == '.') {
          dot = true;
          continue;
        } else {
          break;
        }
      } else {
        return Token.UNDEFINED;
      }
    }

    if (dot) return Token.UNDEFINED;

    if (c == '(') {
      while (true) {
        c = a_scanner.read();
        if (c == ')') return my_token;
        if (c == '\n') {
          a_scanner.unread();
          return Token.UNDEFINED;
        }
      }
    }

    return Token.UNDEFINED;
  }

  /**
   * @param a_scanner
   * @param cha
   * @return
   */
  private IToken scanClosingParen(final ICharacterScanner a_scanner) {
    while (true) {
      final int c = a_scanner.read();
      if (c == ')') return my_token;
      if (c == '\n' || c == ICharacterScanner.EOF) {
        a_scanner.unread();
        return Token.UNDEFINED;
      }
    }
  }


  /**
   * @param a_scanner
   */
  private void scanWhitespace(ICharacterScanner a_scanner) {
    do {
      final int c = a_scanner.read();
      if (!Character.isWhitespace(c)) {
        break;
      }
    } while (true);
    a_scanner.unread();
  }

  /**
   * The method scans in a method identifier. These include also "&lt;init&gt;"
   * and "&lt;clinit&gt;" bytecode identifiers.
   *
   * @param a_scanner the scanner to read the identifier from
   * @return <code>true</code> in case an identifier is recognised
   */
  private boolean scanIdent(final ICharacterScanner a_scanner) {
    int c = a_scanner.read();
    final StringBuffer buf = new StringBuffer("");
    boolean ok = false;
    if (Character.isJavaIdentifierStart(c) || c == '<') {
      ok = true;
      if (c == '<') c = a_scanner.read();
      while (Character.isJavaIdentifierPart(c)) {
        buf.append((char)c);
        c = a_scanner.read();
      }
      final String res = buf.toString();
      if (c == '>' && (res.equals("init") || res.equals("clinit"))) return ok;
    }
    a_scanner.unread();
    return ok;
  }

  /**
   * Returns the success token for the rule.
   *
   * @return the success token
   */
  public IToken getSuccessToken() {
    return my_token;
  }

  /**
   * Evaluates the rule by examining the characters available from
   * the provided character scanner. If the text that the rule investigated
   * does not match the rule's requirements the method returns
   * {@link Token#UNDEFINED}. Otherwise, this method returns this rule's success
   * token.
   *
   * @param a_scanner the character scanner to be used by this rule
   * @return the token computed by the rule
   */
  public IToken evaluate(final ICharacterScanner a_scanner) {
    return evaluate(a_scanner, false);
  }


}
