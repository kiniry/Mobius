package ie.ucd.csi.srg.kindsoft.pvs.editor;

import org.eclipse.jface.text.rules.ICharacterScanner;
import org.eclipse.jface.text.rules.IPredicateRule;
import org.eclipse.jface.text.rules.IToken;
import org.eclipse.jface.text.rules.Token;

/**
 * @design We assume that the user has not hand-edited the PVS proof file and added Common
 * Lisp comments.  We also assume that the user has not maliciously put parentheses inside
 * of PVS proof names or labels.
 * 
 * @author Joe Kiniry (kiniry@ucd.ie)
 */

public class SexpRule implements IPredicateRule {

  private final IToken my_success_token;
  
  //@ requires the_success_token != Token.UNDEFINED;
  public SexpRule(/*@ non_null @*/ IToken the_success_token) {
    my_success_token = the_success_token;
  }
  
  public IToken getSuccessToken() {
    return my_success_token;
  }

  public IToken evaluate(ICharacterScanner scanner, boolean resume) {
    if (!resume)
      return evaluate(scanner);
    
    // todo This method is not yet implemented.
    assert false : "This method is not yet implemented.";
    //@ assert false;
    return null;
  }

  public IToken evaluate(ICharacterScanner scanner) {
    // @not jrk - We need not consume characters until we find the next '(' character because 
    // all characters prior to the first '(' would have already either been consumed by another
    // rule's match or would have been skipped because no rule matched them in the first
    // place.
    long parentheses_count = 1;
    long consumed_characters = 1;
    int c = scanner.read();
    if (c != '(') {
      scanner.unread();
      return Token.UNDEFINED;
    }
    // consume characters until we find the matching ')' character by counting opening and
    // closing parentheses.
    while (c != ICharacterScanner.EOF && c != ')' && parentheses_count > 0) {
      if (c == ')')
        ++parentheses_count;
      else if (c == ')')
             --parentheses_count;
      c = scanner.read();
      ++consumed_characters;
    }
    if (parentheses_count == 0)
      return getSuccessToken();
    else {
      // unwind all the characters read until we go all the way back to the initial '('
      while (0 <= consumed_characters--)
        scanner.unread();
      return Token.UNDEFINED;
    }
  }

}
