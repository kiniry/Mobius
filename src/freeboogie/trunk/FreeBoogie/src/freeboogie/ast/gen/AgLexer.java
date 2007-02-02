/** Public domain. */

package freeboogie.ast.gen;

import java.io.IOException;

import freeboogie.util.Err;

/**
 * Recognizes abstract gramamr (AG) tokens.
 * 
 * @author rgrig 
 * @author reviewed by TODO
 */
public class AgLexer extends PeekStream<AgToken> {
  
  private CharStream stream;
  private Character lastChar;
  private StringBuilder repBuilder;
  
  /**
   * Initializes the lexer.
   * @param stream the underlying stream
   */
  public AgLexer(CharStream stream) {
    super(new TokenLocation());
    this.stream = stream;
    repBuilder = new StringBuilder();
  }
  
  private void readChar() throws IOException {
    repBuilder.append(lastChar);
    lastChar = stream.next();
  }

  private String rep() {
    String r = repBuilder.toString();
    repBuilder = new StringBuilder();
    return r;
  }
  
  /*
   * This method always reads one more character than the recognized
   * token and also eats the read characters from the underlying stream.
   * 
   * TODO: decide if you keep this method as complex as it stands (likely)
   *       and, if so, explain why
   * 
   * @see freeboogie.ast.gen.PeekStream#read()
   */
  @Override
  public AgToken read() throws IOException {
    AgToken.Type type = null;
    if (lastChar == null) return null;
    else if (lastChar == '=') {
      type = AgToken.Type.EQ;
      readChar();
    } else if (lastChar == '!') {
      type = AgToken.Type.BANG;
      readChar();
    } else if (lastChar == ',') {
      type = AgToken.Type.COMMA;
      readChar();
    } else if (lastChar == '(') {
      type = AgToken.Type.LP;
      readChar();
    } else if (lastChar == ')') {
      type = AgToken.Type.RP;
      readChar();
    } else if (Character.isWhitespace(lastChar)) {
      do readChar();
      while (Character.isWhitespace(lastChar));
      type = AgToken.Type.WS;
    } else if (lastChar == ':') {
      readChar();
      if (lastChar == '>') { 
        type = AgToken.Type.SUPERTYPE;
        readChar();
      } else 
        type = AgToken.Type.COLON;
    } else if (lastChar == '/') {
      readChar();
      if (lastChar != '/') type = AgToken.Type.ERROR;
      else {
        type = AgToken.Type.COMMENT;
        while (lastChar != '\n') readChar();
        readChar();
      }
    } else if (Character.isLetter(lastChar)) {
      do readChar();
      while (Character.isLetter(lastChar));
      if (repBuilder.toString().equals("enum")) 
        type = AgToken.Type.ENUM;
      else type = AgToken.Type.ID;
    } else {
      type = AgToken.Type.ERROR;
      readChar();
    }
    
    stream.eat();
    return new AgToken(type, rep());
  }
  
  /**
   * Like {@code next}, but skips WS, COMMENT, and ERROR tokens.
   * It also gives error messages for ERROR tokens.
   * @return the next good token
   * @throws IOException if thrown by the underlying stream
   */
  public AgToken nextGood() throws IOException {
    AgToken r;
    do {
      r = next(); 
      if (r.type == AgToken.Type.ERROR) {
        Err.error("I'm ignoring the yucky character '" 
          + r.rep + "' at " + getLoc());
      }
    } while (!r.isGood());
    return r;
  }
  
  /**
   * For testing. (TODO)
   * 
   * @param args
   */
  public static void main(String[] args) {
  // TODO Auto-generated method stub

  }
}
