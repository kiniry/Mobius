package mobius.directvcgen.pojs;

import static com.sun.tools.javac.util.LayoutCharacters.CR;
import static com.sun.tools.javac.util.LayoutCharacters.FF;
import static com.sun.tools.javac.util.LayoutCharacters.LF;
import static com.sun.tools.javac.util.LayoutCharacters.TabInc;

import java.nio.CharBuffer;

import com.sun.tools.javac.parser.Scanner;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.Position;


/**
 * @deprecated Experimental
 * @author J. Charles (julien.charles@inria.fr)
 */
public class CommentScanner extends Scanner {

  /** A factory for creating scanners. */
  public static class Factory extends Scanner.Factory {
    /** 
     * Create a new scanner factory.
     * @param context 
     */
    protected Factory(final Context context) {
      super(context);
    }
    
    public static void preRegister(final Context context) {
      context.put(scannerFactoryKey, new Context.Factory<Scanner.Factory>() {
        public Factory make() {
          return new Factory(context);
        }
      });
    }

    

    /** {@inheritDoc} */
    @Override
    public Scanner newScanner(final CharSequence input) {
      if (input instanceof CharBuffer) {
        return new CommentScanner(this, (CharBuffer)input);
      }
      else {
        final char[] array = input.toString().toCharArray();
        return newScanner(array, array.length);
      }
    }

    /** {@inheritDoc} */
    @Override
    public Scanner newScanner(final char[] input, final int inputLength) {
      return new CommentScanner(this, input, inputLength);
    }
  }


  /** Create a scanner from the input buffer.  buffer must implement
   *  array() and compact(), and remaining() must be less than limit().
   */
  protected CommentScanner(final Factory fac, 
                           final CharBuffer buffer) {
      super(fac, buffer);
  }

  /** Create a scanner from the input array.  The array must have at
   *  least a single character of extra space.
   */
  protected CommentScanner(final Factory fac, final char[] input, 
                           final int inputLength) {
      super(fac, input, inputLength);
  }

  /** Starting position of the comment in original source. */
  private int fPos;

  /** The comment input buffer, index of next chacter to be read,
   *  index of one past last character in buffer.
   */
  private char[] buf;
  private int bp;
  private int buflen;

  /** The current character.
   */
  private char ch;

  /** The column number position of the current character.
   */
  private int col;

  /** The buffer index of the last converted Unicode character.
   */
  private int unicodeConversionBp = 0;

  /**
   * Buffer for doc comment.
   */
  private char[] docCommentBuffer = new char[1024];

  /**
   * Number of characters in doc comment buffer.
   */
  private int docCommentCount;

  /**
   * Translated and stripped contents of doc comment.
   */
  private String docComment = null;

  private boolean previousTokenComment = false;




  /** Unconditionally expand the comment buffer.
   */
  private void expandCommentBuffer() {
    final char[] newBuffer = new char[docCommentBuffer.length * 2];
    System.arraycopy(docCommentBuffer, 0, newBuffer,
                     0, docCommentBuffer.length);
    docCommentBuffer = newBuffer;
  }

  /** Convert an ASCII digit from its base (8, 10, or 16)
   *  to its value.
   */
  private int digit(final int base) {
    final char c = ch;
    final int result = Character.digit(c, base);
    if (result >= 0 && c > 0x7f) {
      ch = "0123456789abcdef".charAt(result);
    }
    return result;
  }

  /** Convert Unicode escape; bp points to initial '\' character
   *  (Spec 3.3).
   */
  private void convertUnicode() {
    if (ch == '\\' && unicodeConversionBp != bp) {
      bp++; ch = buf[bp]; col++;
      if (ch == 'u') {
        do {
          bp++; ch = buf[bp]; col++;
        } while (ch == 'u');
        final int limit = bp + 3;
        if (limit < buflen) {
          int d = digit(16);
          int code = d;
          while (bp < limit && d >= 0) {
            bp++; ch = buf[bp]; col++;
            d = digit(16);
            code = (code << 4) + d;
          }
          if (d >= 0) {
            ch = (char)code;
            unicodeConversionBp = bp;
            return;
          }
        }
        // "illegal.Unicode.esc", reported by base scanner
      } 
      else {
        bp--;
        ch = '\\';
        col--;
      }
    }
  }


  /** Read next character.
   */
  private void scanChar() {

    bp++;
    if (buf.length <= bp) {
      return;
    }
    ch = buf[bp];
    switch (ch) {
      case '\r': // return
        col = 0;
        break;
      case '\n': // newline
        if (bp == 0 || buf[bp - 1] != '\r') {
          col = 0;
        }
        break;
      case '\t': // tab
        col = (col / TabInc * TabInc) + TabInc;
        break;
      case '\\': // possible Unicode
        col++;
        convertUnicode();
        break;
      default:
        col++;
    }
  }

  /**
   * Read next character in doc comment, skipping over double '\' characters.
   * If a double '\' is skipped, put in the buffer and update buffer count.
   */
  private void scanDocCommentChar() {
    scanChar();
    if (ch == '\\') {
      if (buf[bp + 1] == '\\' && unicodeConversionBp != bp) {
        if (docCommentCount == docCommentBuffer.length) {
          expandCommentBuffer();
        }
        docCommentBuffer[docCommentCount++] = ch;
        bp++; col++;
      } 
      else {
        convertUnicode();
      }
    }
  }

  /**
   *  Reset doc comment before reading each new token.
   */
  @Override
  public void nextToken() {
    if (!previousTokenComment) { 
      docComment = null;
    }
    else {
      previousTokenComment = false;
    }
    super.nextToken();
    if (docComment != null && docComment.equals("")) {
      docComment = null;
    }
  }

  /**
   * @return the documentation string of the current token.
   */
  public String docComment() {
    return docComment;
  }

  /**
   * Process a doc comment and make the string content available.
   * Strips leading whitespace and stars.
   */
  @SuppressWarnings("fallthrough")
  protected void processComment(final CommentStyle style) {
    if (docComment == null) {
      docComment = "";
    }
    
    if (style == CommentStyle.JAVADOC) {
      previousTokenComment = true;

      // we skip java doc
      return;
    }
    else if (style == CommentStyle.LINE) {
      processLineComment(style);
      return;
    }
    fPos = pos();
    buf = getRawCharacters(fPos, endPos());
    buflen = buf.length;
    bp = 0;
    col = 0;

    docCommentCount = 0;
    
    boolean firstLine = true;

    // Skip over first slash
    scanDocCommentChar();
    // Skip over first star
    scanDocCommentChar();

    // consume any number of at (@)
    while (bp < buflen && (ch == '@' || ch == '*')) {
      scanDocCommentChar();
    }

    // is the comment in the form /**/, /***/, /****/, etc. ?
    if (bp < buflen && ch == '/') {
      docComment = "";
      return;
    }

    // skip a newline on the first line of the comment.
    if (bp < buflen) {
      if (ch == LF) {
        scanDocCommentChar();
        firstLine = false;
      } 
      else if (ch == CR) {
        scanDocCommentChar();
        if (ch == LF) {
          scanDocCommentChar();
          firstLine = false;
        }
      }
    }
    
  outerLoop:

      // The outerLoop processes the doc comment, looping once
      // for each line.  For each line, it first strips off
      // whitespace, then it consumes any stars, then it
      // puts the rest of the line into our buffer.
    while (bp < buflen) {

      // The wsLoop consumes whitespace from the beginning
      // of each line.
    wsLoop:
      
      while (bp < buflen) {
        switch(ch) {
          case ' ':
            scanDocCommentChar();
            break;
          case '\t':
            col = ((col - 1) / TabInc * TabInc) + TabInc;
            scanDocCommentChar();
            break;
          case FF:
            col = 0;
            scanDocCommentChar();
            break;
//Treat newline at beginning of line (blank line, no star)
//as comment text.  Old Javadoc compatibility requires this.
/*---------------------------------*
              case CR: // (Spec 3.4)
                  scanDocCommentChar();
                  if (ch == LF) {
                      col = 0;
                      scanDocCommentChar();
                  }
                  break;
              case LF: // (Spec 3.4)
                  scanDocCommentChar();
                  break;
*---------------------------------*/
          default:
            // we've seen something that isn't whitespace;
            // jump out.
            break wsLoop;
        }
      }

      // Are there stars here?  If so, consume them all
      // and check for the end of comment.
      if (ch == '*') {
        // skip all of the stars
        do {
          scanDocCommentChar();
        } while (ch == '*');
        
        // check for the closing slash.
        if (ch == '/') {
          // We're done with the doc comment
          // scanChar() and breakout.
          break outerLoop;
        }
      } 
      else if (!firstLine) {
        //The current line does not begin with a '*' so we will indent it.
        for (int i = 1; i < col; i++) {
          if (docCommentCount == docCommentBuffer.length) {
            expandCommentBuffer();
          }
          docCommentBuffer[docCommentCount++] = ' ';
        }
      }
    
    // The textLoop processes the rest of the characters
    // on the line, adding them to our buffer.
    textLoop:
      while (bp < buflen) {
        switch (ch) {
          case '*':
            // Is this just a star?  Or is this the
            // end of a comment?
            scanDocCommentChar();
            if (ch == '/') {
              // This is the end of the comment,
              // set ch and return our buffer.
              break outerLoop;
            }
            // This is just an ordinary star.  Add it to
            // the buffer.
            if (docCommentCount == docCommentBuffer.length) {
              expandCommentBuffer();
            }
            docCommentBuffer[docCommentCount++] = '*';
            break;
          case ' ':
          case '\t':
            if (docCommentCount == docCommentBuffer.length) {
              expandCommentBuffer();
            }
            docCommentBuffer[docCommentCount++] = ch;
            scanDocCommentChar();
            break;
          case FF:
            scanDocCommentChar();
            break textLoop; // treat as end of line
          case CR: // (Spec 3.4)
            scanDocCommentChar();
            if (ch != LF) {
              // Canonicalize CR-only line terminator to LF
              if (docCommentCount == docCommentBuffer.length) {
                expandCommentBuffer();
              }
              docCommentBuffer[docCommentCount++] = (char)LF;
              break textLoop;
            }
            /* fall through to LF case */
          case LF: // (Spec 3.4)
            // We've seen a newline.  Add it to our
            // buffer and break out of this loop,
            // starting fresh on a new line.
            if (docCommentCount == docCommentBuffer.length) {
              expandCommentBuffer();
            }
            docCommentBuffer[docCommentCount++] = ch;
            scanDocCommentChar();
            break textLoop;
          default:
            // Add the character to our buffer.
            if (docCommentCount == docCommentBuffer.length) {
              expandCommentBuffer();
            }
            docCommentBuffer[docCommentCount++] = ch;
            scanDocCommentChar();
        }
      } // end textLoop
      firstLine = false;
    } // end outerLoop

    if (docCommentCount > 0) {
      int i = docCommentCount - 1;
    trailLoop:
      while (i > -1) {
        switch (docCommentBuffer[i]) {
          case '*':
            i--;
            break;
          default:
            break trailLoop;
        }
      }
      docCommentCount = i + 1;

      // Store the text of the doc comment

      docComment += new String(docCommentBuffer, 0 , docCommentCount);
          
    } 
  }
  /**
   * Process a doc comment and make the string content available.
   * Strips leading whitespace and stars.
   */
  @SuppressWarnings("fallthrough")
  private void processLineComment(final CommentStyle style) {
    
    if (style != CommentStyle.LINE) {
      // there's something rotten in the kingdom of Danemark
      return;
    }

    fPos = pos();
    buf = getRawCharacters(fPos, endPos());
    buflen = buf.length;
    bp = 0;
    col = 0;

    docCommentCount = 0;
    
    //boolean firstLine = true;

    // Skip over first slash
    scanDocCommentChar();
    // Skip over second slash
    scanDocCommentChar();

    // consume any number of at (@)
    do {
      scanDocCommentChar();
    }  while (bp < buflen && (ch == '@' || ch == '*'));

    // is the comment in the form /**/, /***/, /****/, etc. ?
    if (bp < buflen && ch == '/') {
      docComment = "";
      return;
    }

    // skip a newline on the first line of the comment.
    if (bp < buflen) {
      if (ch == LF) {
        scanDocCommentChar();
        //firstLine = false;
      } 
      else if (ch == CR) {
        scanDocCommentChar();
        if (ch == LF) {
          scanDocCommentChar();
          //firstLine = false;
        }
      }
    }
    
    // The textLoop processes the rest of the characters
    // on the line, adding them to our buffer.
  textLoop:
    while (bp < buflen) {
      switch (ch) {
        case ' ':
        case '\t':
          if (docCommentCount == docCommentBuffer.length) {
            expandCommentBuffer();
          }
          docCommentBuffer[docCommentCount++] = ch;
          scanDocCommentChar();
          break;
        case FF:
          scanDocCommentChar();
          break textLoop; // treat as end of line
        case CR: // (Spec 3.4)
          scanDocCommentChar();
          if (ch != LF) {
            // Canonicalize CR-only line terminator to LF
            if (docCommentCount == docCommentBuffer.length) {
              expandCommentBuffer();
            }
            docCommentBuffer[docCommentCount++] = (char)LF;
            break textLoop;
          }
            /* fall through to LF case */
        case LF: // (Spec 3.4)
            // We've seen a newline.  Add it to our
            // buffer and break out of this loop,
            // starting fresh on a new line.
          if (docCommentCount == docCommentBuffer.length) {
            expandCommentBuffer();
          }
          docCommentBuffer[docCommentCount++] = ch;
          scanDocCommentChar();
          break textLoop;
        default:
          // Add the character to our buffer.
          if (docCommentCount == docCommentBuffer.length) {
            expandCommentBuffer();
          }
          docCommentBuffer[docCommentCount++] = ch;
          scanDocCommentChar();
      }
    } // end textLoop

    if (docCommentCount > 0) {
      // Store the text of the doc comment
      docComment =  docComment + new String(docCommentBuffer, 0 , docCommentCount);
    } 
  }

  /** Build a map for translating between line numbers and
   * positions in the input.
   *
   * @return a LineMap */
  public Position.LineMap getLineMap() {
    final char[] buff = getRawCharacters();
    return Position.makeLineMap(buff, buff.length, true);
  }
}
