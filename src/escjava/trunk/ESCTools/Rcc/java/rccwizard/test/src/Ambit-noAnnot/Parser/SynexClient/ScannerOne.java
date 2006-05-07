// Copyright 1996 Digital Equipment Corporation. Distributed only by permission.

package Parser.SynexClient;

/** === This interface provides a (somewhat specialized) token scanner.
|
|   The ascii characters are divided into a fixed number of 
|   character classes which default to the following table:
|
|     Blank        HT LF FF CR SP
|     Reserved        " ' ~ DEL
|     Delimiter        ( )
|     Special        # $ % & * + - / : = < > @ \ ^ | , . ; [ ] _ { } ? !
|     Digit        0..9
|     Letter        A..Z ` a..z
|     Illegal        all the others
|
|   (N.B. Special characters can be changed to Delimiter by addDelimiter().)
|
|   Moreover, there are some "improper" character classes:
|
|     StringChar  is either any single character that is not Illegal
|                 or one of `'` `"` `\`, or is one of the pairs of
|                  characters `\'` `\"` `\\`.
|     Comment     is, recursively, a sequence of non-Illegal chars and
|                  Comments enclosed between `(*` and `*)`.
|     Eof          is the end-of-file token (optionally generated)
|
|  The stream of input characters is split into "lexemes" by always
|  extracting the longest prefix that is a legal lexeme.
|  The following fixed set of lexemes is recognized:
|
|     Space          a sequence of Blanks and Comments
|     AlphaNum          a sequence of Letters and Digits starting with a Letter
|     Symbol          a sequence of Specials
|     Char          a single StringChars enclosed between two `'`
|     String          a sequence of StringChars enclosed betweenn two `"`
|     Nat          a sequence of Digits
|     Int          a Nat, possibly preceded by a single `~`
|     Real          an Int followed by `.` and a Nat
|     Delimiter          a single Delimiter character
|     Eof          end-of-file (optionally generated)
|
|  Finally, the scanner produces "tokens" from the stream of lexemes:
|
|     - Space lexemes do not produce tokens.
|     - Char, String, Int, Real, Delimiter, and Eof lexemes are also tokens.
|     - AlphaNum and Symbol lexemes are Identifier tokens, except when
|         they have been explicitly declared to be keywoTextCrds, in which
|         case they are Keyword tokens.
|
|  Both Identifier and Keyword tokens are called Name tokens.
|  Name tokens are inserted in an internal symbol table; when they are
|  returned as texts they are unique.
|
|  The scanner scans characters out of a stack of input readers. When a reader
|  is exhausted the scanner switches to the next one in the stack; if the
|  stack is empty the scanner raises ScanFailureException. Initially, the only reader in
|  the stack is stdin, with generateEOF=TRUE (see PushInput); use PopInput
|  right away if you want to remove this reader.
|
| --- Here is a typical top-level loop for the scanner:
|
|    SynScan.SetPrompt("- ", "  ");
|    LOOP
|      TRY
|        SynScan.FirstPrompt();
|          IF SynScan.GetTokenEof() THEN RAISE SynScan.NoReader END;
|         (* ... *)
|        (* parse, execute, and print *)
|         (* ... *)
|             SynWr.Flush(swr);
|      EXCEPT
|      | SynScan.Fail => (* Continue. *)
|      | SynScan.NoReader => EXIT;
|      END;
|    END;
*/

import java.io.IOException;
import java.io.DataInputStream;

import java.lang.Integer;
import java.lang.Float;

import java.util.Hashtable;

import Parser.Synex.Scanner.Scanner;
import Parser.Synex.Scanner.Token;
import Parser.Synex.Scanner.TokenEOF;
import Parser.Synex.Scanner.ScanFailureException;

import Parser.SynexClient.TokenClient.TokenChar;
import Parser.SynexClient.TokenClient.TokenDelim;
import Parser.SynexClient.TokenClient.TokenInt;
import Parser.SynexClient.TokenClient.TokenIde;
import Parser.SynexClient.TokenClient.TokenKey;
import Parser.SynexClient.TokenClient.TokenReal;
import Parser.SynexClient.TokenClient.TokenString;

public class ScannerOne extends Scanner {

/** === A scanner */


/** CharacterEnum */

  private static final int IllegalCharEnum = 0;
  private static final int LetterCharEnum = 1;
  private static final int DigitCharEnum = 2;
  private static final int SpecialCharEnum = 3;
  private static final int DelimCharEnum = 4;
  private static final int ReservedCharEnum = 5;
  private static final int BlankCharEnum = 6;
  private static final int EofEnum = 7;

/** === PRIVATE FIELDS === */

  char[] scanBuffer;
  int scanBufferSize;
  
  Hashtable keySet;
  Hashtable ideSet;
  
  int[] charTable; // array [char] of CharacterEnum

/** === Constructors === */

  public ScannerOne() {
  /* The input stack is empty; must use pushInput to initialize */
    init();
  }
  
/** === Token Primitives === */

  public Token nextToken() throws ScanFailureException {
    /** Implements Scanner.nextToken() */
    char ch;   
    while (charTable[lookChar()%256] == BlankCharEnum) {
      ch = getChar();
    }
    ch = lookChar();
    int categ = charTable[ch%256];
    if (categ == LetterCharEnum) {
      scanAlphaNumIde();
      return scanBufferIde();
    } else if (categ == SpecialCharEnum) {
      scanSpecialIde();
      return scanBufferIde();
    } else if (categ == DelimCharEnum) {
      ch = getChar();
      if ((ch == '(') && (lookChar() == '*')) {
        ch = getChar();
        scanComment();
        return nextToken();
      } else {
        return new TokenDelim(ch);
      }
    } else if ((ch == '~') || (categ == DigitCharEnum)) {
      return scanNumber();
    } else if (ch == '\'') {
      return scanChar();
    } else if (ch == '\"') {
      return scanString();
    } else if (categ == EofEnum) {
      ch = getChar();
      return new TokenEOF();
    } else {
      ch = getChar();
      throw new ScanFailureException("Illegal Char");
    }
  }
  
  public void clear() {
    super.clear();
    scanBufferSize = 0;
  }
  
  public void addKeyword(String name) { 
    if (!keySet.containsKey(name)) {
      keySet.put(name, new TokenKey(name));
    }
  }
  
  public void addDelimiter(char ch) {
    if (charTable[ch%256] == SpecialCharEnum) {
      setChar(ch, DelimCharEnum);
    }
  }
  
/** === PRIVATE METHODS === */
  
  void scanComment() throws ScanFailureException {
    int level = 1;
    while (level > 0) {
      char ch = getChar();
      if (ch == EofChar) {
        throw new ScanFailureException("Comment still open at end of stream");
      }
      if (ch == '*') {
        if (lookChar() == ')') { ch = getChar(); level--; }
      } else if (ch == '(') {
        if (lookChar() == '*') { ch = getChar(); level++; }
      }
    }
  }
  
  TokenChar scanChar() throws ScanFailureException {
    char ch = getChar(); // initial quote
    ch = decodeChar();
    if (getChar() != '\'') {
      throw new ScanFailureException("closing \' expected");
    }
    return new TokenChar(ch);
  }
  
  char decodeChar() throws ScanFailureException {
    char ch0 = getChar();
    if (ch0 != '\\') { return ch0; }
    char ch1 = getChar();
    if (ch1 == 'n') { return '\n'; }
    if (ch1 == 'r') { return '\r'; }
    if (ch1 == 't') { return '\t'; }
    if (ch1 == 'f') { return '\f'; }
    if ((ch1 >= '0') && (ch1 <= '3')) {
      char ch2 = getChar();
      char ch3 = getChar();
      if ((ch2 < '0') || (ch2 >'7') || (ch3 < '0') || (ch3 >'7')) {
        throw new ScanFailureException("Ill-formed character escape sequence");
      }
      return (char)((ch1-'0')*64 + (ch2-'0')*8 + (ch3-'0'));
    }
    return ch1;
  }
  
  static void encodeCharToBuffer(char ch, StringBuffer buff) {
    if ((ch == '\\') || (ch == '\'') || (ch == '\"')) { 
      buff.append('\\'); buff.append(ch); return; 
    }
    if ((ch >= ' ') && (ch <= '~')) { buff.append(ch); return; }
    buff.append('\\');
    if (ch == '\n') { buff.append('n'); return; }
    if (ch == '\r') { buff.append('r'); return; }
    if (ch == '\t') { buff.append('t'); return; }
    if (ch == '\f') { buff.append('f'); return; }
    buff.append((char)((ch/64)+'0'));
    buff.append((char)(((ch%64)/8)+'0'));
    buff.append((char)((ch%8)+'0'));
  }
  
  public static String encodeChar(char ch) {
    StringBuffer buff = new StringBuffer(4);
    encodeCharToBuffer(ch, buff);
    return buff.toString();
  }
  
  public static String encodeString(String str) {
    StringBuffer buff = new StringBuffer();
    for (int i = 0; i < str.length(); i++) {
      encodeCharToBuffer(str.charAt(i), buff);
    }
    return buff.toString();
  }
  
  TokenString scanString() throws ScanFailureException {
    char ch = getChar(); // initial quote
    while (lookChar() != '\"') {
      ch = decodeChar();
      scanBuffer[scanBufferSize++] = ch;
      if (scanBufferSize == scanBuffer.length) {
        char[] buf = new char[2*scanBuffer.length];
        for (int i = 0; i < scanBuffer.length; i++) { buf[i] = scanBuffer[i]; }
        scanBuffer = buf;
      }
    }
    ch = getChar();
    String str = String.valueOf(scanBuffer, 0, scanBufferSize);
    scanBufferSize = 0;
    return new TokenString(str);
  }
  
  void scanAlphaNumIde() throws ScanFailureException {
    while (true) {
      int categ = charTable[lookChar()%256];
      if ((categ != LetterCharEnum) && (categ != DigitCharEnum)) {
        break;
      }
      scanBuffer[scanBufferSize++] = getChar();
    }
  }
 
  void scanSpecialIde() throws ScanFailureException {
    while (charTable[lookChar()%256] == SpecialCharEnum) {
      scanBuffer[scanBufferSize++] = getChar();
    }
  }
  
  Token scanBufferIde() throws ScanFailureException {
    String name = String.valueOf(scanBuffer, 0, scanBufferSize);
    scanBufferSize = 0;
    if (keySet.containsKey(name)) { 
      return (TokenKey)keySet.get(name); 
    }
    if (!ideSet.containsKey(name)) { 
      ideSet.put(name, new TokenIde(name));
    }
    return (TokenIde)ideSet.get(name);
  }
  
  int scanNat() throws ScanFailureException {
    int nat = 0;
    while (charTable[lookChar()%256] == DigitCharEnum) {
      nat = (10 * nat) + (getChar() - '0');
      if (nat < 0) { 
        throw new ScanFailureException("Integer constant is too big");
      }
    }
    return nat;
  }
  
  int scanNeg() throws ScanFailureException {
    int neg = 0;
    while (charTable[lookChar()%256] == DigitCharEnum) {
      neg = (10 * neg) - (getChar() - '0');
      if (neg > 0) { 
        throw new ScanFailureException("Integer constant is too big");
      }
    }
    return neg;
  }

  int scanInt() throws ScanFailureException {
    if (haveChar('~')) { return scanNeg(); } else { return scanNat(); }
  }
  
  Token scanNumber() throws ScanFailureException {
    int n;
    boolean negative = haveChar('~');
    if (negative) { n = scanNeg(); } else { n = scanNat(); }
    if (lookChar() == '.') {
      char ch = getChar();
      double r = n;
      double q = 1.0d;
      while (charTable[lookChar()%256] == DigitCharEnum) {
        q = q * 10.0d;
        if (negative) { 
          r -= (getChar() - '0') / q;
        } else {
          r += (getChar() - '0') / q;
        }
      }
      return new TokenReal(r);
    } else {
      return new TokenInt(n);
    }
  }

  void setChar(char c, int category) {
  /** Assign a character class to a character, for customization.
       Must not modify the Reserved character class. 
       Must keep '(' and ')' as delimiters, for scanning comments. */
    charTable[c%256] = category;
  }
    
  void setRange(char s, char t, int category) {
    for (int i = s%256; i <= t%256; i++) {
      charTable[i] = category;
    }
  }

  void init() {
    scanBuffer = new char[256];
    scanBufferSize = 0;
   
    ideSet = new Hashtable(100);
    keySet = new Hashtable(10);
    
    charTable = new int[256];
    for (int i = 0; i < 256; i++) {
      charTable[i] = IllegalCharEnum;
    }
    setRange('\011', '\012', BlankCharEnum);
    setRange('\014', '\015', BlankCharEnum);
    setChar(' ', BlankCharEnum);
    setChar('!', SpecialCharEnum);
    setChar('\"', ReservedCharEnum);
    setRange('#', '&', SpecialCharEnum);
    setChar('\'', ReservedCharEnum);
    setRange('(', ')', DelimCharEnum);
    setRange('*', '/', SpecialCharEnum);
    setRange('0', '9', DigitCharEnum);
    setRange(':', '@', SpecialCharEnum);
    setRange('A', 'Z', LetterCharEnum);
    setRange('[', '_', SpecialCharEnum);
    setRange('`', 'z', LetterCharEnum);
    setRange('{', '}', SpecialCharEnum);
    setChar('~', ReservedCharEnum);
    setChar(EofChar, EofEnum);
    // --- unicode?
  }

}

/* --- who needs these?

  public boolean isDelimiter(char ch) {
  // Whether char is a legal Delimiter token.
    return charTable[ch%256] == DelimCharEnum;
  }
  
  public boolean isIdentifier(String string) {
  // Whether string is a legal Identifier (Name or Keyword) token
    int length = string.length();
    if (length == 0) { return false; }
    int categ0 = charTable[string.charAt(0)%256];
    if (categ0 == LetterCharEnum) {
      for (int i=0; i<length; i++) {
        int categ = charTable[string.charAt(i)%256];
        if ((categ != LetterCharEnum) &&
            (categ != DigitCharEnum)) {
          return false;
        }
      }
    } else if (categ0 == SpecialCharEnum) {
      for (int i=0; i<length; i++) {
        int categ = charTable[string.charAt(i)%256];
        if (categ != SpecialCharEnum) {
          return false;
        }
      }
    }
    return true;
  }
*/

