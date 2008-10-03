package annot.textio;

import java.util.Vector;

import annot.bcclass.BCClass;
import annot.bcclass.MLog;

/**
 * This class represents BMl of an editing bytecode. It's
 * objects can be constructed  with {@link BCClass} and current
 * String representation of bytecode. You can add one or more
 * changes (using {@link #addChange(int, int, String)}
 * method), then execute these changes using
 * {@link #performChanges()} method (this will parse all
 * that changes merged to one, single change, updating
 * it's {@link BCClass}) and see that it's correct, than call
 * {@link #resetChanges()} method. If some changes has been
 * parsed outside this class, call {@link #resetChanges()}
 * to assume that {@link BCClass} is up to date.
 * It can parse only BML placed somewhere in bytecode,
 * not the bytecode itself. Bytecode changes won't be updated
 * into {@link BCClass}.
 *
 * @author Tomasz Batkiewicz (tb209231@students.mimuw.edu.pl)
 * @version a-01
 */
public class CodeFragment {

  /**
   * Disable parsing single attributes; for debugging only.
   */
  private static final boolean GO_DISABLE_PARSER = false;

  /**
   * Flag which indicates if the code after preprocessing by
   * {@link #decorate(String)} should be shown in BMLLib log.
   */
  private static final boolean SHOW_DECORATED_CODE = true;


  /**
   * BCClass related with current bytecode.
   */
  private final BCClass bcc;

  /**
   * Position of first character on which old and current
   * bytecodes differs.
   */
  private int begin;

  /**
   * Current bytecode.
   */
  private String code;

  /**
   * whether current bytecode is correct or not.
   */
  private boolean correct = true;

  /**
   * Position of first unaffected character (in current
   * bytecode).
   */
  private int end;

  /**
   * Last error message.
   */
  private String errMsg = "";

  /**
   * The flag is <code>true</code> in case some changes have been performed
   * using {@link #addChange(int, int, String)} since the last
   * {@link #resetChanges()} call.
   */
  private boolean modified;

  /**
   * Old (original) version of bytecode.
   */
  private String oldCode;

  /**
   * Position of first unaffected character (in original
   * bytecode).
   */
  private int oldEnd;

  /**
   * Common prefix for original and current bytecode.
   */
  private String prefix;

  /**
   * Common suffix for original and current bytecode.
   */
  private String suffix;

  /**
   * Code that should be added in merged changes
   * in bytecode.
   */
  private String toAdd;

  /**
   * Code that should be removed in merged changes
   * in bytecode.
   */
  private String toRemove;

  /**
   * The vector with positions of BML regions. It is <code>null</code> before
   * the parsing is done for the current BML string.
   */
  private Vector < PosInCode > bml_positions;

  /**
   * The array with lines of the current bytecode in the CodeFragment.
   */
  private String[] lines;

  /**
   * A standard contructor.
   *
   * @param abcc - BCClass related with this bytecode,
   * @param acode - a String representation of bytecode.
   */
  public CodeFragment(final BCClass abcc, final String acode) {
    this.bcc = abcc;
    this.code = acode;
    this.oldCode = acode;
  }

  /**
   * @return all keywords that can stand at the beginning
   *     of an annotation.
   */
  private static String[] getAllAttributeNames() {
    final String[] ret = {DisplayStyle._classInvariant,
                          DisplayStyle._requires, DisplayStyle._assert,
                          DisplayStyle._loopspec };
    return ret;
  }

  /**
   * Translates line number of a String to character number
   * (offset).
   *
   * @param code - multi-line String,
   * @param lnr - number of line in <code>code</code>.
   * @return Offset of first character of <code>lnr</code>'s
   *     line in <code>code</code>.
   */
  private static int getLineOffset(final String code, final int lnr) {
    final String[] lines = code.split("\n");
    int pos = 0;
    for (int i = 0; i  <  lnr; i++) {
      pos += lines[i].length() + 1;
    }
    return pos;
  }

  /**
   * Translates character position in a String to number
   * of line containing this character.
   *
   * @param code - multi-line String,
   * @param pos - number of character (offset)
   *     in <code>code</code>.
   * @return Number of line in <code>code</code> containing
   *     character with offset <code>pos</code>.
   */
  private static int getLineOfOffset(final String code, final int pos) {
    return (code.substring(0, pos) + '.').split("\n").length - 1;
  }

  /**
   * @return all keywords that can stand at the beginning
   *     of an method annotation.
   */
  private static String[] getMethodAttributeNames() {
    final String[] ret = {DisplayStyle._requires };
    return ret;
  }

  /**
   * Adds a change (effect of bytecode editing) to this
   * bytecode. A change is replacing one fragment of this
   * bytecode with another String.
   *
   * @param cfrom - position of first modified character,
   * @param length - length of removed String,
   * @param nc - new String added at removed String's
   *     position.
   */
  public void addChange(final int cfrom, final int length, final String nc) {
    final int cto = cfrom + length;
    addChangeErrorChecking(cfrom, cto);
    updateAddedArea(cfrom, nc, cto);
    this.prefix = this.code.substring(0, this.begin);
    this.suffix = this.code.substring(this.end);
    this.oldEnd = this.prefix.length() + this.toRemove.length();
    this.end = this.prefix.length() + this.toAdd.length();
    this.code = this.prefix + this.toAdd + this.suffix;
    this.bml_positions = null;
    this.lines = this.code.split("\n");
  }

  /**
   * @param cfrom
   * @param cto
   * @throws RuntimeException
   */
  private void addChangeErrorChecking(final int cfrom, final int cto)
    throws RuntimeException {
    if (cfrom  >  cto) {
      throw new RuntimeException("wrong parameter values: cfrom  >  cto");
    }
    if (cto  >  this.code.length()) {
      throw new RuntimeException("invalid position: " + cto + " (length = " +
                                 this.code.length() + ")");
    }
    if (cfrom  <  0) {
      throw new RuntimeException("invalid parameter: " + cfrom + "  <  0");
    }
  }

  /**
   * @return current bytecode.
   */
  public String getCode() {
    return this.code;
  }

  /**
   * @return last error message.
   *     Currenlty error messages tells only if code were
   *     parsed by ANTLR, or was so incorrect that was
   *     rejected before passing it to ANTLR.
   */
  public String getErrMsg() {
    return this.errMsg;
  }

  /**
   * @return whether current bytecode is correct.
   *     It can ignore errors that are far enought from
   *     edited fragment (eg. if they were there at the
   *     beginnin, or before last {@link #resetChanges()}
   *     call.
   */
  public boolean isCorrect() {
    return this.correct;
  }


  /**
   * Modifies current bytecode, replacing given fragment
   * with another String and updating {@link BCClass}.
   * Either use this or sequently:<br>
   * - {@link #addChange(int, int, String)} (one or more
   *     times (for merged changes)),<br>
   * - {@link #performChanges()},<br>
   * - {@link #resetChanges()}.
   *
   * @param cfrom - position of first modified character,
   * @param length - length of removed String,
   * @param nc - new String added at removed String's
   *     position.
   * @see #addChange(int, int, String)
   */
  public void modify(final int cfrom, final int length, final String nc) {
    addChange(cfrom, length, nc);
    performChanges();
    MLog.putMsg(MLog.LEVEL_PINFO, toString());
    if (this.correct) {
      resetChanges();
    }
  }

  /**
   * Propagates the current document change to the BMLLib AST.
   * First, checks that current bytecode is correct,
   * then parses it, affecting as few elements of BCClass
   * as it can. Parsing whole class can be uneffective
   * (slow), so it tries to skip unaffected BML annotations,
   * comments and methods. It can parse only BML
   * annotations, not the bytecode itself (bytecode-level
   * BCEL structures will be unaffected).
   */
  public void performChanges() {
    this.correct = true;
    this.errMsg = "";
    //DONE compute positions of affected code
    //FIXME implement that

    MLog.putMsg(MLog.LEVEL_PINFO, "code to be preprocessed:\n" + this.code);
    final String toparse = preProcess(this.code);
    if (SHOW_DECORATED_CODE) {
      MLog.putMsg(MLog.LEVEL_PINFO, "code to be parsed:\n" + toparse);
    }
    if (GO_DISABLE_PARSER) {
      return;
    }
    //DONE create grammar for parsing bytecode

    this.correct = this.bcc.getParser().parseClass(toparse, false);
    //DONE and parse it into bcc.
    if (this.correct) {
      this.bcc.getParser().parseClass(toparse, true);
    }
    bml_positions = this.bcc.getParser().getBMLPositions();
    this.errMsg = this.bcc.getParser().getErrMsg();
  }

  /**
   * Assumes that bytecode has been parsed succesfuly.
   * It should be called after each
   * {@link #performChanges()} call, if bytecode is correct.
   * Calling it for incorrect bytecode may result of ignoring
   * some errors in next parsing attempt.
   * This method has been separated from
   * {@link #performChanges()} method only for test
   * pusposes, to show {@link CodeFragment}'s state
   * just after parsing it.
   */
  public void resetChanges() {
    this.oldCode = this.code;
    this.begin = -1;
    this.end = -1;
    this.oldEnd = -1;
    this.toAdd = null;
    this.toRemove = null;
    this.prefix = null;
    this.suffix = null;
    this.modified = false;
  }
  /**
   * Displays current state of this bytecode fragment.
   */
  public String toString() {
    if (!this.modified) {
      return "code hasn't been modified yet";
    }
    String ret = "******** removed code: *********\n";
    ret += this.toRemove;
    ret += "\n*** current (modified) code: ***\n";
    ret += this.prefix + "##" + this.toAdd + "##" + this.suffix;
    ret += "\n*** CodeFragment status: ***";
    ret += "\ntotal length: " + this.code.length();
    ret += "\nchanged fragment: " + this.begin + " to " + this.end;
    ret += "\ncode is currently " + (this.correct ? "correct" : "incorrect");
    if (this.errMsg.length()  >  0) {
      ret += "\nlast error message: " + this.errMsg;
    }
    return ret;
  }

  /**
   * @param cfrom
   * @param nc
   * @param cto
   */
  private void updateAddedArea(final int cfrom, final String nc,
                               final int cto) {
    if (!this.modified) {
      this.begin = cfrom;
      this.end = cto;
      this.toRemove = this.code.substring(cfrom, cto);
      this.toAdd = nc;
      this.modified = true;
    } else {
      if (cto  <= this.begin) {
        updateNewBeforeOld(cfrom, nc, cto);
      } else if (cfrom  <= this.begin &&
                 cto  >  this.begin && cto  <= this.end) {
        updateNewOverlapsOld(cfrom, nc, cto);
      } else if (cfrom  <= this.begin && cto  >  this.end) {
        updateNewOverOld(cfrom, nc, cto);
      } else if (cfrom  >  this.begin && cto  <= this.end) {
        updateOldOverNew(cfrom, nc, cto);
      } else if (cfrom  >  this.begin &&
                 cfrom  <= this.end && cto  >  this.end) {
        updateOldOverlapsNew(cfrom, nc, cto);
      } else if (cfrom  >  this.end) {
        updateOldBeforeNew(cfrom, nc, cto);
      }
    }
  }

  /**
   * @param cfrom
   * @param nc
   * @param cto
   */
  private void updateNewBeforeOld(final int cfrom, final String nc,
                                  final int cto) {
    //       oooooo
    // nnnn
    MLog.putMsg(MLog.LEVEL_PDEBUG, "branch no 1");
    this.toRemove = this.code.substring(cfrom, this.begin) + this.toRemove;
    this.toAdd = nc + this.code.substring(cto, this.begin) + this.toAdd;
    this.begin = cfrom;
  }

  /**
   * @param cfrom
   * @param nc
   * @param cto
   */
  private void updateNewOverlapsOld(final int cfrom, final String nc,
                                    final int cto) {
    //       oooooo
    //    nnnnnn
    MLog.putMsg(MLog.LEVEL_PDEBUG, "branch no 2");
    this.toRemove = this.code.substring(cfrom, this.begin) + this.toRemove;
    this.toAdd = nc + this.toAdd.substring(cto - this.begin);
    this.begin = cfrom;
  }

  /**
   * @param cfrom
   * @param nc
   * @param cto
   */
  private void updateNewOverOld(final int cfrom, final String nc,
                                final int cto) {
    //       oooooo
    //    nnnnnnnnnnn
    MLog.putMsg(MLog.LEVEL_PDEBUG, "branch no 3");
    this.toRemove = this.code.substring(cfrom, this.begin) + this.toRemove +
      this.code.substring(this.end, cto);
    this.toAdd = nc;
    this.begin = cfrom;
    this.end = cto;
  }

  /**
   * @param cfrom
   * @param nc
   * @param cto
   */
  private void updateOldBeforeNew(final int cfrom, final String nc,
                                  final int cto) {
    //       oooooo
    //               nnnn
    MLog.putMsg(MLog.LEVEL_PDEBUG, "branch no 6");
    this.toRemove = this.toRemove + this.code.substring(this.end, cto);
    this.toAdd = this.toAdd + this.code.substring(this.end, cfrom) + nc;
    this.end = cto;
  }

  /**
   * @param cfrom
   * @param nc
   * @param cto
   */
  private void updateOldOverlapsNew(final int cfrom, final String nc,
                                    final int cto) {
    //       oooooo
    //         nnnnnnn
    MLog.putMsg(MLog.LEVEL_PDEBUG, "branch no 5");
    this.toRemove = this.toRemove + this.code.substring(this.end, cto);
    this.toAdd = this.toAdd.substring(0, cfrom - this.begin) + nc;
    this.end = cto;
  }

  /**
   * @param cfrom
   * @param nc
   * @param cto
   */
  private void updateOldOverNew(final int cfrom, final String nc,
                                final int cto) {
    //       oooooo
    //         nn
    MLog.putMsg(MLog.LEVEL_PDEBUG, "branch no 4");
    this.toAdd = this.toAdd.substring(0, cfrom - this.begin) + nc +
      this.toAdd.substring(cto - this.begin);
  }

  /**
   * This method strips out the one-line comments and BML signs @ at the
   * beginning of a line, but inside a BML comment.
   *
   * @param code the bytecode with BML to preprocess
   * @return the preprocessed code
   */
  public static String preProcess(final String code) {
    final StringBuffer buf = new StringBuffer(code.length());
    int i = 0;
    while (i < code.length()) {
      char ch = code.charAt(i);
      if (ch == '"') {
        final int opos = i;
        i = readString(i, code);
        buf.append(code.substring(opos, i));
        continue;
      } else if (ch == '/') { // DisplayStyle.BML_COMMENT_START starts with '/'
        i++;
        ch = code.charAt(i);
        if (ch == '/') {
          i = readOneLineComment(i, code);
          continue;
        } else if (code.substring(i).startsWith(
                         DisplayStyle.BML_COMMENT_START.substring(1))) {
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

  /**
   * The method reads in a BML comment removing the @ signs at the beginnings
   * of internal lines. It reads string from the <code>code</code> parameter.
   * The first character to be read is pointed by the <code>pos</code>
   * parameter. The resulting string is appended to the <code>buf</code>
   * parameter. The result is the position of the first character in
   * <code>code</code>which has not been swallowed in the course of the
   * processing. This method assumes that <code>pos</code> is inside of a
   * BML comment.
   *
   * @param pos the position of the first character to read
   * @param code the string to read characters from
   * @param buf the string to append characters to
   * @return the position of the first character that was not read by the
   *   procedure
   */
  private static int readBMLComment(final int pos, final String code,
                                    final StringBuffer buf) {
    int i = pos;
    boolean newline = false;
    while (i < code.length()) {
      final char ch = code.charAt(i);
      if (DisplayStyle.BML_AT_SIGN.charAt(i) == ch && newline) {
        newline = false;
        if (code.substring(i).startsWith(DisplayStyle.BML_COMMENT_END)) {
          buf.append(DisplayStyle.BML_COMMENT_END);
          return i + DisplayStyle.BML_COMMENT_END.length();
        } else {
          i++;
          continue;
        }
      } else if (ch == '\n') {
        newline = true;
      } else if (!Character.isWhitespace(ch) && newline) {
        newline = false;
      }
      buf.append(ch);
      i++;
    }
    return 0;
  }

  /**
   * 
   * @param pos
   * @param code
   * @return
   */
  private static int readOneLineComment(final int pos, final String code) {
    int i = pos + 1;
    while (i < code.length()) {
      final char ch = code.charAt(i);
      if (ch == '\n') {
        return i;
      }
      i++;
    }
    return i;
  }

  /**
   * 
   * @param pos
   * @param code
   * @return
   */
  private static int readString(final int pos, final String code) {
    int i = pos + 1;
    while (i < code.length()) {
      char ch = code.charAt(i);
      if (ch == '\\') {
        i++;
        ch = code.charAt(i);
        continue;
      } else if (ch == '"') {
        return ++i;
      }
      i++;
    }
    return i;
  }


}
