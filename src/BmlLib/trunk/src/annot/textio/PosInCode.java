package annot.textio;

public class PosInCode {

  private int line_no = -1;

  private int char_pos = -1;

  public PosInCode(final int line, final int pos) {
    line_no = line;
    char_pos = pos;
  }

  public int getLine() {
    return line_no;
  }

  public int getCharPos() {
    return char_pos;
  }

}
