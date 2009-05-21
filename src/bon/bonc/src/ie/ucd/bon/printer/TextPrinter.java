package ie.ucd.bon.printer;

import java.io.PrintStream;

public class TextPrinter {

  private final PrintStream ps;
  private int indentation;
  private int spacesPerIndent;
  
  public TextPrinter(PrintStream ps) {
    this.ps = ps;
    indentation = 0;
    spacesPerIndent = 2;
  }
  
  public void printLines(int number) {
    for (int i=0; i < number; i++) {
      printLine(false);
    }
    printIndentation();
  }
  
  public void printLine() {
    printLine(true);
  }
  
  public void printLine(boolean printIndent) {
    ps.println();
    if (printIndent) {
      printIndentation();
    }
  }
  
  public void printIndentation() {
    for (int i=0; i < indentation*spacesPerIndent; i++) {
      ps.println(' ');
    }
  }
  
  public void print(String s) {
    ps.print(s);
  }
  
}
