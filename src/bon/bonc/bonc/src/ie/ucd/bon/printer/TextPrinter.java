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
  
  public void increaseIndentation() {
    indentation++;
  }
  
  public void decreaseIndentation() {
    indentation--;
  }

  public void startLine() {
    printIndentation();
  }
  
  public void printLines(int number) {
    for (int i=0; i < number; i++) {
      printLine();
    }
  }
  
  public void printLine() {
    ps.println();
  }
  
  public void printLine(String line) {
    ps.println(line);
  }
  
  public void printIndentation() {
    printSpaces(indentation*spacesPerIndent);
  }
  
  public void print(String s) {
    ps.print(s);
  }
  
  public void print(Object o) {
    ps.print(o.toString());
  }
  
  public void print(char c) {
    ps.print(c);
  }
  
  public void printSpace() {
    ps.print(' ');
  }
  
  public void printSpaces(int num) {
    for (int i=0; i < num; i++) {
      printSpace();
    }
  }
  
}
