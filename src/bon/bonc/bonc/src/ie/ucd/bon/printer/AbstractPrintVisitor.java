package ie.ucd.bon.printer;

import ie.ucd.bon.ast.AbstractVisitorWithAdditions;
import ie.ucd.bon.parser.tracker.ParsingTracker;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.PrintStream;
import java.util.Map;

public class AbstractPrintVisitor extends AbstractVisitorWithAdditions implements PrintAgent {

  protected final TextPrinter tp;
  private final ByteArrayOutputStream baos;
  
  public AbstractPrintVisitor() {
    baos = new ByteArrayOutputStream();
    tp = new TextPrinter(new PrintStream(baos));
  }

  public String getAllOutputAsString(ParsingTracker tracker, Map<String,Object> data) throws IOException {
    return baos.toString();
  }

  public String getVisitorOutputAsString() {
    return baos.toString();
  }

  public void resetVisitorOutput() {
    baos.reset();
  }
  
}
