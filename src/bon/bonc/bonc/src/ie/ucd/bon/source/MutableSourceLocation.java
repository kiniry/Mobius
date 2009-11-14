package ie.ucd.bon.source;


public final class MutableSourceLocation extends SourceLocation {

  public MutableSourceLocation(SourceLocation loc) {
    super(loc);
  }

  public final MutableSourceLocation setLineNumber(int lineNumber) {
    this.lineNumber = lineNumber;
    return this;
  }
  
  public final MutableSourceLocation setCharPositionInLine(int charPositionInLine) {
    this.charPositionInLine = charPositionInLine;
    return this;
  }
  
  public final MutableSourceLocation setAbsoluteCharPositionStart(int absoluteCharPositionStart) {
    this.absoluteCharPositionStart = absoluteCharPositionStart;
    return this;
  }
  
  public final MutableSourceLocation setAbsoluteCharPositionEnd(int absoluteCharPositionEnd) {
    this.absoluteCharPositionEnd = absoluteCharPositionEnd;
    return this;
  }
  
}
