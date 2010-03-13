package ie.ucd.bon.typechecker.errors;

import ie.ucd.bon.source.SourceLocation;

public class InvalidNumberOfGenericsProvided extends TypeCheckingError {

  private static final String message = "Invalid number of generic parameters for type %s (%s provided, but expected %s)";
  
  private final String typeName;
  private final int expected;
  private final int provided;
  
  public InvalidNumberOfGenericsProvided(SourceLocation loc, String typeName, int expected, int provided) {
    super(loc);
    this.typeName = typeName;
    this.expected = expected;
    this.provided = provided;
  }
  
  @Override
  public String getMessage() {
    return String.format(message, typeName, provided, expected);
  }

}
