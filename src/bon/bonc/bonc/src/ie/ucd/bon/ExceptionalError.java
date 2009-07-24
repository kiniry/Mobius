package ie.ucd.bon;

import ie.ucd.bon.errorreporting.BONError;
import ie.ucd.bon.source.SourceLocation;
import ie.ucd.bon.util.StringUtil;

public class ExceptionalError extends BONError {

  private final String message;
  
  public ExceptionalError(Exception e) {
    super(SourceLocation.NO_LOCATION);
    this.message = "BONc has encountered an exceptional error. \n\n" + StringUtil.exceptionStackTraceAsString(e);  
  }
  
  @Override
  public String getMessage() {
    return message;
  }

}
