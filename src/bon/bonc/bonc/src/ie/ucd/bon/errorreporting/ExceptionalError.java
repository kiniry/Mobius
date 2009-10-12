package ie.ucd.bon.errorreporting;

import ie.ucd.bon.source.SourceLocation;
import ie.ucd.bon.util.StringUtil;

public class ExceptionalError extends BONError {

  private final String message;

  public ExceptionalError(final Exception e) {
    super(SourceLocation.NO_LOCATION);
    this.message = "BONc has encountered an exceptional error. \n\n" + StringUtil.exceptionStackTraceAsString(e);
  }

  @Override
  public String getMessage() {
    return message;
  }

}
