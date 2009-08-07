package freeboogie;

import java.util.ArrayList;
import java.util.List;

import com.google.common.collect.Lists;

import freeboogie.tc.FbError;

public class ErrorsFoundException extends Exception {
  private static final long serialVersionUID = 8234628L;

  private List<FbError> errors;

  public ErrorsFoundException() {
    this(new ArrayList<FbError>());
  }

  public ErrorsFoundException(List<FbError> errors) {
    this.errors = Lists.newArrayList(errors);
  }

  public void report() {
    FbError.reportAll(errors);
  }
}
