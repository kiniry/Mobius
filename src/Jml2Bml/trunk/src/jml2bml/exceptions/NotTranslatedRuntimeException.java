package jml2bml.exceptions;

import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.util.JCDiagnostic.DiagnosticPosition;

public class NotTranslatedRuntimeException extends RuntimeException {
  private static final long serialVersionUID = 821440172563056853L;
  public final DiagnosticPosition position;
  public NotTranslatedRuntimeException(final String msg) {
    super(msg);
    position = null;
  }
  public NotTranslatedRuntimeException(final String msg, final JCTree node) {
    super(msg);
    position = node.pos();
    
  }
}
