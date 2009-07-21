package mobius.cct.verifiers;

import mobius.cct.classfile.ClassName;

/**
 * Exception thrown when a verifier requests verification
 * of the same specification it is assigned to. 
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public class CyclicDependencyException extends VerificationException {
  /**
   * SerialVersionUID.
   */
  private static final long serialVersionUID = 1L;

  /** Class name. */
  private final ClassName fName;

  /** Specification type. */
  private final String fSpec;
  
  /**
   * Constructor.
   * @param name Name of verified class.
   * @param spec Type of verified specification.
   */
  public CyclicDependencyException(final ClassName name, 
                                   final String spec) {
    fName = name;
    fSpec = spec;
  }
  
  /**
   * Constructor.
   * @param msg Message.
   * @param name Name of verified class.
   * @param spec Type of verified specification.
   */
  public CyclicDependencyException(final String msg,
                                   final ClassName name,
                                   final String spec) {
    super(msg);
    fName = name;
    fSpec = spec;
  }
  
  /**
   * Get name of verified class.
   * @return Class name.
   */
  public ClassName getName() {
    return fName;
  }
  
  /**
   * Get type of verified specification.
   * @return Specification type.
   */
  public String getSpec() {
    return fSpec;
  }
}
