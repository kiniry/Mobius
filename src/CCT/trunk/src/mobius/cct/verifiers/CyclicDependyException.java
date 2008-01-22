package mobius.cct.verifiers;

/**
 * Exception thrown when a verifier requests verification
 * of the same specification it is assigned to. 
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public class CyclicDependyException extends Exception {
  /**
   * SerialVersionUID.
   */
  private static final long serialVersionUID = 1L;

  /** Class name. */
  private final String fName;

  /** Specification type. */
  private final String fSpec;
  
  /**
   * Constructor.
   * @param name Name of verified class.
   * @param spec Type of verified specification.
   */
  public CyclicDependyException(final String name, 
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
  public CyclicDependyException(final String msg,
                                final String name,
                                final String spec) {
    super(msg);
    fName = name;
    fSpec = spec;
  }
  
  /**
   * Get name of verified class.
   * @return Class name.
   */
  public String getName() {
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
