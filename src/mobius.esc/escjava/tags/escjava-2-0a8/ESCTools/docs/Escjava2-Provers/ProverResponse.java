class ProverResponse
{
  /**
   * A singleton response code to indicate everything is fine.
   */
  public /*@ non_null @*/ static ProverResponse OK =
    new ProverResponse();

  /**
   * A singleton response code to indicate that something is seriously
   * wrong with the corresponding call and/or the prover and a failure
   * has taken place.  A response code of FAIL typically indicates a
   * non-correctable situation.  The {@link #info} field should be
   * consulted for additional information, and no further calls, but
   * for {@link ProverInterface#stop_prover()} should be made.
   */
  public /*@ non_null @*/ static ProverResponse FAIL =
    new ProverResponse();

  /**
   * A singleton response code to indicate a positive response to the
   * last command.
   */
  public /*@ non_null @*/ static ProverResponse YES =
    new ProverResponse();

  /**
   * A singleton response code to indicate a negative response to the
   * last command.
   */
  public /*@ non_null @*/ static ProverResponse NO =
    new ProverResponse();

  /**
   * A singleton response code to indicate a counter-example is
   * available.  The counter-example is contained in the {@link
   * #formula} field of this response object.
   */
  public /*@ non_null @*/ static ProverResponse COUNTER_EXAMPLE =
    new ProverResponse();

  /**
   * A singleton response code to indicate a syntax error in the
   * corresponding prover call.  The {@link #info} field should be
   * consulted for additional information.
   */
  public /*@ non_null @*/ static ProverResponse SYNTAX_ERROR =
    new ProverResponse();

  /**
   * A singleton response code to indicate that some progress
   * information is available from the prover.  The {@link #info}
   * field should be consulted for additional information.
   */
  public /*@ non_null @*/ static ProverResponse PROGRESS_INFORMATION =
    new ProverResponse();

  /**
   * A singleton response code to indicate that the prover has timed
   * out on the corresponding prover call.  The {@link #info} and/or
   * {@link #formula} fields should be consulted for additional
   * information.
   */
  public /*@ non_null @*/ static ProverResponse TIMEOUT =
    new ProverResponse();

  /**
   * A singleton response code to indicate an inconsistency warning
   * from the prover for one or more of the previous {@link
   * ProverInterface#declare_axiom(Formula)} and {@link
   * ProverInterface#make_assumption(Formula)} calls.  The {@link
   * #info} and/or {@link #formula} fields should be consulted for
   * additional information.
   */
  public /*@ non_null @*/ static ProverResponse INCONSISTENCY_WARNING =
    new ProverResponse();

  /**
   * A formula.  Typically, this field is used to represent a
   * counter-example in response to a call to {@link
   * ProverInterface#is_valid(Formula)}.
   */
  public Formula formula;

  /**
   * A set of properties.  Typically, this field is used to represent
   * property/value pairs specific to reporting prover progress,
   * state, resource utilization, etc.
   */
  public Properties info;

  /**
   * A private constructor that is only to be used during static
   * initialization.
   */
  private ProverResponse() {
    ; // skip
  }
}
