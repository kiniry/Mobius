interface ProverInterface
{
  /**
   * Start up the prover.  After the prover is started correctly it
   * should be ready to receive any of the commands embodied by all
   * the other methods of this API.
   *
   * @return a response code.  A response code of {@link
   * ProverResponse#OK} indicates that the prover started successfully
   * and is ready to receive commands.  A response code of {@link
   * ProverResponse#FAIL} indicates that the prover did not start
   * successfully and is not ready to receive commands.  In the latter
   * case, {@link ProverResponse.FAIL.info} can contain additional
   * arbitrary information about the failure.
   */
  /*@ public normal_behavior
    @   ensures \result == ProverResponse.OK || \result == ProverResponse.FAIL;
    @*/
  public /*@ non_null @*/ ProverResponse start_prover();

  /**
   * Send arbitrary information to the prover.  Typically this
   * information is not mandatory and is only suggestions or
   * informative information from the front-end.  This data is highly
   * prover-dependent.
   *
   * @param properties the set of property/value pairs to send to the
   * prover.
   * @return a response code.
   */
  /*@ public normal_behavior
    @   ensures \result == ProverResponse.OK || 
    @           \result == ProverResponse.FAIL ||
    @           \result == ProverResponse.SYNTAX_ERROR ||
    @           \result == ProverResponse.PROGRESS_INFORMATION;
    @*/
  public ProverResponse set_prover_resource_flags(Properties properties);

  /**
   *
   * @param signature
   * @return a response code.
   */
  public ProverResponse signature(Signature signature);

  /**
   *
   * @param formula
   * @return a response code.
   */
  public ProverResponse declare_axiom(Formula formula);

  /**
   *
   * @param formula
   * @return a response code.
   */
  public ProverResponse make_assumption(Formula formula);

  /**
   *
   *
   * @param formula
   * @param properties
   * @return a response code.
   *
   * @design kiniry 30 June 2004 - Possible alternative names for this
   * method include check(), is_entailed(), is_an_entailed_model_of().
   * I prefer is_valid().
   */
  public ProverResponse is_valid(Formula formula, Properties properties);

  /**
   *
   * @param count
   * @return a response code.
   */
  public ProverResponse retract_assumption(int count);

  /**
   *
   * @return a response code.
   */
  public ProverResponse stop_prover();
}
