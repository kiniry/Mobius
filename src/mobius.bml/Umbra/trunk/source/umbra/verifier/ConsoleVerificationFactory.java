/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) 2006-2009 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.verifier;

/**
 * @author Szymon Wrzyszcz (sw237122@students.mimuw.edu.pl)
 * @version a-01
 *
 */
public class ConsoleVerificationFactory extends VerificationFactory {

  /**
   * @param a_verifier verifier used to check bytecode.
   * @return a new console presenter
   */
  @Override
  public ResultPresenter getResultPresenter(final BytecodeVerifier a_verifier) {
    return new ConsoleResultPresenter(a_verifier);
  }

  /**
   * @param a_result_presenter presenter used to show
   * verification results.
   * @return a new console confirmer
   */
  @Override
  public SaveConfirmer getSaveConfirmer(
           final ResultPresenter a_result_presenter) {
    return new ConsoleSaveConfirmer(a_result_presenter);
  }
}
