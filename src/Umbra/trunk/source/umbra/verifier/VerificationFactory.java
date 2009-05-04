/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) 2006-2008 University of Warsaw"
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
public abstract class VerificationFactory {

  /**
   * @return presenter for results of verification
   * @param  a_verifier verifier
   */
  public abstract ResultPresenter getResultPresenter(
      final BytecodeVerifier a_verifier);

  /**
   * @return object responsible for asking user if she wants
   * to save despite of verification trouble.
   * @param  a_result_presenter presenter
   */
  public abstract SaveConfirmer getSaveConfirmer(
      final ResultPresenter a_result_presenter);

}
