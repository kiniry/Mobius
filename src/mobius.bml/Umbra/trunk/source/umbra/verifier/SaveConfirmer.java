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
public abstract class SaveConfirmer {

  /**
   *
   */
  private ResultPresenter my_result_presenter;

  /**
   * @param a_result_presenter presenter
   */
  public SaveConfirmer(final ResultPresenter a_result_presenter) {
    this.my_result_presenter = a_result_presenter;
  }

  /**
   * @return result presenter
   */
  public ResultPresenter getResultPresenter() {
    return my_result_presenter;
  }

  /**
   * in case there are verification problems asks user
   * if she wants to save anyway.
   *
   * @return true if user wants to save, false otherwise
   */
  public abstract boolean confirm();

}
