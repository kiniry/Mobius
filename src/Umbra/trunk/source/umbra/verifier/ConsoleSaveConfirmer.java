/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) 2006-2008 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.verifier;

import java.util.Scanner;

/**
 * @author Szymon Wrzyszcz (sw237122@students.mimuw.edu.pl)
 * @version a-01
 *
 */
public class ConsoleSaveConfirmer extends SaveConfirmer {

  /**
   * verifier used to check bytecode.
   */
  private BytecodeVerifier my_verifier;

  /**
   * @param a_result_presenter presenter used to display
   * verification status.
   */
  public ConsoleSaveConfirmer(final ResultPresenter a_result_presenter) {
    super(a_result_presenter);
    this.my_verifier = getResultPresenter().getVerifier();
  }

  /**
   * in case there are verification problems asks use
   * if she wants to save anyway.
   * @return true if user wants to save, false otherwise
   */
  @Override
  public boolean confirm() {
    if (!my_verifier.passed()) {
      getResultPresenter().presentAll();
      final Scanner scanner = new Scanner(System.in);
      String token;
      do {
        System.out.println("verification failed. save anyway? y/n");
        token = scanner.next();
      } while (!"y".equals(token) && !"n".equals(token));
      return "y".equals(token);
    } else {
      return true;
    }
  }

}
