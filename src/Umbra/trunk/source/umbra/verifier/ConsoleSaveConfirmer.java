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

  private BytecodeVerifier verifier;
  
  /**
   * @param resultPresenter
   */
  public ConsoleSaveConfirmer(ResultPresenter resultPresenter) {
    super(resultPresenter);
    this.verifier = resultPresenter.verifier;
  }

  /**
   * 
   */
  @Override
  public boolean confirm() {
    if (!verifier.passed()) {
      resultPresenter.presentAll();
      Scanner scanner = new Scanner(System.in);
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
