/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) 2006-2009 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.verifier;

import org.eclipse.swt.widgets.Shell;

/**
 * @author Szymon Wrzyszcz (sw237122@students.mimuw.edu.pl)
 * @version a-01
 *
 */
public abstract class SaveConfirmer {

  protected ResultPresenter resultPresenter;
  
  /**
   * @param resultPresenter
   */
  public SaveConfirmer(ResultPresenter resultPresenter) {
    this.resultPresenter = resultPresenter;
  }

  /**
   * in case there are verification problems asks user if she wants to save anyway
   * 
   * @param a_shell bytecode editor shell, used by graphical confirmers
   * @return true if user wants to save, false otherwise
   */
  public abstract boolean confirm();
  
}
