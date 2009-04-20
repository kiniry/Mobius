/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) 2006-2008 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.verifier;

import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.MessageBox;
import org.eclipse.swt.widgets.Shell;

/**
 * @author Szymon Wrzyszcz
 * @version a-01
 *
 */
public class SWTResultPresenter extends ResultPresenter {

  private Shell a_shell;
  
  /**
   * @param verifier
   */
  public SWTResultPresenter(BytecodeVerifier verifier, Shell a_shell) {
    super(verifier);
    this.a_shell = a_shell;
  }
  
  /* (non-Javadoc)
   * @see umbra.verifier.ResultPresenter#presentAll()
   */
  @Override
  public void presentAll() {
    // TODO Auto-generated method stub
    MessageBox msgBox = new MessageBox(a_shell, SWT.ICON_QUESTION | SWT.YES | SWT.NO);
    
  }

  /* (non-Javadoc)
   * @see umbra.verifier.ResultPresenter#presentPass1()
   */
  @Override
  public void presentPass1() {
    // TODO Auto-generated method stub
    
  }

  /* (non-Javadoc)
   * @see umbra.verifier.ResultPresenter#presentPass2()
   */
  @Override
  public void presentPass2() {
    // TODO Auto-generated method stub
    
  }

  /* (non-Javadoc)
   * @see umbra.verifier.ResultPresenter#presentPass3a()
   */
  @Override
  public void presentPass3a() {
    // TODO Auto-generated method stub
    
  }

  /* (non-Javadoc)
   * @see umbra.verifier.ResultPresenter#presentPass3b()
   */
  @Override
  public void presentPass3b() {
    // TODO Auto-generated method stub
    
  }

}
