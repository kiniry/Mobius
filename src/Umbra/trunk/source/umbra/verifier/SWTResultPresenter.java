/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) 2006-2008 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.verifier;

import org.apache.bcel.classfile.JavaClass;
import org.apache.bcel.classfile.Method;
import org.apache.bcel.verifier.VerificationResult;
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
  private MessageBox msgBox; 
  
  /**
   * @param verifier
   */
  public SWTResultPresenter(BytecodeVerifier verifier, Shell a_shell) {
    super(verifier);
    this.a_shell = a_shell;
    msgBox = new MessageBox(a_shell, SWT.ICON_QUESTION | SWT.YES | SWT.NO);
  }
  
  /* (non-Javadoc)
   * @see umbra.verifier.ResultPresenter#presentAll()
   */
  @Override
  public void presentAll() {
    // TODO Auto-generated method stub
     
    msgBox.setMessage("");
    presentPass1();
    presentPass2();
    presentPass3a();
    presentPass3b();
    msgBox.open();
  }

  /* (non-Javadoc)
   * @see umbra.verifier.ResultPresenter#presentPass1()
   */
  @Override
  public void presentPass1() {
    // TODO Auto-generated method stub
    VerificationResult result = verifier.doPass1();
    
    String s = msgBox.getMessage();
    s += "pass1" + "\n";
    s += line(40, '-') + "\n";
    s += getInfo(result) + "\n";
    msgBox.setMessage(s);
  }

  /* (non-Javadoc)
   * @see umbra.verifier.ResultPresenter#presentPass2()
   */
  @Override
  public void presentPass2() {
    // TODO Auto-generated method stub
    VerificationResult result = verifier.doPass2();
    
    String s = msgBox.getMessage();
    s += "pass2" + "\n";
    s += line(40, '-') + "\n";
    s += getInfo(result) + "\n";
    msgBox.setMessage(s);
  }

  /* (non-Javadoc)
   * @see umbra.verifier.ResultPresenter#presentPass3a()
   */
  @Override
  public void presentPass3a() {
    String s = msgBox.getMessage();
    s += "pass3a" + "\n";
    s += line(40, '-') + "\n";
    JavaClass jc = verifier.getJavaClass();
    Method[] methods = jc.getMethods();
    for (int i=0; i < methods.length; i++) {
      VerificationResult result = verifier.doPass3a(i);
      s += presentMethod(methods[i]) + " " + getInfo(result) + "\n";
    }
    msgBox.setMessage(s);
  }

  /* (non-Javadoc)
   * @see umbra.verifier.ResultPresenter#presentPass3b()
   */
  @Override
  public void presentPass3b() {
    String s = msgBox.getMessage();
    s += "pass3b" + "\n";
    s += line(40, '-') + "\n";
    JavaClass jc = verifier.getJavaClass();
    Method[] methods = jc.getMethods();
    for (int i=0; i < methods.length; i++) {
      VerificationResult result = verifier.doPass3b(i);
      s += presentMethod(methods[i]) + " " + getInfo(result) + "\n";
    }
    msgBox.setMessage(s);
  }

}
