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
 * @author Szymon Wrzyszcz (sw237122@students.mimuw.edu.pl)
 * @version a-01
 *
 */
public class SWTResultPresenter extends ResultPresenter {

  /**
   *
   */
  private final int my_width = 40;

  /**
   *
   */
  private Shell my_shell;

  /**
   *
   */
  private MessageBox my_msgBox;

  /**
   * @param a_verifier verifier
   * @param a_shell    shell
   */
  public SWTResultPresenter(final BytecodeVerifier a_verifier,
                            final Shell a_shell) {
    super(a_verifier);
    this.my_shell = a_shell;
    my_msgBox = new MessageBox(my_shell, SWT.ICON_QUESTION | SWT.YES | SWT.NO);
  }

  /**
   *
   */
  @Override
  public void presentAll() {
    my_msgBox.setMessage("");
    presentPass1();
    presentPass2();
    presentPass3a();
    presentPass3b();
    my_msgBox.open();
  }

  /**
   *
   */
  @Override
  public void presentPass1() {
    final VerificationResult result = getVerifier().doPass1();

    String s = my_msgBox.getMessage();
    s += "pass1" + "\n";
    s += line(my_width, '-') + "\n";
    s += getInfo(result) + "\n";
    my_msgBox.setMessage(s);
  }

  /**
   *
   */
  @Override
  public void presentPass2() {
    final VerificationResult result = getVerifier().doPass2();
    String s = my_msgBox.getMessage();
    s += "pass2" + "\n";
    s += line(my_width, '-') + "\n";
    s += getInfo(result) + "\n";
    my_msgBox.setMessage(s);
  }

  /**
   *
   */
  @Override
  public void presentPass3a() {
    String s = my_msgBox.getMessage();
    s += "pass3a" + "\n";
    s += line(my_width, '-') + "\n";
    final JavaClass my_jc = getVerifier().getJavaClass();
    final Method[] methods = my_jc.getMethods();
    for (int i = 0; i < methods.length; i++) {
      final VerificationResult result = getVerifier().doPass3a(i);
      s += presentMethod(methods[i]) + " " + getInfo(result) + "\n";
    }
    my_msgBox.setMessage(s);
  }

  /**
   *
   */
  @Override
  public void presentPass3b() {
    String s = my_msgBox.getMessage();
    s += "pass3b" + "\n";
    s += line(my_width, '-') + "\n";
    final JavaClass jc = getVerifier().getJavaClass();
    final Method[] methods = jc.getMethods();
    for (int i = 0; i < methods.length; i++) {
      final VerificationResult result = getVerifier().doPass3b(i);
      s += presentMethod(methods[i]) + " " + getInfo(result) + "\n";
    }
    my_msgBox.setMessage(s);
  }

}
