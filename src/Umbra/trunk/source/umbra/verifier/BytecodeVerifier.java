/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) 2006-2008 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.verifier;



import org.apache.bcel.Repository;
import org.apache.bcel.classfile.JavaClass;
import org.apache.bcel.util.ClassPath;
import org.apache.bcel.util.SyntheticRepository;
import org.apache.bcel.verifier.VerificationResult;
import org.apache.bcel.verifier.Verifier;
import org.apache.bcel.verifier.VerifierFactory;

/**
 * @author Szymon Wrzyszcz (sw237122@students.mimuw.edu.pl)
 * @author Tomasz Olejniczak (to236111@students.mimuw.edu.pl)
 * @version a-01
 *
 */
public class BytecodeVerifier {

  /**
   * verifier used to check bytecode.
   */
  private Verifier my_verifier;

  /**
   * class checked by the verifier.
   */
  private JavaClass my_jc;

  /**
   * @param a_jc class to verify
   * @param a_build_path a build path of the project the verified
   * class belongs to
   */
  public BytecodeVerifier(final JavaClass a_jc, final String a_build_path) {
    this.my_jc = a_jc;
    final ClassPath cp = ClassPath.SYSTEM_CLASS_PATH;
    final ClassPath ncp = new ClassPath(cp.toString() + ":" + a_build_path);
    final SyntheticRepository sr = SyntheticRepository.getInstance(ncp);
    Repository.setRepository(sr);
    /*
     * TODO (Umbra) it is possible that the old version of class is loaded from
     * project build path and adding the fresh (present in editor) version of
     * class to the repository does not work.
     */
    Repository.addClass(a_jc);
    final String class_name = a_jc.getClassName();
    my_verifier = VerifierFactory.getVerifier(class_name);
    my_verifier.flush();
  }

  /**
   * @return java class
   */
  public JavaClass getJavaClass() {
    return my_jc;
  }

  /**
   * @return result of pass 1 verification
   */
  public VerificationResult doPass1() {
    return my_verifier.doPass1();
  }

  /**
   * @return result of pass 2 verification
   */
  public VerificationResult doPass2() {
    return my_verifier.doPass2();
  }

  /**
   * @param  a_method_no index of method to verify
   * @return result of pass 3a verification
   */
  public VerificationResult doPass3a(final int a_method_no) {
    return my_verifier.doPass3a(a_method_no);
  }

  /**
   * @param  a_method_no index of method to verify
   * @return result of pass 3b verification
   */
  public VerificationResult doPass3b(final int a_method_no) {
    return my_verifier.doPass3b(a_method_no);
  }

  /**
   * @return true if verification passed false otherwise
   */
  public boolean passed() {
    boolean ok = true;
    if (doPass1().getStatus() != VerificationResult.VERIFIED_OK) ok = false;
    if (ok && doPass2().getStatus() != VerificationResult.VERIFIED_OK)
       ok = false;

    for (int i = 0; ok && i < my_jc.getMethods().length; i++) {
      if (doPass3a(i).getStatus() != VerificationResult.VERIFIED_OK) ok = false;
      if (doPass3b(i).getStatus() != VerificationResult.VERIFIED_OK) ok = false;
    }
    return ok;
  }

}
