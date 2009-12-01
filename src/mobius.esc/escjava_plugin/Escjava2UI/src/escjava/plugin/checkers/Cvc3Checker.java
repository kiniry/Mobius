package escjava.plugin.checkers;

import java.util.List;

import org.eclipse.jdt.core.IJavaProject;


public class Cvc3Checker extends Checker {

  public Cvc3Checker(final IJavaProject proj) {
    super(proj);
  }
  protected boolean addOptions(final List<String> inputs) {
    //inputs.add("-prover");
    //inputs.add("cvc3");
    inputs.add("-svcg");
    inputs.add("cvc3");
    return super.addOptions(inputs);
  }
}
