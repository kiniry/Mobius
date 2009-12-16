package escjava.plugin.checkers;

import java.util.List;

import mobius.prover.z3.Z3Editor;

import org.eclipse.jdt.core.IJavaProject;


public class Z3Checker extends Checker {

  public Z3Checker(final IJavaProject proj) {
    super(proj);
  }
  protected boolean addOptions(final List<String> inputs) {
//    inputs.add("-prover");
//    inputs.add("z3");
    inputs.add("-svcg");
    inputs.add("z3");
    System.setProperty("z3", Z3Editor.getZ3Location());
    return super.addOptions(inputs);
  }
}
