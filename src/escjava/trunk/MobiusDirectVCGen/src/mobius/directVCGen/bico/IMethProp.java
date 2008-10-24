package mobius.directVCGen.bico;

import java.util.List;

import org.apache.bcel.generic.MethodGen;

import escjava.sortedProver.Lifter.QuantVariableRef;

public interface IMethProp {
  public MethodGen getBCELDecl();
  public QuantVariableRef getResult();
  public List<QuantVariableRef> getArgs();
  public List<QuantVariableRef> getLocalVars();
  
}
