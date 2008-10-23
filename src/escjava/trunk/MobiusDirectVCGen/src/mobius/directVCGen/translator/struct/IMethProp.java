package mobius.directVCGen.translator.struct;

import java.util.List;
import java.util.Set;

import org.apache.bcel.generic.MethodGen;

import escjava.sortedProver.Lifter.QuantVariableRef;

public interface IMethProp {
  public MethodGen getBCELDecl();
  public QuantVariableRef getResult();
  public List<QuantVariableRef> getArgs();
  public List<QuantVariableRef> getLocalVars();
  public Set<QuantVariableRef[]> getAssignableSet();
}
