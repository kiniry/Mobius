package mobius.directVCGen.formula;

import java.util.List;

import escjava.sortedProver.Lifter.QuantVariableRef;

public interface ILocalVars {
  public List<QuantVariableRef> getLocalVars(); 
  public List<QuantVariableRef> getArgs();
}
