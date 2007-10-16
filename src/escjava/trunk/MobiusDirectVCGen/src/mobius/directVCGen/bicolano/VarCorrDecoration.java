package mobius.directVCGen.bicolano;

import java.util.HashMap;
import java.util.Map;
import java.util.Map.Entry;

import javafe.ast.ASTDecoration;
import javafe.ast.RoutineDecl;
import mobius.directVCGen.formula.Expression;
import mobius.directVCGen.formula.Heap;
import mobius.directVCGen.formula.Num;

import org.apache.bcel.generic.LocalVariableGen;

import escjava.sortedProver.Lifter.QuantVariableRef;
import escjava.sortedProver.Lifter.Term;

/**
 * Give the correspondence between the variables of a method
 * and their bytecode equivalence.
 * @author J. Charles (julien.charles@inria.fr)
 */
public class VarCorrDecoration extends ASTDecoration {
  
  /** the current instance initialized of the annotation decorations. */
  public static final VarCorrDecoration inst = new VarCorrDecoration();

  public VarCorrDecoration() {
    super("variables-bytecode-map");
  }

  @SuppressWarnings("unchecked")
  public Map<QuantVariableRef, Term> get(final RoutineDecl n) {
    final Map<QuantVariableRef, Term> v = 
      (Map<QuantVariableRef, Term>) super.get(n);
    return v;
  }
  
  
  public void set(final RoutineDecl n,
                  final Map<QuantVariableRef, LocalVariableGen> vars,
                  final Map<QuantVariableRef, Term> old) {
    final Map<QuantVariableRef, Term> bcvars = 
      new HashMap<QuantVariableRef, Term>();
    bcvars.putAll(old);
    
    for (Entry<QuantVariableRef, LocalVariableGen> entry: vars.entrySet()) {
      final Term value = 
        Expression.doLvGet(entry.getKey().getSort(),
                           Heap.lvvar, entry.getValue().getIndex());
      bcvars.put(entry.getKey(), value);
      //System.out.println(">>>>    " + entry.getKey() + " " +  value);
    }
    super.set(n, bcvars);
  }

}
