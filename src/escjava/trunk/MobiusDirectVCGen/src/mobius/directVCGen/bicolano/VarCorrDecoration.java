package mobius.directVCGen.bicolano;

import java.util.HashMap;
import java.util.Map;
import java.util.Map.Entry;

import mobius.directVCGen.formula.Expression;
import mobius.directVCGen.formula.Heap;
import mobius.directVCGen.formula.Num;
import mobius.directVCGen.formula.Ref;

import org.apache.bcel.generic.LocalVariableGen;

import escjava.sortedProver.Lifter.QuantVariableRef;
import escjava.sortedProver.Lifter.Term;

import javafe.ast.ASTDecoration;
import javafe.ast.RoutineDecl;

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
                  final Map<QuantVariableRef, LocalVariableGen> vars) {
    final Map<QuantVariableRef, Term> bcvars = 
      new HashMap<QuantVariableRef, Term>();
    for (Entry<QuantVariableRef, LocalVariableGen> entry: vars.entrySet()) {
      Term value = Expression.sym("do_lvget",
                                  entry.getKey().getSort(), 
                                  new Term[] {Heap.lvvar,
                                              Expression.rvar(entry.getValue().getIndex() + "%N", Num.sortInt)});
      bcvars.put(entry.getKey(), value);
      System.out.println(">>>>    " + entry.getKey() + " " +  value);
    }
    super.set(n, bcvars);
  }

}
