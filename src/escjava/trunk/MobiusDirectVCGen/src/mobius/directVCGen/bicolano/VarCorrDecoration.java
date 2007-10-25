package mobius.directVCGen.bicolano;

import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import javafe.ast.ASTDecoration;
import javafe.ast.RoutineDecl;

import org.apache.bcel.generic.LocalVariableGen;

import escjava.sortedProver.Lifter.QuantVariableRef;

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
  public List<QuantVariableRef> get(final RoutineDecl n) {
    final List<QuantVariableRef> v = 
      (List<QuantVariableRef>) super.get(n);
    return v;
  }
  
  
  public void set(final RoutineDecl n,
                  final Map<QuantVariableRef, LocalVariableGen> vars,
                  final List<QuantVariableRef> old) {
    final List<QuantVariableRef> bcvars = 
      new ArrayList<QuantVariableRef>();
    bcvars.addAll(old);
    
    for (Entry<QuantVariableRef, LocalVariableGen> entry: vars.entrySet()) {
      bcvars.add(entry.getKey());
      
    }
    
    final LinkedList<QuantVariableRef> rev = new LinkedList<QuantVariableRef>();
    for (QuantVariableRef q: bcvars) {
      rev.addFirst(q);
    }
    super.set(n, rev);
  }

}
