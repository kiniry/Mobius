package mobius.directVCGen.formula.jmlTranslator.struct;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import javafe.ast.ConstructorDecl;
import javafe.ast.FieldAccess;
import javafe.ast.RoutineDecl;
import mobius.directVCGen.formula.Lookup;
import escjava.sortedProver.Lifter.QuantVariable;
import escjava.sortedProver.Lifter.QuantVariableRef;

/**
 * Properties that are passed as argument of the visitor. 
 * @author Hernann Lehner and J. Charles (julien.charles@inria.fr)
 */
public final class MethodProperties extends ContextProperties {

  /** */
  private static final long serialVersionUID = 1L;
  
  
  /** valid properties string. */
  private static final List<String> validStr = 
    new ArrayList<String>();

  
  
  /** key to represent a result in the properties set. */  
  public QuantVariableRef fResult;
  
  
  /** tells whether or not we are inspecting a constructor. */
  public final boolean fIsConstructor;
  
  /** the routine is a JML \helper routine. See JML reference */
  public  boolean fIsHelper;
  
  /** the set of variables that can be assigned in the current method. */
  public  final Set<QuantVariableRef[]> fAssignableSet = new HashSet<QuantVariableRef[]>(); 
  
  
  /** if the flag modifies nothing is set for the method. */
  public boolean fNothing;

  /** the local variables. */
  public LinkedList<List<QuantVariableRef>> fLocalVars = 
      new LinkedList<List<QuantVariableRef>> ();
  
  /** the arguments of the method. */
  private LinkedList<QuantVariableRef> fArgs;

  /** the current method which is inspected. */
  private final RoutineDecl fMethod;
  
  /** the counter to get the assert number, for the naming. */
  private int fAssert;
  
  /**
   * initialize the properties with default values.
   * @param met the method which is inspected
   */
  public MethodProperties(final RoutineDecl met) {
    initProperties();
    
    validStr.addAll(super.getValidStr());
    fMethod = met;
    fArgs = new LinkedList<QuantVariableRef>(); 
    fArgs.addAll(Lookup.mkArguments(met));

    fIsConstructor = fMethod instanceof ConstructorDecl;
  }
  

  
  private void initProperties() {
    validStr.add("freshSet");
    validStr.add("subsetCheckingSetConstraints");
    validStr.add("subSetCheckingSetInitially");
    validStr.add("routinebegin");
    validStr.add("quantifier");
    validStr.add("quantVars");
    
    put("freshSet", new HashSet<QuantVariableRef>());
    put("subsetCheckingSetConstraints", new HashSet<FieldAccess>());
    put("subSetCheckingSetInitially", new HashSet<FieldAccess>());
    put("routinebegin", Boolean.TRUE);  
    put("quantifier", Boolean.FALSE);
    put("quantVars", new HashSet<QuantVariable>());
    
  }

  

  public List<String> getValidStr() {
    return validStr;
  }
  
  public RoutineDecl getDecl() {
    return fMethod;
  }
  
  public List<QuantVariableRef> getLocalVars() {
    final List<QuantVariableRef> res = new LinkedList<QuantVariableRef>();
    for (List<QuantVariableRef> list: fLocalVars) {
      res.addAll(list);
    }
    return res;
  }



  public int getAssertNumber() {
    return fAssert++;
  }



  public List<QuantVariableRef> getArgs() {
    return fArgs;
  }
}
