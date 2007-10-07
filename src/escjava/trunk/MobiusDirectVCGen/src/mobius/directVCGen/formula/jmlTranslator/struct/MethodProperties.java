package mobius.directVCGen.formula.jmlTranslator.struct;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;

import javafe.ast.FieldAccess;
import javafe.ast.RoutineDecl;
import escjava.sortedProver.Lifter.QuantVariable;
import escjava.sortedProver.Lifter.QuantVariableRef;

/** Properties that are passed as argument of the visitor. */
public final class MethodProperties extends ContextProperties {

  /** */
  private static final long serialVersionUID = 1L;
  
  
  /** valid properties string. */
  private static final List<String> validStr = 
    new ArrayList<String>();
  
  static
  {
    validStr.add("freshSet");
    validStr.add("subsetCheckingSetConstraints");
    validStr.add("subSetCheckingSetInitially");
    validStr.add("assignableSet");
    validStr.add("nothing");
    validStr.add("routinebegin");
    validStr.add("quantifier");
    validStr.add("quantVars");
    validStr.add("isHelper");
    validStr.add("firstExPost"); 
    validStr.add("isConstructor");
  }
  
  
  /** key to represent a result in the properties set. */  
  public QuantVariableRef fResult;
  
  /** the current method which is inspected. */
  public  RoutineDecl fMethod;
  
  /** telles whether or not we are inspecting a constructor. */
  public  boolean fIsConstructor;
  /**
   * initialize the properties with default values.
   */
  public MethodProperties() {
    initProperties(); 
    validStr.addAll(super.getValidStr());
    
  }
  
  
  private void initProperties() {
   
    


    put("freshSet", new HashSet<QuantVariableRef>());
    put("subsetCheckingSetConstraints", new HashSet<FieldAccess>());
    put("subSetCheckingSetInitially", new HashSet<FieldAccess>());
    put("assignableSet", new HashSet<QuantVariableRef[]>()); 
    put("nothing", Boolean.FALSE); 
    put("routinebegin", Boolean.TRUE);  
    put("quantifier", Boolean.FALSE);
    put("quantVars", new HashSet<QuantVariable>());
    put("isHelper", Boolean.FALSE);
    

    put("firstExPost", Boolean.TRUE);
    put("isConstructor", Boolean.FALSE);
  }

  

  public List<String> getValidStr() {
    return validStr;
  }
}