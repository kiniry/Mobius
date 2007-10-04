package mobius.directVCGen.formula.jmlTranslator.struct;

import java.util.HashSet;
import java.util.Properties;

import javafe.ast.FieldAccess;
import escjava.sortedProver.Lifter.QuantVariable;
import escjava.sortedProver.Lifter.QuantVariableRef;

/** Properties that are passed as argument of the visitor. */
public final class MethodProperties extends Properties {

  /** */
  private static final long serialVersionUID = 1L;
  
  
  /** valid properties string. */
  private static final String [] validStr = {
    "unaryOp",  
    "old",
    "freshSet", 
    "subsetCheckingSetConstraints",
    "subSetCheckingSetInitially",
    "assignableSet",
    "nothing",
    "routinebegin",
    "quantifier",
    "quantVars",
    "isHelper",
    "firstExPost", 
    "isConstructor"
  };
  
  
  /** key to represent a result in the properties set. */  
  public QuantVariableRef fResult;
  
  
  /**
   * initialize the properties with default values.
   */
  public MethodProperties() {
    initProperties(); 
  }
  
  
  private void initProperties() {
   
    
    put("unaryOp", 0);
    put("old", Boolean.FALSE);
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

  
  @Override
  public Object put (final Object key, final Object value) {
    for (String valid: validStr) {
      if (key.equals(valid)) {
        return super.put(key, value);
      }
    }
    throw new IllegalArgumentException("Invalid key: " + key);
  }
}