package mobius.directVCGen.translator.struct;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import escjava.sortedProver.Lifter.QuantVariableRef;

/**
 * Context properties that are made to replace the properties
 * that were once used in the translator.
 * @author J. Charles (julien.charles@inria.fr)
 */
public class ContextProperties {

  /** */
  private static final long serialVersionUID = 1L; 
  /** the list of properties that can be used in a context properties. */
  private static final List<String> validStr = new ArrayList<String>();
 
 
  /** tell wether or not a predicate is being currently inspected. */
  public boolean fInspectingPred =  true;
  
  /** tell wether or not we are currently inside a fresh annotation. */
  public boolean fresh = false;
  
  /** tell wether or not we are currently inside an old annotation. */
  private boolean fOld;
  /** the set of fresh variables. */
  private final Set<QuantVariableRef> fFresh = 
    new HashSet<QuantVariableRef>();
    
  
  /**
   * initialize the properties with default values.
   */
  public ContextProperties() {
    fOld = false;
    fInspectingPred =  true;
    fresh = false;
  }
  
  

  /**
   * Returns the current set of fresh variables.
   * @return a set, never null.
   */
  public Set<QuantVariableRef> getFreshVariables() {
    return fFresh;
  }

  
  /**
   * Returns the list of valid strings... should be overridden when
   * subclassed.
   * @return a list which can be empty
   */
  public List<String> getValidStr() {
    return validStr;
  }

  public boolean isOld() {
    return fOld;
  }
 
  public void setOld(boolean b) {
    fOld = b;
  }




  
}
