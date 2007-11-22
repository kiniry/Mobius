package mobius.directVCGen.formula.jmlTranslator.struct;

import java.util.ArrayList;
import java.util.List;
import java.util.Properties;

/**
 * Context properties that are made to replace the properties
 * that were once used in the translator.
 * @author J. Charles (julien.charles@inria.fr)
 */
public class ContextProperties extends Properties {

  /** */
  private static final long serialVersionUID = 1L; 
  /** the list of properties that can be used in a context properties. */
  private static final List<String> validStr = new ArrayList<String>();
 
  
  
  /** tell wether or not a predicate are being currently inspected. */
  public boolean fInspectingPred =  true;
  
  /** tell wether or not we are being currently inside a fresh annotation. */
  public boolean fresh = false;
  
  /** tell wether or not annotations are being currently inspected. */
  public boolean interesting;

  
  /**
   * initialize the properties with default values.
   */
  public ContextProperties() {
    initProperties(); 
  }
  
  @Override
  public Object put (final Object key, final Object value) {
    for (String valid: getValidStr()) {
      if (key.equals(valid)) {
        return super.put(key, value);
      }
    }
    throw new IllegalArgumentException("Invalid key: " + key + "\n" +
        " the solutions were: " + getValidStr());
  }
  
  /**
   * Returns the list of valid strings... should be overridden when
   * subclassed.
   * @return a list which can be empty
   */
  public List<String> getValidStr() {
    return validStr;
  }

  private void initProperties() {
    validStr.add("old");
    validStr.add("unaryOp");
    super.put("old", Boolean.FALSE);
    super.put("unaryOp", 0);
  }

  
}
