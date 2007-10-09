package mobius.directVCGen.formula.jmlTranslator.struct;

import java.util.ArrayList;
import java.util.List;
import java.util.Properties;

public class ContextProperties extends Properties {

  /** */
  private static final long serialVersionUID = 1L;
  
  
  /** tell wether or not a predicate are being currently inspected. */
  public boolean pred =  true;
  
  /** tell wether or not we are being currently inside a fresh annotation. */
  public boolean fresh = false;
  
  /** tell wether or not annotations are being currently inspected. */
  public boolean interesting;
  
  
  private static final List<String> validStr = new ArrayList<String>();
  static
  { 
    validStr.add("old");
    validStr.add("unaryOp");
  };
  
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
  
  public List<String> getValidStr() {
    return validStr;
 }

  private void initProperties() {
    super.put("old", Boolean.FALSE);
    super.put("unaryOp", 0);
  }

  
}
