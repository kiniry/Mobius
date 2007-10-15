package mobius.directVCGen.formula.jmlTranslator.struct;

import java.util.HashSet;
import java.util.Properties;
import java.util.Set;

import javafe.ast.FieldAccess;
import javafe.ast.Identifier;

/** Properties that are passed as argument of the visitor. */
public final class GlobalProperties extends Properties {
  /** */
  private static final long serialVersionUID = 1L;

  /** valid properties string. */
  private static final String [] validStr = {
    "doSubsetChecking"
  };
  
  public Set<javafe.ast.Type> visibleTypeSet = new HashSet<javafe.ast.Type>();
  

  


  public Identifier classId = Identifier.intern("");
  
  public final HashSet<FieldAccess> subsetCheckingSet = new HashSet<FieldAccess>();
  
  public GlobalProperties() {
    initProperties(); 
  }
  
  private void initProperties() {
    put("doSubsetChecking", Boolean.FALSE);  
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