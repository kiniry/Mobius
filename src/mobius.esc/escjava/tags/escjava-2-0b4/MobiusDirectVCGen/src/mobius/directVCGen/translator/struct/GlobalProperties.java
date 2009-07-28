package mobius.directVCGen.translator.struct;

import java.util.HashSet;
import java.util.Properties;
import java.util.Set;

import javafe.ast.FieldAccess;
import javafe.ast.Identifier;

/**
 * Properties that are passed as argument of the visitor.
 * Made to replace Claudia's properties use. 
 * @author J. Charles (julien.charles@inria.fr)
 */
public final class GlobalProperties extends Properties {
  /** */
  private static final long serialVersionUID = 1L;

  /** valid properties string. */
  private static final String [] validStr = {
  };

  
  public Set<javafe.ast.Type> visibleTypeSet = new HashSet<javafe.ast.Type>();

  
  public final Set<FieldAccess> subsetCheckingSet = new HashSet<FieldAccess>();

  /** the currently inspected class identifier. */
  private Identifier fClassId = Identifier.intern("");
  
  
  public GlobalProperties() {
    initProperties(); 
  }
  
  private void initProperties() { 
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

  /**
   * Returns the current class id
   * or the id made of the empty string.
   * @return the current class id
   */
  public Identifier getClassId() {
    return fClassId;
  }

  public void setClassId(final Identifier id) {
    fClassId = id;
  }
}
