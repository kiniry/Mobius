/** Public domain. */

package freeboogie.ast.gen;

import java.util.ArrayList;
import java.util.List;

/**
 * Represents a class from the abstract grammar.
 * 
 * @author rgrig 
 * @author reviewed by TODO
 */
public class AgClass {
  /** The name of the class. */
  public String name = null;
  
  /** The base class of this class. TODO: default? */
  public String base = null;
  
  /** The class members. */
  public List<AgMember> members = new ArrayList<AgMember>(10);
  
  /** The enums defined in this class. */
  public List<AgEnum> enums = new ArrayList<AgEnum>();
  
  /** The (textual) invariants that this class must obey. */
  public List<String> invariants = new ArrayList<String>();
  
  /**
   * Returns the enum with a certain name or creates one if none
   * exists. This function does a linear search so it is a good
   * candidate for performance improvement if needed. I don't expect
   * that to be the case because typically a class has at most one enum.
   *  
   * @param enumName the name of the enum
   * @return an {@code AgEnum} object representing the requested enum
   */
  public AgEnum getEnum(String enumName) {
    AgEnum r = null;
    for (AgEnum it : enums) {
      if (it.name.equals(enumName)) r = it; 
    }
    if (r == null) {
      r = new AgEnum();
      r.name = enumName;
      enums.add(r);
    }
    return r;
  }
}
