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
}
