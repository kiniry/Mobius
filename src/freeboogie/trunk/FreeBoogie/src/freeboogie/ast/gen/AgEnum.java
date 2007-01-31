/** Public domain. */

package freeboogie.ast.gen;

import java.util.ArrayList;
import java.util.List;

/**
 * Represents an enum from the abstract grammar.
 * 
 * @author rgrig
 * @author reviewed by TODO
 */
public class AgEnum {
  /** The name of the enum. */
  public String name = null;

  /** The values of the enum. */
  public List<String> values = new ArrayList<String>(10);
}
