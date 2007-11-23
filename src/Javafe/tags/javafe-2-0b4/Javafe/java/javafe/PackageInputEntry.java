/*
 * Created on Aug 21, 2005
 *
 * @design kiniry 21 Aug 2005 - Refactored out of InputEntry to avoid
 * existing recursion bug in typechecker in handling nested classes.
 */

package javafe;

import javafe.filespace.StringUtil;
import javafe.tc.OutsideEnv;

public class PackageInputEntry extends InputEntry {
  public PackageInputEntry(String n) { super(n); }
  public String type() { return "Package"; }
  public String typeOption() { return "package"; }
  public String verify() {
    return verify(name);
  }
  static public String verify(String name) {
    String[] p = StringUtil.parseList(name,'.');
    if (javafe.tc.OutsideEnv.reader.accessable(p)) {
      return null;
    }
    return "Package cannot be found";
  }
}