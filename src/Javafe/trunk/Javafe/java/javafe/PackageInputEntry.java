/*
 * Created on Aug 21, 2005
 *
 * @design kiniry 21 Aug 2005 - Refactored out of InputEntry to avoid
 * existing recursion bug in typechecker in handling nested classes.
 */

package javafe;

import javafe.filespace.StringUtil;

public class PackageInputEntry extends InputEntry {
  public PackageInputEntry(/*@non_null*/String n) { super(n); }
  public /*@non_null*/String type() { return "Package"; }
  public /*@non_null*/String typeOption() { return "package"; }
  public /*@nullable*/String verify() {
    return verify(name);
  }
  //@ requires javafe.tc.OutsideEnv.initialized;
  static public /*@nullable*/String verify(/*@non_null*/String name) {
    String[] p = StringUtil.parseList(name,'.');
    if ((/*+@(non_null)*/javafe.tc.OutsideEnv.reader).accessable(p)) {
      return null;
    }
    return "Package cannot be found";
  }
}