/*
 * Created on Aug 21, 2005
 *
 * @design kiniry 21 Aug 2005 - Refactored out of InputEntry to avoid
 * existing recursion bug in typechecker in handling nested classes.
 */

package javafe;

import java.io.File;

public class ListInputEntry extends InputEntry {
  public ListInputEntry(String n) { super(n); }
  public String type() { return "List"; }
  public String typeOption() { return "list"; }
  public String verify() {
    return verify(name);
  }
  static public String verify(String name) {
    java.io.File f= new java.io.File(name);
    if (f.exists() && f.isFile()) return null;
    return "List file does not exist";
  }
}