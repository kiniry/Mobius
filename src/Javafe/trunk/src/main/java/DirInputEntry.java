/*
 * Created on Aug 21, 2005
 *
 * @design kiniry 21 Aug 2005 - Refactored out of InputEntry to avoid
 * existing recursion bug in typechecker in handling nested classes.
 */

package javafe;

import java.io.File;

public class DirInputEntry extends InputEntry {
  public DirInputEntry(String n) { super(n); }
  public String type() { return "Directory"; }
  public String typeOption() { return "dir"; }
  public String verify() {
    return verify(name);
  }
  static public String verify(String name) {
    java.io.File f= new java.io.File(name);
    if (f.exists() && f.isDirectory()) return null;
    return "Directory does not exist";
  }
}