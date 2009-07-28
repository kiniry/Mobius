/*
 * Created on Aug 21, 2005
 *
 * @design kiniry 21 Aug 2005 - Refactored out of InputEntry to avoid
 * existing recursion bug in typechecker in handling nested classes.
 */

package javafe;

public class FileInputEntry extends InputEntry {
  public FileInputEntry(String n) { super(n); }
  public String type() { return "File"; }
  public String typeOption() { return "file"; }
  public String verify() {
    return verify(name);
  }
  static public String verify(String name) {
    java.io.File f= new java.io.File(name);
    if (f.exists() && f.isFile()) return null;
    return "File does not exist";
  }
}