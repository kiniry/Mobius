package javafe;

import java.util.ArrayList;
import java.util.Iterator;

import javafe.filespace.StringUtil;

public class InputEntry {
  public InputEntry(String n) { name = n; }
  public String name;
  public ArrayList contents;
  public boolean auto = false;
  public /*@non_null*/String toString() { return name; }
  public String type() { return ""; }
  public String typeOption() { return ""; }
  public String verify() { return null; }
  public String savedString() {
    String q = "";
    if (name.indexOf(' ') != -1) q = "\"";
    String t = typeOption();
    if (auto) t = "";
    else if (t.length() != 0) t = "-"+t+" ";
    return t + q + name + q;
  }
  static public void clear(ArrayList a) {
    Iterator i = a.iterator();
    while (i.hasNext()) {
      InputEntry ie = (InputEntry)i.next();
      ie.clear();
    }
  }
  public void clear() { contents = null; }
  
  static public InputEntry make(String type, String name) {
    if (type == null) return make(name);
    if (type.equals("file")) return new FileInputEntry(name);
    if (type.equals("dir")) return new DirInputEntry(name);
    if (type.equals("package")) return new PackageInputEntry(name);
    if (type.equals("class")) return new ClassInputEntry(name);
    if (type.equals("list")) return new ListInputEntry(name);
    return null;
  }
  
  static public InputEntry make(String name) {
    java.io.File f = new java.io.File(name);
    InputEntry ie = null;
    
    if (FileInputEntry.verify(name) == null) 
      ie = new FileInputEntry(name);
    else if (DirInputEntry.verify(name) == null) 
      ie = new DirInputEntry(name);
    else if (PackageInputEntry.verify(name) == null) 
      ie = new PackageInputEntry(name);
    else if (ClassInputEntry.verify(name) == null) 
      ie = new ClassInputEntry(name);
    else if (ListInputEntry.verify(name) == null) 
      ie = new ListInputEntry(name);
    
    if (ie == null) ie = new UnknownInputEntry(name);
    ie.auto = true;
    return ie;
  }
  
  public InputEntry resolve() { return this; }
  
  public boolean match(InputEntry ie) {
    return getClass() == ie.getClass() && name.equals(ie.name);
  }
}
