package javafe;
import java.util.ArrayList;
import java.util.Iterator;

import javafe.filespace.StringUtil;

public class InputEntry {
    public InputEntry(String n) { name = n; }
    public String name;
    public ArrayList contents;
    public boolean auto = false;
    public String toString() { return name; }
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
	if (type.equals("file")) return new InputEntry.File(name);
	if (type.equals("dir")) return new InputEntry.Dir(name);
	if (type.equals("package")) return new InputEntry.Package(name);
	if (type.equals("class")) return new InputEntry.Class(name);
	if (type.equals("list")) return new InputEntry.List(name);
	return null;
    }

    static public InputEntry make(String name) {
	java.io.File f = new java.io.File(name);
	InputEntry ie = null;

	if (InputEntry.File.verify(name) == null) 
		ie = new InputEntry.File(name);
	else if (InputEntry.Dir.verify(name) == null) 
		ie = new InputEntry.Dir(name);
	else if (InputEntry.Package.verify(name) == null) 
		ie = new InputEntry.Package(name);
	else if (InputEntry.Class.verify(name) == null) 
		ie = new InputEntry.Class(name);
	else if (InputEntry.List.verify(name) == null) 
		ie = new InputEntry.List(name);

	if (ie == null) ie = new Unknown(name);
	ie.auto = true;
	return ie;
    }
    public InputEntry resolve() { return this; }

    static public class Unknown extends InputEntry {
	public Unknown(String n) { super(n); auto=true; }
	public String type() { return "Unknown"; }
	public InputEntry resolve() {
	    return make(name);
	}
    }
    static public class File extends InputEntry {
	public File(String n) { super(n); }
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
    static public class Dir extends InputEntry {
	public Dir(String n) { super(n); }
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
    static public class Package extends InputEntry {
	public Package(String n) { super(n); }
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
    static public class Class extends InputEntry {
	public Class(String n) { super(n); }
	public String type() { return "Class"; }
	public String typeOption() { return "class"; }
        public String verify() {
            return verify(name);
        }
	static public String verify(String name) {
	    int n = name.lastIndexOf('.');
            String[] p = StringUtil.parseList(name.substring(0,n==-1?0:n),'.');
	    if (!javafe.tc.OutsideEnv.reader.exists(p,name.substring(n+1))) {
		return "Class can not be found";
	    }
	    return null;
	}

    }
    static public class List extends InputEntry {
	public List(String n) { super(n); }
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
}
