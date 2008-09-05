package mobius.bico;

import java.io.File;
import java.io.FileFilter;
import java.util.Stack;

import mobius.bico.Constants.Suffix;
import mobius.bico.bicolano.AType;
import mobius.bico.bicolano.coq.Translator;

import org.apache.bcel.classfile.JavaClass;
import org.apache.bcel.generic.ArrayType;
import org.apache.bcel.generic.BasicType;
import org.apache.bcel.generic.Instruction;
import org.apache.bcel.generic.ObjectType;
import org.apache.bcel.generic.ReferenceType;
import org.apache.bcel.generic.Type;
import org.apache.bcel.util.Repository;

/**
 * A class containing some utility methods.
 * 
 * @author J. Charles (julien.charles@inria.fr), P. Czarnik
 *         (czarnik@mimuw.edu.pl), L. Hubert (laurent.hubert@irisa.fr)
 */
public class Util {
  /** the size of a tab used in writeln. */
  public static final String TAB = "  ";
  
  /** */
  protected Util() { }
  
  /**
   * Replaces all chars not accepted by coq by "_".
   * 
   * @param raw
   *            the string to coqify
   * @return null only if str == null
   */
  public static String coqify(final String raw) {
    String str = raw;
    if (str == null) {
      return null;
    } 
    else {
      str = str.replace('.', '_');
      str = str.replace('/', '_');
      // strout = strout.replace("(","_");
      // strout = strout.replace(")","_");
      str = str.replace('>', '_');
      str = str.replace('$', '_');
      str = str.replace('<', '_');
      return str;
    }
  }
  
  /**
   * @param s
   *            a string
   * @return s with the first char toUpperCase
   */
  public static String upCase(final String s) {
    if (s != null && s.length() > 0) {
      final char c1 = Character.toUpperCase(s.charAt(0));
      return Character.toString(c1) + s.substring(1);
    } 
    else {
      return null;
    }
  }
  

  
  /**
   * For instruction which are not implemented (yet) in Bico. Prints an error
   * message and returns a translation of the instruction.
   * 
   * @param instruction
   *            a String containing a representation of the instruction
   * @param ins
   *            the instruction object
   * @return the name of the instruction, uppercase, tagged as Unimplemented
   */
  public static String unimplemented(final String instruction,
                                     final Instruction ins) {
    final String name = ins.getName();
    System.err.println("Unimplemented " + instruction + ": " + name);
    return upCase(name) + " " + Translator.comment("Unimplemented");
  }
  
  /**
   * For instructions which should not exist - this is probably an error in
   * Bico.
   * 
   * @param str
   *            a string denoting the object
   * @param ins
   *            the instruction to state as unhandled
   * @return a valid coq structure
   */
  public static String unknown(final String str, final Instruction ins) {
    final String name = ins.getName();
    System.err.println("Unknown " + str + ": " + name);
    return "Nop " + Translator.comment(name);
  }
  
  /**
   * Write the error message if an unhandled type is encountered.
   * 
   * @param str
   *            the structure which was typed by the given type
   * @param t
   *            the type which was found
   */
  public static void unhandled(final String str, final Type t) {
    System.err.println("Unhandled type (" + str + "): " + t.toString());
  }
  
  /**
   * Variant with some more information about instruction kind.
   * 
   * @param str
   *            a string denoting the object
   * @param ins
   *            the instruction to state as unhandled
   * @return a valid coq structure
   */
  public static String unhandled(final String str, final Instruction ins) {
    final String name = ins.getName();
    System.err.println("Unhandled " + str + ": " + name);
    return "Nop " + Translator.comment(name);
  }
  
  /**
   * For instructions not handled by Bicolano.
   * 
   * @param ins
   *            the instruction to treat.
   * @return a String saying that the instruction is unhandled
   */
  public static String unhandled(final Instruction ins) {
    return unhandled("Instruction", ins);
  }
  
  /**
   * Handles type or void.
   * 
   * @param t
   *            the type to convert
   * @param repos
   *            is the repository where information on classes can be found
   * @return (Some "coq type t") or None
   * @throws ClassNotFoundException
   *             if the type couldn't be resolved
   */
  public static String convertTypeOption(final Type t, final Repository repos)
    throws ClassNotFoundException {
    if (t == Type.VOID || t == null) {
      return "None";
    }
    return "(Some " + AType.getInstance().convertType(t, repos) + ")";
  }
  

  

  

  
  /**
   * Returns a Coq version of the package name. If the package is a.bc.de it
   * will return aBcDe
   * 
   * @param pkg the original package name
   * @return the coqified version
   */
  public static String getCoqPackageName(final String pkg) {
    String pn;
    if (pkg.length() == 0) {
      pn = "EmptyPackageName";
    } 
    else {
      final char[] pna = pkg.toCharArray();
      int j = 0;
      for (int i = 0; i < pna.length; i++) {
        if (pna[i] == '.') {
          pna[j] = Character.toUpperCase(pna[++i]);
        } 
        else {
          pna[j] = pna[i];
        }
        j++;
      }
      pn = new String(pna, 0, j);
    }
    return pn;
  }
  
  /**
   * In the class constant pool a String value representing a reference type
   * name have the following format : RefT ::= Lclname; | [ RefT | [ BasicT
   * where clName is a String representing a class name of the form a/b/c
   * BasicT ::= I | B | S.
   * 
   * @param clname String representing a reference type name 
   * in the class file format
   * @return The class name
   */
  public static String classFormatName2Standard(final String clname) {
    String name = clname;
    // if it is an array type 
    while (name.startsWith("[")) {
      name = name.substring(1);
    }
    
    // if "name" denotes a basic type then return
    final BasicType [] bts = {Type.BOOLEAN, Type.INT,
                              Type.SHORT, Type.BYTE,
                              Type.CHAR, Type.LONG,
                              Type.FLOAT, Type.DOUBLE,
                              Type.VOID};
    for (BasicType t: bts) {
      if (t.getSignature().equals(name)) {
        return null;
      }
    }
    
    // else the type is not a basic type and thus, proceed
    // to getting a well formed Java class type
    
    if (name.startsWith("L")) {
      name = name.substring(1);
    } 
    
    if (name.endsWith(";")) {
      name = name.substring(0, name.length() - 1);
    }
    name = name.replace('/', '.');
    return name;
  }
  
  
  /**
   * Removes the class suffix from the given string.
   * @param clzz the name to remove the suffix from
   * @return a string without the class suffix
   */
  public static String removeClassSuffix(final String clzz) {
    return clzz.substring(0, clzz.length() - 
                            Suffix.CLASS.toString().length());
  }
  
  /**
   * Removes the coq suffix (.v) from the given string.
   * @param coqfile the string from which to remove the suffix
   * @return the same string without its last 2 characters
   */
  public static String removeCoqSuffix(final String coqfile) {
    return coqfile.substring(0, coqfile.length() - 
                            Suffix.COQ.length());
  }
  
  /**
   * Filters only valid directory names (directories with names that can be packages).
   * @author J. Charles (julien.charles@inria.fr)
   */
  public static class DirectoryFilter implements FileFilter {
    /**
     * Accept directories.
     * @param cf the file to inspect
     * @return true if this is a directory, and contains no dots
     */
    public boolean accept(final File cf) {
      return cf.isDirectory() && !cf.getParent().equals(cf) && 
              cf.getName().indexOf('.') == -1;
    }
  }
  
  /**
   * A file filter that keeps only files that hava a Class suffix (.class).
   * @author J. Charles (julien.charles@inria.fr)
   */
  public static class ClassFilter implements FileFilter {
    /** {@inheritDoc} */
    public boolean accept(final File cf) {
      return ((cf.isFile()) && cf.getName().endsWith(Suffix.CLASS.toString()));
    }
  }
  
  /**
   * Returns the package path. Basically replaces the dots with slashes.
   * @param javaClass the Class from which the package is taken
   * @return a file being the path correspondint to the package
   */
  public static File getPackageDir(final JavaClass javaClass) {
    return new File(javaClass.getPackageName().replace('.',
                                                       File.separatorChar));
  }
  
  /**
   * Returns a string representing the name of the given type.
   * @param rtyp the type that we want to get a representation from
   * @return a string representing the type or null
   */
  public static String getTypeName(final ReferenceType rtyp) {
    String className = null;
    
    if (rtyp instanceof ObjectType) {
      final ObjectType otyp = (ObjectType) rtyp;
      className = otyp.getClassName();
    }
    else if (rtyp instanceof ArrayType) {
      final ArrayType atyp = (ArrayType) rtyp;
      final Type type = atyp.getBasicType();
      if (type instanceof ReferenceType) {
        className = getTypeName((ReferenceType) type);
      }
    }
    return className;
  }

  /**
   * Treat all classes in the directory passed as value to the 
   * input parameter <code>-lib</code>.
   * 
   * @param sourceDir the source directory
   * @param pkg the current package name
   * 
   * @return a stack containing all the classes that were collected
   */
  public static Stack<String> collectClasses(final File sourceDir,
                                     final String pkg) {
    final File f = new File(sourceDir, pkg);
    final File[] classfiles = f.listFiles(new ClassFilter());    
    final File[] dirfiles = f.listFiles(new DirectoryFilter());
    final Stack<String> pendingClasses = new Stack<String>();
    for (File cf: classfiles) {
      String className = 
        pkg + removeClassSuffix(cf.getName()); 
      className = className.replace(File.separatorChar,
                                    Constants.JAVA_NAME_SEPARATOR);
      pendingClasses.add(className);
    }
    
    for (File cf: dirfiles) {
      final String p = pkg + cf.getName() + File.separatorChar;
      pendingClasses.addAll(collectClasses(sourceDir, p));
    }
    return pendingClasses;
  }
}
