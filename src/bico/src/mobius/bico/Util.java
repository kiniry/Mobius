package mobius.bico;

import java.io.OutputStream;
import java.io.PrintStream;

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
 * @author J. Charles (julien.charles@inria.fr), 
 * P. Czarnik (czarnik@mimuw.edu.pl), 
 * L. Hubert (laurent.hubert@irisa.fr)
 */
public final class Util {
  /** the size of a tab used in writeln. */
  static final String TAB = "  ";
  
  /**
   * @deprecated
   */
  private Util() {
    
  }
  
  /**
   * Replaces all chars not accepted by coq by "_".
   * @param raw the string to coqify
   * @return null only if str == null
   */
  static String coqify(final String raw) {
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
   * @param s a string
   * @return s with the first char toUpperCase
   */
  static String upCase(final String s) {
    if (s != null && s.length() > 0) {
      final char c1 = Character.toUpperCase(s.charAt(0));
      return Character.toString(c1) + s.substring(1);
    } 
    else {
      return null;
    }
  }

  /**
   * for printing offsets.
   * @param index the offset to print
   * @return i%Z or (-i)%Z
   */
  static String printZ(final Number index) {
    return Util.printZ(index.intValue());
  }

  /**
   * for printing offsets.
   * @param index the offset to print
   * @return i%Z or (-i)%Z
   */
  static String printZ(final int index) {
    if (index < 0) {
      return "(" + index + ")%Z";
    } 
    else {
      return String.valueOf(index) + "%Z";
    }
  }

  /**
   * For instruction which are not implemented (yet) in Bico.
   * Prints an error message and returns a translation of the
   * instruction.
   * @param instruction a String containing a representation
   * of the instruction
   * @param ins the instruction object
   * @return the name of the instruction, uppercase, tagged as
   * Unimplemented
   */
  static String unimplemented(final String instruction, final Instruction ins) {
    final String name = ins.getName();
    System.err.println("Unimplemented " + instruction + ": " + name);
    return upCase(name) + " (* Unimplemented *)";
  }

  /**
   * For instructions which should not exist - this is probably an error in
   * Bico.
   * @param str  a string denoting the object
   * @param ins the instruction to state as unhandled
   * @return a valid coq structure
   */
  static String unknown(final String str, final  Instruction ins) {
    final String name = ins.getName();
    System.err.println("Unknown " + str + ": " + name);
    return "Nop (* " + name + " *)";
  }

  /**
   * Write the error message if an unhandled type is encountered.
   * @param str the structure which was typed by the given type
   * @param t the type which was found
   */
  static void unhandled(final String str, final Type t) {
    System.err.println("Unhandled type (" + str + "): " + t.toString());
  }

  /**
   * Variant with some more information about instruction kind.
   * @param str  a string denoting the object
   * @param ins the instruction to state as unhandled
   * @return a valid coq structure
   */ 
  static String unhandled(final String str, final Instruction ins) {
    final String name = ins.getName();
    System.err.println("Unhandled " + str + ": " + name);
    return "Nop (* " + name + " *)";
  }

  /**
   * For instructions not handled by Bicolano.
   * @param ins the instruction to treat.
   * @return a String saying that the instruction is unhandled
   */
  static String unhandled(final Instruction ins) {
    return unhandled("Instruction", ins);
  }

  /**
   * Handles type or void.
   * @param t the type to convert
   * @param repos is the repository where information on classes can be found
   * @return (Some "coq type t") or None
   * @throws ClassNotFoundException if the type couldn't be resolved
   */
  static String convertTypeOption(final Type t, final Repository repos)
    throws ClassNotFoundException {
    if (t == Type.VOID || t == null) {
      return "None";
    }
    return "(Some " + Util.convertType(t, repos) + ")";
  }

  /**
   * Convert a type to a Coq valid type.
   * @param t the type to convert
   * @param repos is the repository where information on classes can be found
   * @return Coq value of t of type type
   * @throws ClassNotFoundException if the type cannot be resolved
   */
  static String convertType(final Type t, final Repository repos)
    throws ClassNotFoundException {
    if (t instanceof BasicType) {
      return "(PrimitiveType " + Util.convertPrimitiveType((BasicType) t) + ")";
    } 
    else if (t instanceof ReferenceType) {
      return "(ReferenceType " + Util.convertReferenceType((ReferenceType) t, repos) + ")";
    } 
    else {
      unhandled("Unhandled Type: ", t);
      return "(ReferenceType (ObjectType javaLangObject (* " + t.toString() + " *) )";
    }
  }

  /**
   * @param type the type to convert
   * @param repos is the repository where information on classes can be found
   * @return Coq value of t of type refType
   * @throws ClassNotFoundException if a type cannot have its class resolved
   */
  static String convertReferenceType(final ReferenceType type, 
                                  final Repository repos) throws ClassNotFoundException {
    String convertedType;
    if (type instanceof ArrayType) {
      convertedType = "(ArrayType " + 
             convertType(((ArrayType) type).getElementType(), repos) + ")";
    } 
    else if (type instanceof ObjectType) {
      final ObjectType ot = (ObjectType) type;
      try {
        if (ot.referencesClassExact()) {
          convertedType = "(ClassType " + coqify(ot.getClassName()) + ".className)";
        } 
        else if (ot.referencesInterfaceExact()) {
          // TODO: adjust to the structure of "interface" modules
          convertedType = "(InterfaceType " + coqify(ot.getClassName()) + ".interfaceName)";
        } 
        else {
          unhandled("ObjectType", type);
          convertedType = "(ObjectType javaLangObject (* " + type.toString() + " *) )";
        }
      } 
      catch (ClassNotFoundException e) {
        final JavaClass jc = repos.findClass(ot.getClassName());
        if (jc != null) {
          if (jc.isClass()) {
            return "(ClassType " + coqify(ot.getClassName()) + ".className)";
          }
          else if (jc.isInterface()) {
            return "(InterfaceType " + coqify(ot.getClassName()) + ".interfaceName)";
          }
        }
        throw e;
      }
    } 
    else {
      unhandled("ReferenceType", type);
      convertedType = "(ObjectType javaLangObject (* " + type.toString() + " *) )";
    }
    return convertedType;
  }

  /**
   * @param t the type to convert
   * @return Coq value of t of type primitiveType
   */
  static String convertPrimitiveType(final BasicType t) {
    if (t == Type.BOOLEAN || t == Type.BYTE || t == Type.SHORT || t == Type.INT) {
      return (t.toString().toUpperCase());
    } 
    else {
      unhandled("BasicType", t);
      return ("INT (* " + t.toString() + " *)");
    }
  }


  /**
   * A stream to use instead of writeln.
   * @author J. Charles (julien.charles@inria.fr)
   */
  public static class Stream extends PrintStream {
    /** the number of tabs. */
    private int fTab;
    /** the tabulations to add. */
    private String fStrTab = "";
    
    /**
     * Create a new stream from an existing one.
     * @param out an already existing stream
     */
    public Stream(final OutputStream out) {
      super(out);
    }
    
    /**
     * Write a line with a given tabulation.
     * @param tab the number of tabulation
     * @param s the string to write
     */  
    public void println(final int tab, final String s) {
      if (tab < 0) {
        super.println(s.toString());
      }
      final StringBuffer str = new StringBuffer();
      for (int i = 0; i < tab; i++) {
        str.append(TAB);
      }
      str.append(s);
      super.println(str.toString());
    }
    
    /**
     * Print the given string, but putting tabulations
     * wherever necessary.
     * @param s the string to print tabbed
     */
    public void println(final String s) {
      String str = fStrTab + s;
      str = str.replaceAll("\n", "\n" + fStrTab);
      super.println(str);
    }
    
    /**
     * Increments the tabulation.
     */
    public void incTab() {
      fTab++;
      fStrTab += TAB;
    }
    
    /**
     * Decrements the tabulations.
     */
    public void decTab() {
      if (fTab > 0) {
        fTab--;
        fStrTab  = "";
        for (int i = 0; i < fTab; i++) {
          fStrTab += TAB;
        }
      }
    }
    
  }
  /**
   * Returns a Coq version of the package name. If the package is a.bc.de
   * it will return  aBcDe
   * @param pkg the original package name
   * @return the coqified version
   */
  static String getCoqPackageName(final String pkg) {
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



}