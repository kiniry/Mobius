package mobius.bico;

import java.io.PrintStream;

import org.apache.bcel.classfile.JavaClass;
import org.apache.bcel.generic.ArrayType;
import org.apache.bcel.generic.BasicType;
import org.apache.bcel.generic.Instruction;
import org.apache.bcel.generic.ObjectType;
import org.apache.bcel.generic.ReferenceType;
import org.apache.bcel.generic.Type;
import org.apache.bcel.util.Repository;

public final class Util {

  /**
   * Replaces all chars not accepted by coq by "_".
   * 
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
   * 
   * @return i%Z or (-i)%Z
   */
  static String printZ(final Number index) {
    return Util.printZ(index.intValue());
  }

  /**
   * for printing offsets.
   * 
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
   * for instruction which are not implemented (yet) in Bico.
   */
  static String unimplemented(final String instruction, final Instruction ins) {
    final String name = ins.getName();
    System.err.println("Unimplemented " + instruction + ": " + name);
    return upCase(name) + " (* Unimplemented *)";
  }

  /**
   * for instructions which should not exist - this is probably an error in
   * Bico.
   */
  static String unknown(String instruction, Instruction ins) {
    String name = ins.getName();
    System.err.println("Unknown " + instruction + ": " + name);
    return "Nop (* " + name + " *)";
  }

  static void unhandled(String str, Type t) {
    System.err.println("Unhandled type (" + str + "): " + t.toString());
  }

  /**
   * variant with some more information about instruction kind.
   */ 
  static String unhandled(String instruction, Instruction ins) {
    String name = ins.getName();
    System.err.println("Unhandled " + instruction + ": " + name);
    return "Nop (* " + name + " *)";
  }

  /**
   * for instructions not handled by Bicolano.
   */
  static String unhandled(Instruction ins) {
    return unhandled("Instruction", ins);
  }

  /**
   * Handles type or void.
   * 
   * @param strin
   *            is the repository where information on classes can be found
   * @return (Some "coq type t") or None
   * @throws ClassNotFoundException
   */
  static String convertTypeOption(Type t, Repository strin)
  throws ClassNotFoundException {
    if (t == Type.VOID || t == null) {
      return "None";
    }
    return "(Some " + Util.convertType(t, strin) + ")";
  }

  /**
   * @param strin
   *            is the repository where information on classes can be found
   * @return Coq value of t of type type
   * @throws ClassNotFoundException
   */
  static String convertType(final Type t, final Repository strin)
    throws ClassNotFoundException {
    if (t instanceof BasicType) {
      return "(PrimitiveType " + Util.convertPrimitiveType((BasicType) t) + ")";
    } 
    else if (t instanceof ReferenceType) {
      return "(ReferenceType " + Util.convertReferenceType((ReferenceType) t, strin) + ")";
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
   * @throws ClassNotFoundException
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

  public static void writeln(PrintStream out, int tabs, String s) {
    final StringBuffer str = new StringBuffer();
    for (int i = 0; i < tabs * Util.TAB; i++) {
      str.append(' ');
    }
    str.append(s);
    out.println(str.toString());
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

  /** the size of a tab used in writeln. */
  static final int TAB = 2;

}
