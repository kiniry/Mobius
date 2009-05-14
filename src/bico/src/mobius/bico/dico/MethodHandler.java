package mobius.bico.dico;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

import mobius.bico.Util;

import org.apache.bcel.classfile.Method;
import org.apache.bcel.generic.ConstantPoolGen;
import org.apache.bcel.generic.InvokeInstruction;
import org.apache.bcel.generic.MethodGen;
import org.apache.bcel.generic.Type;

/**
 * The method handler class is used to have some Java
 * representation of methods, ready to translate for 
 * Bicolano.
 * Methods here are associated with numbers, and also with
 * the usual representation: name, arg type, return type.
 * 
 * @author L. Hubert (lhubert@irisa.fr) 
 * with some slight modifications 
 * from J. Charles (julien.charles@inria.fr)
 */
public class MethodHandler {


  /**
   * A structure to represent methods for bicolano.
   * @author L. Hubert (lhubert@irisa.fr)
   */
  private static class MethodType {
    /**
     * name is the "coqified" version of the class name. This name cannot be
     * used to identify a method. Although it is not safe, two methods are
     * considered to be identical when they have the same name, the same
     * arguments and the same return value.
     */
    private final String fName;

    /** the method return type. */
    private final Type fReturnType;

    /** the argument types. */
    private final List<Type> fArgsType;

    /** the coq name of the method. */
    private String fCoqName;

    /**
     * Construct a method type.
     * @param name the name of the method
     * @param targs the type of its arguments
     * @param tret the type of its return value
     */
    private MethodType(final String name, final Type [] targs, final Type tret) {
      String arguments = "T";
      
      fArgsType = new ArrayList<Type>();
      for (Type t: targs) {
        fArgsType.add(t);
        arguments += "_" + t.toString();
      }
      arguments = Util.coqify(arguments);
      fReturnType = tret;
      //
      
      fName = name + arguments;
    }
    
    /**
     * Constructor from a method gen.
     * @param mg the object to abstract
     */
    public MethodType(final MethodGen mg) {
      this(mg.getName(),  
           mg.getArgumentTypes(), mg.getReturnType());
    }
    
    /**
     * Constructor from a method definition.
     * @param met the object to abstract
     */
    public MethodType(final Method met) {
      this(met.getName(),
           met.getArgumentTypes(),
           met.getReturnType());
    }

    /** {@inheritDoc} */
    @Override
    public boolean equals(final Object o) {
      if (o instanceof MethodType) {
        final MethodType mt = (MethodType) o;
        if (!(getName().equals(mt.getName()) && 
             (fArgsType.size() == mt.fArgsType.size()) && 
             fReturnType.equals(mt.fReturnType))) {
          return false;
        }
        final Iterator<Type> iter = mt.fArgsType.iterator();
        for (Type t: fArgsType) {
          if (!t.equals(iter.next())) {
            return false;
          }
        }
        return true;
      }
      return false;
    }
    
    /**
     * The hashcode is computed from the toString value.
     * @return a valid hashcode
     */
    @Override
    public int hashCode() {
      return toString().hashCode();
    }

    /**
     * @return Name [ retType, argType ]
     */
    @Override
    public String toString() {
      return getName() + " [" + fReturnType + ", " + fArgsType + "]";
    }

    /**
     * @param coqName
     *            the name it will be referenced to in Bicolano. This name
     *            identifies the method (it takes in account it arguments)
     *            and is compatible with coq (has been "coqified").
     */
    public void setCoqName(final String coqName) {
      fCoqName = coqName;
    }

    /**
     * @return the abstract name it will be referenced to in Bicolano. This
     *         name identifies the method (it takes in account it arguments)
     *         and is compatible with coq (has been "coqified").
     */
    public String getCoqName() {
      return fCoqName;
    }

    /**
     * @return the java name
     */
    public String getName() {
      return fName;
    }
  }

  /** the list of method types already seen. */
  private List<MethodType> fMethodList = new ArrayList<MethodType>();
  
  /**
   * Adds the method type of the 
   * method to the list of methods. If the the method type 
   * is already registered it is not added.
   * @param m the method to add.
   */
  public void addMethod(final MethodGen m) {
    final MethodType mt = new MethodType(m);
    addMethod(mt);
  }

  /**
   * Adds the method to the list of method. If the method 
   * was already in the list it is not added a second time.
   * @param mt the method to add
   */
  private void addMethod(final MethodType mt) { 
    if (!fMethodList.contains(mt)) {
      mt.setCoqName(Util.coqify(mt.getName()));
      fMethodList.add(mt);
    }
  }

  /**
   * Returns the name of the method used in bicolano,
   * preferably if the method was previously registered in the 
   * method list.
   * If it was not, it also adds the method to the list.
   * 
   * @param mt the method to look for 
   * @return the string representing the name of the method
   */
  private String getName(final MethodType mt) {
    final int idx = fMethodList.indexOf(mt);
    if (idx != -1) {
      return fMethodList.get(idx).getCoqName();
    }
    else {
      System.err.println("Method " + mt + " is unknown... let's add it!");
      addMethod(mt);
      return getName(mt);
    }
  }

  /**
   * Returns the coqified name of the method.
   * @param m the method to get the name from
   * @return the name of the method.
   */
  public String getName(final MethodGen m) {
    final MethodType mt = new MethodType(m);
    return getName(mt);
  }

  /**
   * Returns the coqified name of the method.
   * @param met the method to translate
   * @return the name of the method
   */
  public String getName(final Method met) {
    final MethodType mt = new MethodType(met);
    return getName(mt);
  }

  
  /**
   * Returns the coqified name of the method. The first
   * argument has to be of the class InvokeInstruction.
   * None of the arguments shall be null.
   * @param ii the instruction where the method call occur.
   * @param cpg the constant pool to resolve the name.
   * @return the name of the method
   */
  public String getName(final InvokeInstruction ii, final ConstantPoolGen cpg) {
    final Type[] targs = ii.getArgumentTypes(cpg);
    final String name = ii.getMethodName(cpg);
    final Type tret = ii.getReturnType(cpg);
    final MethodType mt = new MethodType(name, targs, tret);
    return getName(mt);
  }

}
