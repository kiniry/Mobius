package mobius.bico.dico;

import java.util.ArrayList;
import java.util.List;

import mobius.bico.Util;

import org.apache.bcel.classfile.Method;
import org.apache.bcel.generic.ConstantPoolGen;
import org.apache.bcel.generic.InvokeInstruction;
import org.apache.bcel.generic.MethodGen;
import org.apache.bcel.generic.Type;

/**
 * 
 * @author L. Hubert (lhubert@irisa.fr) 
 * with some slight modifications 
 * from J. Charles (julien.charles@inria.fr)
 */
public class MethodHandler {

  /**
   * 
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
    private final Type[] fArgsType;

    /** the coq name of the method. */
    private String fCoqName;

    private MethodType(final String name, final Type[] targs, final Type tret) {
      fArgsType = targs;
      fReturnType = tret;
      fName = name;
    }
    
    /**
     * Constructor from a method gen.
     * @param mg the object to abstract
     */
    public MethodType(final MethodGen mg) {
      this(mg.getName(),  mg.getArgumentTypes(), mg.getReturnType());
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

    @Override
    public boolean equals(final Object o) {
      if (o instanceof MethodType) {
        final MethodType mt = (MethodType) o;
        if (!(getName().equals(mt.getName()) && 
            (fArgsType.length == mt.fArgsType.length) && 
            fReturnType.equals(mt.fReturnType))) {
          return false;
        }
        for (int i = 0; i < fArgsType.length; i++) {
          if (!fArgsType[i].equals(mt.fArgsType[i])) {
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
  

  public void addMethod(final MethodGen m) {
    final MethodType mt = new MethodType(m);
    addMethod(mt);
  }

  public void addMethod(final MethodType mt) { 
    if (!fMethodList.contains(mt)) {
      final List l = findByName(mt);
      final int postfix = l.size();
      if (postfix > 0) {
        mt.setCoqName(Util.coqify(mt.getName()) + postfix);
      }
      else {
        mt.setCoqName(Util.coqify(mt.getName()));
      }
      fMethodList.add(mt);
    }
  }

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

  public String getName(final MethodGen m) {
    final MethodType mt = new MethodType(m);
    return getName(mt);
  }

  public String getName(final Method met) {
    final MethodType mt = new MethodType(met);
    return getName(mt);
  }

  public String getName(final InvokeInstruction ii, final ConstantPoolGen cpg) {
    final String name = ii.getMethodName(cpg);
    final Type[] targs = ii.getArgumentTypes(cpg);
    final Type tret = ii.getReturnType(cpg);
    final MethodType mt = new MethodType(name, targs, tret);
    return getName(mt);
  }

  private List<MethodType> findByName(final MethodType mt) {
    final List<MethodType> ret = new ArrayList<MethodType>();
    for (MethodType tmp: fMethodList) {
      if (Util.coqify(tmp.getName()).equals(Util.coqify(mt.getName()))) {
        ret.add(tmp);
      }
    }
    return ret;
  }

}
