package mobius.bico;

import java.util.ArrayList;
import java.util.List;

import org.apache.bcel.classfile.Method;
import org.apache.bcel.generic.ConstantPoolGen;
import org.apache.bcel.generic.InvokeInstruction;
import org.apache.bcel.generic.MethodGen;
import org.apache.bcel.generic.Type;

/**
 * 
 * @author L. Hubert (lhubert@irisa.fr)
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

    public MethodType(final String name, final Type[] targs, final Type tret) {
      this.fArgsType = targs;
      this.fReturnType = tret;
      this.fName = name;
    }
    
    /**
     * Constructor form a method gen.
     * @param mg the object to abstract
     */
    public MethodType(final MethodGen mg) {
      this.fArgsType = mg.getArgumentTypes();
      this.fReturnType = mg.getReturnType();
      this.fName = mg.getName();
    }
    
    
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
    public int hashCode() {
      return toString().hashCode();
    }

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

  public static class MethodNotFoundException extends Exception {
    private static final long serialVersionUID = 1L;

    public MethodNotFoundException(final MethodType mt) {
      super(mt.toString());
    }
  }

  /** the list of method types already seen. */
  private List<MethodType> fMethodList = new ArrayList<MethodType>();
  

  public void addMethod(final MethodGen m) {
    final MethodType mt = new MethodType(m);
    
    if (find(mt) == null) {
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

  private String getName(final MethodType mt) throws MethodNotFoundException {
    final MethodType mtOld = find(mt);
    if (mtOld != null) {
      return mtOld.getCoqName();
    }
    else {
      throw new MethodNotFoundException(mt);
    }
  }

  public String getName(final MethodGen m) throws MethodNotFoundException {
    final String name = m.getName();
    final Type[] targs = m.getArgumentTypes();
    final Type tret = m.getReturnType();
    final MethodType mt = new MethodType(name, targs, tret);
    return getName(mt);
  }

  public String getName(final Method met) throws MethodNotFoundException {
    final String name = met.getName();
    final Type[] targs = met.getArgumentTypes();
    final Type tret = met.getReturnType();
    final MethodType mt = new MethodType(name, targs, tret);
    return getName(mt);
  }

  public String getName(final InvokeInstruction ii, final ConstantPoolGen cpg)
    throws MethodNotFoundException {
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

  private MethodType find(final MethodType mt) {
    for (MethodType tmp: fMethodList) {
      if (tmp.equals(mt)) {
        return tmp;
      }
    }
    return null;
  }

}
