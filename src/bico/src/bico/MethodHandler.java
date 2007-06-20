package bico;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

import org.apache.bcel.classfile.Method;
import org.apache.bcel.generic.ConstantPoolGen;
import org.apache.bcel.generic.InvokeInstruction;
import org.apache.bcel.generic.MethodGen;
import org.apache.bcel.generic.Type;

public class MethodHandler {

  private class MethodType {
    /**
     * name is the "coqified" version of the class name. This name cannot be
     * used to identify a method. Although it is not safe, two methods are
     * considered to be identical when they have the same name, the same
     * arguments and the same return value.
     */
    private final String name;

    private final Type tret;

    private final Type[] targs;

    private String coqName;

    public MethodType(String name, Type[] targs, Type tret) {
      this.targs = targs;
      this.tret = tret;
      this.name = name;
    }

    public boolean equals(Object o) {
      if (getName() == null || tret == null || targs == null)
        return false;
      if (o instanceof MethodType) {
        MethodType mt = (MethodType) o;
        if (!(getName().equals(mt.getName())
            && (targs.length == mt.targs.length) && tret
            .equals(mt.tret)))
          return false;
        for (int i = 0; i < targs.length; i++) {
          if (!targs[i].equals(mt.targs[i]))
            return false;
        }
        return true;
      }
      return false;
    }

    public String toString() {
      return getName() + " [" + tret + ", " + targs + "]";
    }

    /**
     * @param coqName
     *            the name it will be referenced to in Bicolano. This name
     *            identifies the method (it takes in account it arguments)
     *            and is compatible with coq (has been "coqified").
     */
    public void setCoqName(String coqName) {
      this.coqName = coqName;
    }

    /**
     * @return the abstract name it will be referenced to in Bicolano. This
     *         name identifies the method (it takes in account it arguments)
     *         and is compatible with coq (has been "coqified").
     */
    public String getCoqName() {
      return coqName;
    }

    /**
     * @return the java name
     */
    public String getName() {
      return name;
    }
  }

  public class MethodNotFoundException extends Exception {
    private static final long serialVersionUID = 1L;

    public MethodNotFoundException(MethodType mt) {
      super(mt.toString());
    }
  }

  ArrayList<MethodType> al = new ArrayList<MethodType>();

  public void addMethod(MethodGen m) {
    MethodType mt = new MethodType(m.getName(), m.getArgumentTypes(), m
                                   .getReturnType());
    if (find(mt) == null) {
      List l = findByName(mt);
      int postfix = l.size();
      if (postfix > 0)
        mt.setCoqName(Executor.coqify(mt.getName()) + postfix);
      else
        mt.setCoqName(Executor.coqify(mt.getName()));
      al.add(mt);
    }
  }

  private String getName(MethodType mt) throws MethodNotFoundException {
    MethodType mt_old = find(mt);
    if (mt_old != null)
      return mt_old.getCoqName();
    else
      throw new MethodNotFoundException(mt);
  }

  public String getName(MethodGen m) throws MethodNotFoundException {
    String name = m.getName();
    Type[] targs = m.getArgumentTypes();
    Type tret = m.getReturnType();
    MethodType mt = new MethodType(name, targs, tret);
    return getName(mt);
  }

  public String getName(Method met) throws MethodNotFoundException {
    String name = met.getName();
    Type[] targs = met.getArgumentTypes();
    Type tret = met.getReturnType();
    MethodType mt = new MethodType(name, targs, tret);
    return getName(mt);
  }

  public String getName(InvokeInstruction ii, ConstantPoolGen cpg)
  throws MethodNotFoundException {
    String name = ii.getMethodName(cpg);
    Type[] targs = ii.getArgumentTypes(cpg);
    Type tret = ii.getReturnType(cpg);
    MethodType mt = new MethodType(name, targs, tret);
    return getName(mt);
  }

  private List<MethodType> findByName(MethodType mt) {
    Iterator iter = al.iterator();
    ArrayList<MethodType> ret = new ArrayList<MethodType>();
    while (iter.hasNext()) {
      MethodType tmp = (MethodType) iter.next();
      if (Executor.coqify(tmp.getName()).equals(
                                                Executor.coqify(mt.getName()))) {
        ret.add(tmp);
      }
    }
    return ret;
  }

  private MethodType find(MethodType mt) {
    Iterator<MethodType> iter = al.iterator();
    while (iter.hasNext()) {
      MethodType tmp = iter.next();
      if (tmp.equals(mt))
        return tmp;
    }
    return null;
  }

}
