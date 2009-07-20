package mobius.bico.dico;

import java.io.PrintStream;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.Map;
import java.util.Map.Entry;

import mobius.bico.bicolano.coq.Translator;

import org.apache.bcel.classfile.JavaClass;

/**
 * This class is used to generate a dictionnary file
 * readable by OCaml.
 * <p>
 *  Here is an example of OCaml code that needs to be
 * added to the dictionary to have something usable.
 * (in a file TranslatorDef, it's the file included by
 * the generated file)
 *
 *<pre>
 *
 *    module OrderedInt =
 *  struct
 *    type t = int
 *    let compare= Pervasives.compare
 *  end
 *
 *  module OrderedPair =
 *    functor (M1:Map.OrderedType) ->
 *      functor (M2:Map.OrderedType) ->
 *  struct
 *    type t = M1.t * M2.t
 *    let compare = Pervasives.compare
 *  end
 *  module OrderedClassName = OrderedPair(OrderedInt)(OrderedInt)
 *  module OrderedMethodName = OrderedPair (OrderedClassName) (OrderedInt)
 *  module OrderedFieldName = OrderedMethodName
 *
 *  module DicoInt = Map.Make(OrderedInt)
 *  module DicoPN = DicoInt
 *  module DicoCN = Map.Make(OrderedClassName)
 *  module DicoMN = Map.Make(OrderedMethodName)
 *  module DicoFN = Map.Make(OrderedFieldName)
 *  module DicoMNPC = Map.Make (OrderedPair (OrderedMethodName) (OrderedInt))
 *  module DicoType = Map.Make (OrderedPair (OrderedInt) (OrderedClassName))
 *
 *  module PN = DicoPN
 *  module CN = DicoCN
 *  module FN = DicoFN
 *  module MN = DicoMN
 *  let pn : string PN.t = PN.empty
 *  let cn : string CN.t = CN.empty
 *  let fn : string FN.t = FN.empty
 *  let mn : string MN.t = MN.empty
 *  </pre>
 *
 * @author Laurent.Hubert@irisa.fr
 */
public class CamlDictionary extends ADictionary {
  /** current class number. */
  private int fCurrentClass = RESERVED_CLASSES;
  
  /** current package number. */
  private int fCurrentPackage = RESERVED_PACKAGES;

  /**
   * This class is used to implement the Couples and 
   * the Triplets.
   * @author Laurent.Hubert@irisa.fr
   */
  private abstract static class ABaseCouple<T> {
    /** the first element of the couple. */
    final T fI1;
    /** the second element of the couple. */
    final int fI2;

    /**
     * Creates a couple of 2 elements.
     * @param i1 the first element of the couple
     * @param i2 the second element of the couple
     */
    ABaseCouple(final T i1, final int i2) {
      fI1 = i1;
      fI2 = i2;
    }

    /**
     * @return (the_first_element, the_second_element)
     */
    @Override
    public String toString() {
      return "(" + fI1 + "," + fI2 + ")";
    }

    /**
     * Tells if 2 couples are equal.
     * @param obj the object to compare
     * @return true if both object contents are equal
     */
    @SuppressWarnings("unchecked")
    @Override
    public boolean equals(final Object obj) {
      if (this == obj) {
        return true;
      }
      if (obj == null) {
        return false;
      }
      if (obj instanceof ABaseCouple) {
        final ABaseCouple<T> other = (ABaseCouple<T>) obj;
        return ((fI1.equals(other.fI1)) &&
                 (fI2 == other.fI2));
      }
      return false;      
    }
    
    /**
     * Computes the hash code of the object from the 
     * toString method.
     * @return a valid hash code
     */
    @Override
    public int hashCode() {
      return toString().hashCode();
    }
  }
  
  /**
   * This class represents integer couples.
   * @author Laurent.Hubert@irisa.fr
   */
  private static final class ClassType {
    /** the Coq class number. */
    private int fClass;
    
    /** the Coq package number. */
    private int fPkg;

    /**
     * Build a couple of int.
     * @param classNumber the first element of the couple
     * @param pkgNumber the second element of the couple
     */
    ClassType(final int classNumber, final int pkgNumber) {
      fClass = classNumber;
      fPkg = pkgNumber;
    }
    
    /**
     * @return A couple of 2 numbers: <code>(pkg, class)</code>
     */
    @Override
    // FIXME: should use Translator#toZ(int)
    public String toString() {
      return Translator.couple("" + fPkg, "" + fClass);
    }
    
    /**
     * @return the class number
     */
    public int getClassNum() {
      return fClass;
    }
    
    /**
     * @return the package number
     */
    public int getPkgNum() {
      return fPkg;
    }
  } 
  
  /**
   * This class represents integer triplets.
   * @author Laurent.Hubert@irisa.fr
   */
  private static final class Triplet extends ABaseCouple<ClassType> {
    /**
     * Build a triplet.
     * @param ct the class containing the field or the method
     * @param num the number representing in Coq the field or the method
     */
    Triplet(final ClassType ct, final int num) {
      super(ct, num);
    }
    
  }

  /** the package names and their associated numbers. */
  private final Map<String, Integer> fPackageNames = new HashMap<String, Integer>();
  
  /** the class names and their associated numbers (class number and package number). */
  private final Map<String, ClassType> fClassNames = new HashMap<String, ClassType>();
  
  /** the field names and their associated numbers (class, package and field numbers). */
  private final Map<String, Triplet> fFieldNames = new HashMap<String, Triplet>();
  
  /** the method names and their associated numbers (class, package and method numbers). */
  private final Map<String, Triplet> fMethodNames = new HashMap<String, Triplet>();


  /** {@inheritDoc} */
  @Override
  public void addClass(final JavaClass jc, 
                       final int coqClassName) {
    addClass(jc.getClassName(), fPackageNames.get(jc.getPackageName()), coqClassName);
  }
  
  /**
   * Generic way to add a class to the dictionnary, out of one strings and 2 integers.
   * @param javaName the name of the class to add
   * @param packageName the package number
   * @param coqClassName the class number
   */
  private void addClass(final String javaName, final int packageName, 
                       final int coqClassName) {
    if (coqClassName > fCurrentClass) {
      fCurrentClass = coqClassName;
    }
    fClassNames.put(javaName, new ClassType(coqClassName, packageName));
  }
  
  /** {@inheritDoc} */
  @Override
  public void addClass(final JavaClass jc) {
    if (getCoqClassName(jc) == 0) {
      fCurrentClass++;
      addClass(jc.getClassName(), getCoqPackageName(jc), fCurrentClass);  
    }
  }
  
  /**
   * @return the last number that was attributed to a class.
   */
  public int getCurrentClass() {
    return fCurrentClass;
  }

  
  /** {@inheritDoc} */
  @Override
  public int getCoqClassName(final JavaClass jc) {
    final ClassType c = fClassNames.get(jc.getClassName());
    if (c == null) {
      return 0;
    }
    else {
      return c.getClassNum();
    }
  }

  /** {@inheritDoc} */
  @Override
  public int getCoqPackageName(final JavaClass jc) {
    if (fPackageNames == null) {
      throw new NullPointerException();
    }
    if (jc == null) {
      throw new NullPointerException();
    }
    int packageName = 0; // fPackageNames.get(jc.getPackageName());
    if (packageName == 0) {
      packageName = fCurrentPackage++;
      addPackage(jc.getPackageName(), packageName);
    }
    return packageName;
  }
  
  /** {@inheritDoc} */
  @Override
  public void addField(final String javaName, final int coqPackageName, 
                       final int coqClassName,
                       final int coqFieldName) {
    fFieldNames.put(javaName,
           new Triplet(new ClassType(coqClassName, coqPackageName), coqFieldName));
  }

  /** {@inheritDoc} */
  @Override
  public void addMethod(final String javaName, final int coqPackageName,
                        final int coqClassName, final int coqMethodName) {
    if (this.getClassName(coqClassName) == null) {
      throw new IllegalArgumentException("Unknown class: " + coqClassName + "\n" + 
                                         fClassNames);
    }
    fMethodNames.put(javaName, new Triplet(new ClassType(coqClassName, coqPackageName),
                                 coqMethodName));
  }
  
  /** {@inheritDoc} */
  @Override
  public void addPackage(final String javaName, final int coqPackageName) {
    fPackageNames.put(javaName, coqPackageName);
  }


  /**
   * Dump the caml dictionnary to the given stream.
   * @param out the stream to dump to
   */
  public void write(final PrintStream out) {
    out.print("include TranslatorDef\n\n");

    for (Map.Entry<String, Integer> e: fPackageNames.entrySet()) {
      out.print("let pn= DicoPN.add " + e.getValue() + " \"" + 
                e.getKey().replaceAll("\"", "\\\"") + "\" pn\n");
    }

    for (Map.Entry<String, ClassType> e: fClassNames.entrySet()) {
      out.print("let cn= DicoCN.add " + e.getValue() + " \"" + 
                e.getKey().replaceAll("\"", "\\\"") + "\" cn\n");
    }

    for (Map.Entry<String, Triplet> e: fFieldNames.entrySet()) {
      out.print("let fn= DicoFN.add " + e.getValue() + " \"" + 
                e.getKey().replaceAll("\"", "\\\"") + "\" fn\n");
    }

    for (Map.Entry<String, Triplet> e: fMethodNames.entrySet()) {
      out.print("let mn= DicoMN.add (" + e.getValue() + ") \"" + 
                e.getKey().replaceAll("\"", "\\\"") + "\" mn\n");
    }
  }

  /** {@inheritDoc} */
  @Override
  public Collection<Integer> getMethods() {
    final Collection<Integer> coll = new ArrayList<Integer>();
    for (Entry<String, Triplet> entry: fMethodNames.entrySet()) {
      coll.add(entry.getValue().fI2);
    }
    return coll;
  }
  
  /** {@inheritDoc} */
  @Override
  public String getClassName(final int coqName) {
    for (Map.Entry<String, ClassType> entry: fClassNames.entrySet()) {
      if (entry.getValue().getClassNum() == coqName) {
        return entry.getKey();
      }
    }
    throw new IllegalArgumentException("Key not found: " + coqName + "\n" + 
                                       fClassNames);
  }
  
  /** {@inheritDoc} */
  @Override
  public String getMethodName(final int coqName) {
    for (Map.Entry<String, Triplet> entry: fMethodNames.entrySet()) {
      if (entry.getValue().fI2 == coqName) {
        return entry.getKey();
      }
    }
    return null;
  }

  /** {@inheritDoc} */
  @Override
  public String getPackageName(final int coqName) {
    for (Map.Entry<String, Integer> entry: fPackageNames.entrySet()) {
      if (entry.getValue().intValue() == coqName) {
        return entry.getKey();
      }
    }
    return null;
  }

  /** {@inheritDoc} */
  @Override
  public int getClassFromMethod(final int meth) {
    for (Map.Entry<String, Triplet> entry: fMethodNames.entrySet()) {
      if (entry.getValue().fI2 == meth) {
        return entry.getValue().fI1.getClassNum();
      }
    }
    return 0;
  }

  /** {@inheritDoc} */
  @Override
  public int getPackageFromClass(final int clzz) {
    for (Map.Entry<String, ClassType> entry: fClassNames.entrySet()) {
      if (entry.getValue().getClassNum() == clzz) {
        return entry.getValue().getPkgNum();
      }
    }
    return 0;
  }



}


