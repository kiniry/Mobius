package mobius.bico.dico;

import java.io.PrintStream;
import java.util.HashMap;
import java.util.Map;

import org.apache.bcel.classfile.JavaClass;


/**
 * @author Laurent.Hubert@irisa.fr
 * 
 */
public class CamlDictionary implements Dictionary {
  /** current class number. */
  private int fCurrentClass = RESERVED_CLASSES;

  private class Singleton {
    int i;

    Singleton(final int i) {
      this.i = i;
    }

    @Override
    public String toString() {
      return "" + i;
    }

    @Override
    public boolean equals(final Object obj) {
      if (this == obj) {
        return true;
      }
      if (!super.equals(obj)) {
        return false;
      }
      if (getClass() != obj.getClass()) {
        return false;
      }
      final Singleton other = (Singleton) obj;
      if (i != other.i) {
        return false;
      }
      return true;
    }
  }

  private class Couple {
    int i1, i2;

    Couple(final int i1, final int i2) {
      this.i1 = i1;
      this.i2 = i2;
    }

    @Override
    public String toString() {
      return "(" + i1 + "," + i2 + ")";
    }

    @Override
    public boolean equals(final Object obj) {
      if (this == obj) {
        return true;
      }
      if (obj == null) {
        return false;
      }
      if (!(obj instanceof Couple)) {
        return false;
      }
      final Couple other = (Couple) obj;
      if (i1 != other.i1) {
        return false;
      }
      if (i2 != other.i2) {
        return false;
      }
      return true;
    }
  }

  private class Triplet {
    int i1, i2, i3;

    Triplet(final int i1, final int i2, final int i3) {
      this.i1 = i1;
      this.i2 = i2;
      this.i3 = i3;
    }

    @Override
    public String toString() {
      return "((" + i1 + "," + i2 + ")," + i3 + ")";
    }

    @Override
    public boolean equals(final Object obj) {
      if (this == obj) {
        return true;
      }
      if (obj == null) {
        return false;
      }
      if (getClass() != obj.getClass()) {
        return false;
      }
      final Triplet other = (Triplet) obj;
      if (i1 != other.i1) {
        return false;
      }
      if (i2 != other.i2) {
        return false;
      }
      if (i3 != other.i3) {
        return false;
      }
      return true;
    }
  }

  private Map<String, Singleton> pn = new HashMap<String, Singleton>();
  private Map<String, Couple> cn = new HashMap<String, Couple>();
  private Map<String, Triplet> fn = new HashMap<String, Triplet>();
  private Map<String, Triplet> mn = new HashMap<String, Triplet>();

  /*
   * (non-Javadoc)
   * 
   * @see bico.Dictionary#addClass(java.lang.String, int, int)
   */
  public void addClass(final String javaName, final int coqPackageName, 
                       final int coqClassName) {
    if (coqClassName > fCurrentClass) {
      fCurrentClass = coqClassName;
    }
    cn.put(javaName, new Couple(coqPackageName, coqClassName));
  }
  public void addClass(final JavaClass jc, 
                       final int coqClassName) {
    addClass(jc.getClassName(), getCoqPackageName(jc.getPackageName()), coqClassName);
  }
  public int getCurrentClass() {
    return fCurrentClass;
  }

  public int getCoqClassName(final String javaName) {
    return cn.get(javaName).i2;
  }
  public int getCoqClassName(final JavaClass jc) {
    return getCoqClassName(jc.getClassName());
  }

  public int getCoqPackageName(final JavaClass jc) {
    Couple c = cn.get(jc.getClassName());
    return c.i1;
  }
  /*
   * (non-Javadoc)
   * 
   * @see bico.Dictionary#addField(java.lang.String, int, int, int)
   */
  public void addField(final String javaName, final int coqPackageName, 
                       final int coqClassName,
                       final int coqFieldName) {
    fn.put(javaName,
           new Triplet(coqPackageName, coqClassName, coqFieldName));
  }

  /*
   * (non-Javadoc)
   * 
   * @see bico.Dictionary#addMethod(java.lang.String, int, int, int)
   */
  public void addMethod(final String javaName, final int coqPackageName,
                        final int coqClassName, final int coqMethodName) {
    mn.put(javaName, new Triplet(coqPackageName, coqClassName,
                                 coqMethodName));
  }

  /*
   * (non-Javadoc)
   * 
   * @see bico.Dictionary#addPackage(java.lang.String, int)
   */
  public void addPackage(final String javaName, final int coqPackageName) {
    pn.put(javaName, new Singleton(coqPackageName));
  }

  /*
   * (non-Javadoc)
   * 
   * @see bico.Dictionary#getCoqPackageName(java.lang.String)
   */
  public int getCoqPackageName(final String javaName) {
    final Singleton s = pn.get(javaName);
    if (s != null) {
      return s.i;
    }
    return 0;
  }

  public void write(final PrintStream out) throws java.io.IOException {
    out.print("include TranslatorDef\n\n");

    for (Map.Entry<String, Singleton> e: pn.entrySet()) {
      out.print("let pn= DicoPN.add " + e.getValue() + " \"" + 
                e.getKey().replaceAll("\"", "\\\"") + "\" pn\n");
    }

    for (Map.Entry<String, Couple> e: cn.entrySet()) {
      out.print("let cn= DicoCN.add " + e.getValue() + " \"" + 
                e.getKey().replaceAll("\"", "\\\"") + "\" cn\n");
    }

    for (Map.Entry<String, Triplet> e: fn.entrySet()) {
      out.print("let fn= DicoFN.add " + e.getValue() + " \"" + 
                e.getKey().replaceAll("\"", "\\\"") + "\" fn\n");
    }

    for (Map.Entry<String, Triplet> e: mn.entrySet()) {
      out.print("let mn= DicoMN.add (" + e.getValue() + ") \"" + 
                e.getKey().replaceAll("\"", "\\\"") + "\" mn\n");
    }
  }



}

/* Here is an example of OCaml code that needs to be
 * added to the dictionary to have something usable.
 * (in a file TranslatorDef, it's the file included by
 * the generated file)
 *****************************************************
    module OrderedInt =
  struct
    type t = int
    let compare= Pervasives.compare
  end

  module OrderedPair =
    functor (M1:Map.OrderedType) ->
      functor (M2:Map.OrderedType) ->
  struct
    type t = M1.t * M2.t
    let compare = Pervasives.compare
  end
  module OrderedClassName = OrderedPair(OrderedInt)(OrderedInt)
  module OrderedMethodName = OrderedPair (OrderedClassName) (OrderedInt)
  module OrderedFieldName = OrderedMethodName

  module DicoInt = Map.Make(OrderedInt)
  module DicoPN = DicoInt
  module DicoCN = Map.Make(OrderedClassName)
  module DicoMN = Map.Make(OrderedMethodName)
  module DicoFN = Map.Make(OrderedFieldName)
  module DicoMNPC = Map.Make (OrderedPair (OrderedMethodName) (OrderedInt))
  module DicoType = Map.Make (OrderedPair (OrderedInt) (OrderedClassName))

  module PN = DicoPN
  module CN = DicoCN
  module FN = DicoFN
  module MN = DicoMN
  let pn : string PN.t = PN.empty
  let cn : string CN.t = CN.empty
  let fn : string FN.t = FN.empty
  let mn : string MN.t = MN.empty
 *********************************
 */
