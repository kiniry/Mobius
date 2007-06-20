package bico;

import java.io.Writer;

import java.util.HashMap;
import java.util.Map;
import java.util.Iterator;

/**
 * @author Laurent.Hubert@irisa.fr
 * 
 */
public class CamlDictionary implements Dictionary {
  private class Singleton {
    int i;

    Singleton(int i) {
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
    public boolean equals(Object obj) {
      if (this == obj)
        return true;
      if (obj == null)
        return false;
      if (getClass() != obj.getClass())
        return false;
      final Couple other = (Couple) obj;
      if (i1 != other.i1)
        return false;
      if (i2 != other.i2)
        return false;
      return true;
    }
  }

  private class Triplet {
    int i1, i2, i3;

    Triplet(int i1, int i2, int i3) {
      this.i1 = i1;
      this.i2 = i2;
      this.i3 = i3;
    }

    @Override
    public String toString() {
      return "((" + i1 + "," + i2 + ")," + i3 + ")";
    }

    @Override
    public boolean equals(Object obj) {
      if (this == obj)
        return true;
      if (obj == null)
        return false;
      if (getClass() != obj.getClass())
        return false;
      final Triplet other = (Triplet) obj;
      if (i1 != other.i1)
        return false;
      if (i2 != other.i2)
        return false;
      if (i3 != other.i3)
        return false;
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
  public void addClass(String javaName, int coqPackageName, int coqClassName) {
    cn.put(javaName, new Couple(coqPackageName, coqClassName));
  }

  /*
   * (non-Javadoc)
   * 
   * @see bico.Dictionary#addField(java.lang.String, int, int, int)
   */
  public void addField(String javaName, int coqPackageName, int coqClassName,
                       int coqFieldName) {
    fn.put(javaName,
           new Triplet(coqPackageName, coqClassName, coqFieldName));
  }

  /*
   * (non-Javadoc)
   * 
   * @see bico.Dictionary#addMethod(java.lang.String, int, int, int)
   */
  public void addMethod(String javaName, int coqPackageName,
                        int coqClassName, int coqMethodName) {
    mn.put(javaName, new Triplet(coqPackageName, coqClassName,
                                 coqMethodName));
  }

  /*
   * (non-Javadoc)
   * 
   * @see bico.Dictionary#addPackage(java.lang.String, int)
   */
  public void addPackage(String javaName, int coqPackageName) {
    pn.put(javaName, new Singleton(coqPackageName));
  }

  /*
   * (non-Javadoc)
   * 
   * @see bico.Dictionary#getCoqPackageName(java.lang.String)
   */
  public int getCoqPackageName(String javaName) {
    Singleton s = pn.get(javaName);
    if (s != null)
      return s.i;
    return 0;
  }

  public void write(Writer out) throws java.io.IOException {
    out.write("include TranslatorDef\n\n");

    Iterator<Map.Entry<String, Singleton>> itpn = pn.entrySet().iterator();
    while (itpn.hasNext()) {
      Map.Entry<String, Singleton> e = itpn.next();
      out.write("let pn= DicoPN.add " + e.getValue() + " \""
                + e.getKey().replaceAll("\"", "\\\"") + "\" pn\n");
    }

    Iterator<Map.Entry<String, Couple>> itcn = cn.entrySet().iterator();
    while (itcn.hasNext()) {
      Map.Entry<String, Couple> e = itcn.next();
      out.write("let cn= DicoCN.add " + e.getValue() + " \""
                + e.getKey().replaceAll("\"", "\\\"") + "\" cn\n");
    }

    Iterator<Map.Entry<String, Triplet>> itfn = fn.entrySet().iterator();
    while (itfn.hasNext()) {
      Map.Entry<String, Triplet> e = itfn.next();
      out.write("let fn= DicoFN.add " + e.getValue() + " \""
                + e.getKey().replaceAll("\"", "\\\"") + "\" fn\n");
    }

    Iterator<Map.Entry<String, Triplet>> itmn = mn.entrySet().iterator();
    while (itmn.hasNext()) {
      Map.Entry<String, Triplet> e = itmn.next();
      out.write("let mn= DicoMN.add (" + e.getValue() + ") \""
                + e.getKey().replaceAll("\"", "\\\"") + "\" mn\n");
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