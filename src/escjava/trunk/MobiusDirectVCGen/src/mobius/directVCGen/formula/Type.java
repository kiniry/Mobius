package mobius.directVCGen.formula;

import java.util.HashMap;
import java.util.Vector;

import javafe.ast.MethodDecl;
import javafe.ast.VarInit;
import javafe.tc.FlowInsensitiveChecks;
import escjava.sortedProver.Lifter.FnTerm;
import escjava.sortedProver.Lifter.QuantVariableRef;
import escjava.sortedProver.Lifter.Term;
import escjava.sortedProver.NodeBuilder.Sort;
import escjava.tc.Types;
import escjava.translate.UniqName;

/**
 * This class is made to create terms to use with types.
 * <p>
 * The type <code>javafe.ast.Type</code> should <em>not</em>
 * appear as an import anywhere else but in this  (actually this is not even
 * an import here). If it is the case, it is an architecture error.	
 */
public class Type{
  /** the sort representing a type */
  public static Sort sort = Formula.lf.sortType;
  /** an hash map not to compute twice the types/term correspondance */
  private static final HashMap<javafe.ast.Type, QuantVariableRef> types = new HashMap<javafe.ast.Type, QuantVariableRef>();
  /** a second hashmap to get the orginal type from the given term */
  private static final HashMap<QuantVariableRef, javafe.ast.Type> revtyp = new HashMap<QuantVariableRef, javafe.ast.Type>();
  /** a Set to stock the array types declaration the key is the original type */
  private static final HashMap<QuantVariableRef, Term> arrays = new HashMap<QuantVariableRef, Term>();

  /**
   * The typeof relation. Takes 2 arguments, a heap and a term.
   * @param heap the heap on which interrogate the type of the variable
   * @param var the variable to get the type of
   * @return a newly created term representing a typeof construct
   */
  public static FnTerm of(Term heap, Term var) {
    if(heap.getSort() != Heap.sort)
      throw new IllegalArgumentException("Type of the first param should be heap (" + Heap.sort + "), found: " + heap.getSort());
    if(var.getSort() != Ref.sort)
      throw new IllegalArgumentException("Type of the second param should be ref (" + Ref.sort + "), found: " + var.getSort());

    return Formula.lf.mkFnTerm(Formula.lf.symTypeOf, new Term[] {heap, var});
  }

  /**
   * Translate a type to a term which represents the name of the type.
   * @param type the type to translate
   * @return a term which has the type {@link Type#sort} and which represents
   * the name of the type which is translated
   */
  public static QuantVariableRef translate(javafe.ast.Type type) {
    QuantVariableRef t = types.get(type);
    if(t != null) {
      return t;
    }
    else {
      t = Expression.rvar(UniqName.type(type), Type.sort);
      types.put(type, t);
      revtyp.put(t, type);
      return t;	
    }
  }

  /**
   * Translate a type to a term which is a type in the target
   * representation language.
   * @param type the type to translate
   * @return term which has the type {@link Type#sort} and which represents
   * the type which is translated
   */
  public static Term translateToType(javafe.ast.Type type) {
    QuantVariableRef q = translate(type) ;
    return Expression.rvar("(ReferenceType (ClassType " + q.qvar.name + "))", q.getSort());
  }

  /**
   * Returns the sort of the given expression.
   * @param e the expression to get the sort from
   * @return a valid sort as decided by 
   * {@link escjava.sortedProver.Lifter#typeToSort(javafe.ast.Type)}
   * @see #getTypeName(VarInit)
   * @see #translate(javafe.ast.Type)
   */
  public static Sort getSort(VarInit e) {
    javafe.ast.Type t = FlowInsensitiveChecks.getType(e);
    Sort s = Formula.lf.typeToSort(t);
    return s;
  }


  /**
   * Returns true if we can determine that typ1 is a subtype of typ2.
   * Should be used only with real type terms that were obtained previously
   * by a call to {@link #translate(javafe.ast.Type)} !!!
   * @param typ1 the first type
   * @param typ2 the secont type to compare to the first one
   * @return if one is a subclass or the same as the other
   */
  public static boolean isSubClassOrEq(Term typ1, Term typ2) {
    javafe.ast.Type t1 = revtyp.get(typ1);
    javafe.ast.Type t2 = revtyp.get(typ2);
    if(t1 == null || t2 == null) {
      throw new IllegalArgumentException("One of the argument (" + t1 + " or " + 
                                         t2 +") is an invalid type!");
    }
    return Types.isSubClassOrEq(t1, t2);
  }

  /**
   * Returns the type of an expression. It returns the name of the 
   * type not the sort (eg. used for class names not primitive types).
   * @param expr the expression to get the type from
   * @return a term representing a type
   * @see #getSort(VarInit)
   * @see #translate(javafe.ast.Type)
   */
  public static Term getTypeName(VarInit expr) {
    return translate(FlowInsensitiveChecks.getType(expr)) ;
  }

  /**
   * Return the type of an expression. It is not solely the name of the
   * type it is also surrounded by conversions things.
   * @param expr the expression to get the type of
   * @return a valid type
   * @see #translateToType(javafe.ast.Type)
   */
  public static Term getType(VarInit expr) {
    return translateToType(FlowInsensitiveChecks.getType(expr)) ;
  }
  /**
   * Returns a term representing the class type 
   * {@link java.lang.Throwable}.
   * @see #javaLangArithmeticException()
   * @see #javaLangNullPointerException()
   * @see #getJavaLang(String)
   */
  public static Term javaLangThrowable() {
    return translate(Types.javaLangThrowable());
  }

  /**
   * Returns a term representing the class type 
   * {@link java.lang.ArithmeticException}.
   * @see #javaLangThrowable()
   * @see #javaLangNullPointerException()
   * @see #getJavaLang(String)
   */
  public static Term javaLangArithmeticException() {
    return translate(Types.getJavaLang("ArithmeticException"));
  }

  /**
   * Returns a term representing the class type 
   * {@link java.lang.NullPointerException}.
   * @see #javaLangArithmeticException()
   * @see #javaLangThrowable()
   * @see #getJavaLang(String)
   */
  public static Term javaLangNullPointerException() {
    return translate(Types.getJavaLang("NullPointerException"));
  }

  /**
   * Returns a term representing the specified type.
   * @deprecated used for convenience only
   */
  public static Term getJavaLang(String string) {
    return translate(Types.getJavaLang(string));
  }
  /**
   * @deprecated should not be needed
   */
  public static Sort typeToSort(javafe.ast.Type t) {
    return Formula.lf.typeToSort(t);
  }

  /**
   * Returns a list of all the types that need to be declared (mostly these are
   * the class names).
   * @return A printable version of the types name. It uses the builder to do so.
   */
  public static Vector<String> getAllTypes() {
    Formula.lf.dumpBuilder = Formula.lf.builder;
    Vector<String> v = new Vector<String>();
    for(Term t: revtyp.keySet()) {
      v.add(t.dump().toString());
    }
    Formula.lf.dumpBuilder = null;
    return v;
  }


  /**
   * This construct is to use with multi-arrays. Right now
   * since multi-arrays are not handled it is not used.
   * @deprecated
   */
  public static Term arrayof(Term type) {
    Object t = revtyp.get(type);
    if(t == null) {
      throw new IllegalArgumentException("The argument must be an already registred type found: " + type);
    }
    else {

      QuantVariableRef oldType = (QuantVariableRef) type; 
      if((type = arrays.get(oldType)) != null)
        return type;
      String name = oldType.qvar.name + "_ref"; 
      type = Expression.rvar(name, Type.sort);
      arrays.put(oldType, type);
      return type;	
    }
  }

  /**
   * Returns a term representing the class type 
   * {@link java.lang.ArrayOutOfBoundException}.
   * @see #javaLangThrowable()
   * @see #javaLangNullPointerException()
   * @see #getJavaLang(String) 
   */
  public static Term javaLangArrayOutOfBoundException() {
    return translate(Types.getJavaLang("ArrayOutOfBoundException"));
  }

  /**
   * Returns the return type of a given method.
   * @param x the method to get the retun type
   * @return the sort which is the return type of the method
   */
  public static Sort getReturnType(MethodDecl x) {
    return Formula.lf.typeToSort(x.returnType);
  }




}
