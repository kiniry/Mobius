package mobius.directvcgen.translator.struct;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import javafe.ast.ConstructorDecl;
import javafe.ast.RoutineDecl;
import mobius.directvcgen.formula.ILocalVars;
import mobius.directvcgen.formula.Lookup;
import mobius.directvcgen.formula.Translator;
import mobius.directvcgen.formula.Util;

import org.apache.bcel.generic.MethodGen;

import escjava.sortedProver.Lifter.QuantVariable;
import escjava.sortedProver.Lifter.QuantVariableRef;
import escjava.sortedProver.Lifter.Term;

/**
 * Properties that are passed as argument of the visitor. 
 * @author Hernann Lehner and J. Charles (julien.charles@inria.fr)
 */
public final class MethodProperties extends ContextProperties implements ILocalVars {

  /** */
  private static final long serialVersionUID = 1L;
  
  
  /** valid properties string. */
  private static final List<String> validStr = 
    new ArrayList<String>();

  /** the current method which is inspected. */
  private final RoutineDecl fMethod;
  
  /** tells whether or not we are inspecting a constructor. */
  private final boolean fIsConstructor;
  
  /** the routine is a JML \helper routine. See JML reference */
  private final boolean fIsHelper;
  
  /** the set of variables that can be assigned in the current method, the first arg being a term the second a quantvarref. */
  private final Set<Term[]> fAssignableSet = new HashSet<Term[]>(); 

  
  /** key to represent a result in the properties set. */  
  public QuantVariableRef fResult;
  
  /** if the flag modifies nothing is set for the method. */
  private boolean fNothing;

  /** the local variables. */
  public LinkedList<List<QuantVariableRef>> fLocalVars = 
      new LinkedList<List<QuantVariableRef>> ();
  
  /** the arguments of the method. */
  private LinkedList<QuantVariableRef> fArgs;

  
  /** the counter to get the assert number, for the naming. */
  private int fAssert;
  

  private boolean fRoutineBegin = true;
  private boolean fQuantifier = false;
  private Set<QuantVariable> fQuantVars = new HashSet<QuantVariable>();

  private Term fInitiallyFOL = null;
  
  /**
   * initialize the properties with default values.
   * @param met the method which is inspected
   */
  public MethodProperties(final RoutineDecl met) {
    
    validStr.addAll(super.getValidStr());
    fMethod = met;
    fArgs = new LinkedList<QuantVariableRef>(); 
    fArgs.addAll(Lookup.getInst().mkArguments(getBCELDecl()));

    fIsConstructor = fMethod instanceof ConstructorDecl;
    fIsHelper = Util.isHelper(met);
    
  
  }

  
  public RoutineDecl getDecl() {
    return fMethod;
  }
  public MethodGen getBCELDecl() {
    return Translator.getInst().translate(fMethod);
  }
  public List<QuantVariableRef> getLocalVars() {
    final List<QuantVariableRef> res = new LinkedList<QuantVariableRef>();
    for (List<QuantVariableRef> list: fLocalVars) {
      res.addAll(list);
    }
    return res;
  }



  public int getAssertNumber() {
    return fAssert++;
  }



  public List<QuantVariableRef> getArgs() {
    return fArgs;
  }



  public QuantVariableRef getResult() {
    return fResult;
  }


  public Set<Term[]> getAssignableSet() {

    return fAssignableSet;
  }



  public void setQuantifier(boolean b) {
    fQuantifier = b;
  }



  public Collection<QuantVariable> getQuantVars() {
    return fQuantVars;
  }



  public void clearQuantVars() {
    fQuantVars.clear();
  }



  public void setInitiallyFOL(Term initiallyFOL) {
    this.fInitiallyFOL = initiallyFOL;
  }



  public Term getInitiallyFOL() {
    return fInitiallyFOL;
  }



  public void addQuantVars(QuantVariable qvar) {
    fQuantVars.add(qvar);
  }



  public boolean isQuantifier() {
    return fQuantifier;
  }



  public void setRoutineBegin(boolean b) {
    fRoutineBegin = b;
  }



  public boolean isRoutineBegin() {
    return fRoutineBegin;
  }



  public boolean isConstructor() {
    return fIsConstructor;
  }



  public boolean isHelper() {
    return fIsHelper;
  }


  public void setModifiesNothing(boolean b) {
    fNothing = b;
  }


  public boolean isModifiesNothing() {
    return fNothing;
  }

}
