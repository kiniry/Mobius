package mobius.directvcgen.formula.annotation;

import escjava.sortedProver.Lifter.QuantVariableRef;
import escjava.sortedProver.Lifter.Term;

/**
 * An annotation representing a set instruction.
 * 
 * @author H. Lehner and J. Charles (julien.charles@inria.fr)
 */
public class Set extends AAnnotation {

  /** FOL-Terms  containing variable declarations. (Each Term is just a Variable) */
  //TODO: Could maybe be Vector<SortVar> instead
  private final QuantVariableRef fDeclaration;

  /** FOL-Terms translation of JML's set statement. */
  private final Assignment fAssignment;


  /**
   * Build a new set from a variable and its assignment.
   * @param decl the variable to assign
   * @param assign the JML assignment associated to this construct
   */
  public Set(final QuantVariableRef decl, final Assignment assign) {
    fDeclaration = decl;
    fAssignment = assign;
  }
  
  /** {@inheritDoc} */
  @Override
  public int getID() {
    return annotSet;
  }


  /**
   * Inner class that represents a JML assignment (set statement).
   */
  public static class Assignment {
    /** the variable which is being assigned. */
    private final QuantVariableRef fVar;
    /** the expression which is assigned to the variable. */
    private final Term fExpr;

    /**
     * Construct an assignment structure out of a variable and an expression.
     * @param var a variable
     * @param expr an expression
     */
    public Assignment(final QuantVariableRef var, final Term expr) {
      if (var == null || expr == null) {
        throw new IllegalArgumentException("var (" + getVar() + ") " +
                                           "or expr (" + getExpr() + ") " +
                                           "shouldn't be null!");
      }
      fVar = var;
      fExpr = expr;
    }

    /** {@inheritDoc} */
    @Override
    public String toString() {
      return getVar() + " := " + getExpr();
    }

    /**
     * Returns the ghost variable which is being assigned.
     * @return a variable
     */
    public QuantVariableRef getVar() {
      return fVar;
    }

    /**
     * Returns the expression to which the variable is being 
     * assigned.
     * @return an expression
     */
    public Term getExpr() {
      return fExpr;
    }




  }


  /** {@inheritDoc} */
  @Override
  public String toString() {
    return "Declare " + fDeclaration + ", Set " + fAssignment;
  }

  /**
   * Return the assignment of the set instruction.
   * @return an assignment structure
   */
  public  Assignment getAssignment() {
    return fAssignment;
  }

  /**
   * Returns the declaration, the variable name which is set.
   * @return a declaration
   */
  public QuantVariableRef getDeclaration() {
    return fDeclaration;
  }

}
