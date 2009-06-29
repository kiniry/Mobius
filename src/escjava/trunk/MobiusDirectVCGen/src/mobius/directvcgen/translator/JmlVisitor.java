package mobius.directvcgen.translator;

import java.util.Iterator;
import java.util.List;
import java.util.Vector;

import javafe.ast.ArrayRefExpr;
import javafe.ast.BlockStmt;
import javafe.ast.ClassDecl;
import javafe.ast.ConstructorDecl;
import javafe.ast.FieldAccess;
import javafe.ast.Identifier;
import javafe.ast.LiteralExpr;
import javafe.ast.LocalVarDecl;
import javafe.ast.MethodDecl;
import javafe.ast.NewInstanceExpr;
import javafe.ast.RoutineDecl;
import javafe.ast.SkipStmt;
import javafe.ast.Stmt;
import javafe.ast.VarDeclStmt;
import javafe.ast.VariableAccess;
import javafe.util.Location;
import mobius.directVCGen.formula.Expression;
import mobius.directVCGen.formula.Heap;
import mobius.directVCGen.formula.Logic;
import mobius.directVCGen.formula.Lookup;
import mobius.directVCGen.formula.Ref;
import mobius.directVCGen.formula.Type;
import mobius.directVCGen.formula.Util;
import mobius.directVCGen.formula.annotation.AAnnotation;
import mobius.directVCGen.formula.annotation.AnnotationDecoration;
import mobius.directVCGen.formula.annotation.Assume;
import mobius.directVCGen.formula.annotation.Cut;
import mobius.directVCGen.formula.annotation.Set;
import mobius.directvcgen.translator.struct.ContextProperties;
import mobius.directvcgen.translator.struct.GlobalProperties;
import mobius.directvcgen.translator.struct.MethodProperties;
import escjava.ast.CondExprModifierPragma;
import escjava.ast.EverythingExpr;
import escjava.ast.ExprDeclPragma;
import escjava.ast.ExprModifierPragma;
import escjava.ast.ExprStmtPragma;
import escjava.ast.GCExpr;
import escjava.ast.ImportPragma;
import escjava.ast.ModifiesGroupPragma;
import escjava.ast.NothingExpr;
import escjava.ast.SetStmtPragma;
import escjava.ast.TagConstants;
import escjava.ast.TypeExpr;
import escjava.ast.VarExprModifierPragma;
import escjava.sortedProver.Lifter.QuantVariable;
import escjava.sortedProver.Lifter.QuantVariableRef;
import escjava.sortedProver.Lifter.Term;
import escjava.tc.Types;


/**
 * @author Claudia Brauchli (claudia@vis.ethz.ch)
 * @author Hermann Lehner (hermann.lehner@inf.ethz.ch)
 */
class JmlVisitor extends BasicJMLTranslator {
  /** global properties of a class. */
  final GlobalProperties fGlobal = new GlobalProperties();
  
  /** the visitor that translates the JML formulas properly. */
  private JMLTransVisitor fTranslator;
  
  /** the subset checking option. */
  private boolean fDoSubsetChecking;
  
  /**
   * Visitor that translates JML Constructs to FOL by using JmlExprToFormula to
   * translate expressions.
   */
  public JmlVisitor() {
    this(false, null);
     
  }

  /**
   * Visitor that translates JML Constructs to FOL by using JmlExprToFormula to
   * translate expressions.
   * @param doSubsetChecking if the subset checking has to be done
   */
  public JmlVisitor(final boolean doSubsetChecking) {
    this(doSubsetChecking, 
         new JMLTransVisitor(doSubsetChecking));

    fTranslator = new JMLTransVisitor(fDoSubsetChecking);
     
  }

  /**
   * Create a new JML visitor.
   * @param doSubsetChecking if the subset check have to be done
   * @param trans the jml translator to use
   */
  protected JmlVisitor(final boolean doSubsetChecking, 
                    final JMLTransVisitor trans) {
    fDoSubsetChecking = doSubsetChecking;
    fTranslator = trans;
  }

  /**
   * Inspect a class and go recursively through its methods.
   * @param x the class to inspect
   * @param o ignored
   * @return should be ignored
   */
  @Override
  public final Object visitClassDecl(final /*@non_null*/ ClassDecl x, 
                                     final Object o) {
    fGlobal.setClassId(x.id);
    
    //Use default properties to start with.
    return visitTypeDecl(x, new ContextProperties());
  }

  /**
   * Computes the annotations of a routine.
   * @param x a routine
   * @param o must be of type MethodProperties
   * @return the method properties
   */
  @Override
  public final Object visitRoutineDecl(final /*@non_null*/ RoutineDecl x, 
                                       final Object o) {
    final MethodProperties prop = (MethodProperties) o;
    fGlobal.addVisibleTypes(VisibleTypeCollector.getBCELVisibleTypeSet(x));
    prop.setRoutineBegin(true); 
    prop.setModifiesNothing(false);
    
    final boolean hasPost = Util.hasPost(x);
    // If method is not decorated with any postcondition, 
    // we add a dummy postcondition node "//@ ensures true;"
    if (!hasPost) {
      final LiteralExpr litEx = LiteralExpr.make(TagConstants.BOOLEANLIT, Boolean.TRUE, 0);
      final ExprModifierPragma postc = 
        ExprModifierPragma.make(TagConstants.ENSURES, 
                                litEx, Location.NULL);
      if (x.pmodifiers != null) {
        x.pmodifiers.addElement(postc);
      }
    }
    
    // FIXME: if body equals null it tends to bug
    visitASTNode(x, prop);
    
    doAssignable(prop);
    
    if (!prop.isHelper()) {
      // if the method is not a helper the invariants have to
      // be checked
      addInvPredToPreconditions(prop);
      addInvPredToPostconditions(prop);  
    }  
    return prop;
  }


  /**
   * Inspects a method.
   * @param x the method to inspect
   * @param o ignored
   * @return the properties of the method
   */
  @Override
  public final Object visitMethodDecl(final /*@non_null*/ MethodDecl x, final Object o) {
    final MethodProperties prop = new MethodProperties(x);
    prop.fResult =  Expression.rvar(Expression.getResultVar(x));
    
    visitRoutineDecl(x, prop);
    
    if (!prop.isHelper()) {
      final Term constraints = LookupJavaFe.getInst().getConstraint(x.getParent());
      LookupJavaFe.getInst().addNormalPostcondition(prop, constraints);
      Lookup.getInst().addExceptionalPostcondition(prop.getBCELDecl(), constraints);
    }  
    return prop;
  }

  /**
   * Inspects a constructor.
   * @param x the method to inspect
   * @param o ignored
   * @return the properties of the method
   */
  @Override
  public final Object visitConstructorDecl(final /*@non_null*/ ConstructorDecl x, 
                                           final Object o) {
    final MethodProperties prop = new MethodProperties(x);
    prop.fResult =  null;
    visitRoutineDecl(x, prop);
    
    if (!prop.isHelper()) {
      Term initially = prop.getInitiallyFOL();
      if (initially == null) {
        initially = Logic.trueValue();
        // TODO: quick fix, double check it
      }
      LookupJavaFe.getInst().addNormalPostcondition(prop, initially);
      Lookup.getInst().addExceptionalPostcondition(prop.getBCELDecl(), initially);
    } 
    return prop;
  }



  @Override
  public Object visitLocalVarDecl(final /*@non_null*/ LocalVarDecl x, final Object o) {
    final MethodProperties prop = (MethodProperties) o;
    if (prop.isQuantifier()) {
      final QuantVariable qvar = Expression.var(x);
      prop.addQuantVars(qvar);
    }   
    return null;
  }


  @Override
  public /*@non_null*/ Object visitArrayRefExpr(final /*@non_null*/ ArrayRefExpr x, 
                                                final Object o) {
    final Term var = (Term) x.array.accept(this, o); 
    final Term idx = (Term) x.index.accept(this, o);
    
    return Heap.selectArray(Heap.var, var, idx, Type.getSort(x));
  }
  

  @Override
  public final Object visitCondExprModifierPragma(
                                  final /*@non_null*/ CondExprModifierPragma x, 
                                  final Object o) {
    final MethodProperties prop = ((MethodProperties) o);
    final int tag = x.getTag();
    if (tag == TagConstants.ASSIGNABLE || 
        tag == TagConstants.MODIFIABLE ||
        tag == TagConstants.MODIFIES) {
      if (x.expr instanceof FieldAccess) {
        
        final FieldAccess var = (FieldAccess) x.expr;
        final Term targetVar = (Term) var.od.accept(this, o);
        final QuantVariableRef fieldVar = Expression.rvar(var.decl);
        final Term[] qvars = {targetVar, fieldVar};
        prop.getAssignableSet().add(qvars);   
      } 
      else if (x.expr instanceof NothingExpr) {
        prop.setModifiesNothing(true);
      }
    }
    
    return visitASTNode(x, o);
  }
 
  /** {@inheritDoc} */  
  @Override
  public final Object visitEverythingExpr(final /*@non_null*/ EverythingExpr x, 
                                          final Object o) {
    return visitASTNode(x, o);
  }


  @Override
  public Object visitExprDeclPragma(final /*@non_null*/ ExprDeclPragma x, final Object o) {
    
    return x.accept(fTranslator, o);
  }
  
  
  /**
   * @param x constraint node containing the parents class declaration
   * @param t translated term to conjoin the class constraints
   * @param o object containing some context information
   */
  public void constrToConstraints(final ExprDeclPragma x, 
                                  final Term t, 
                                  final ContextProperties o) {
    boolean constIsValid = true;
    Term constTerm = t;
    
    final Term allConst = LookupJavaFe.getInst().getConstraint(x.parent);
    
    if (fDoSubsetChecking) { 
      constIsValid = doSubsetChecking(o);
    }
    
    if (constIsValid) {
      constTerm = Logic.Safe.and(allConst, constTerm); 
      LookupJavaFe.getInst().addConstraint(x.parent, constTerm); 
    }
    else {
      System.out.println("Constraint error (subset check)! " +
          "The following term was not conjoined to " +
          "the overall type constraints: " + t.toString() + "\n");
    }
  }
  


  @Override
  public Object visitExprModifierPragma(final /*@non_null*/ ExprModifierPragma x, 
                                        final Object o) {
    x.accept(fTranslator, o);
    return null;
  }


  @Override
  public Object visitVarExprModifierPragma(final /*@non_null*/ VarExprModifierPragma x, 
                                           final Object o) {
    x.accept(fTranslator, o);
    return null;
  }

  /**
   * Save values of all arguments as ghost variables. 
   * Now we also have the argument's value of the pre-state, 
   * not only of post-state.
   * @param annos Vector of AAnotations, here Annotations = Assignments
   * @param o Properties Object holding routines declaration
   * @deprecated
   */
  // FIXME: I think this function is totally wrong
  // since old are computed by the wp.
  public void argsToGhost(final List<AAnnotation> annos, 
                          final Object o) {  
    ///final RoutineDecl m = ((MethodProperties) o).getDecl();
    
//    for (final FormalParaDecl p: m.args.toArray()) {
//      final Term t1 = Expression.rvar(p);
//      final Term t2 = Expression.old(p);
//      final Set.Assignment assignment = new Set.Assignment((QuantVariableRef) t2, t1);
//      annos.add(new Set((QuantVariableRef) t2, assignment)); 
//    }
  }
  
  /**
   * Get the annotation for the given statement.
   * @param x BlockStmt holding all statements of one entire block
   * @param annos Collection of statement pragmas as annotations
   * @param prop Object as Properties object
   */
  public void handleStmt(final BlockStmt x, 
                         final List<AAnnotation> annos, 
                         final MethodProperties prop) {
    Term inv = null;
    for (final Stmt s: x.stmts.toArray()) {
      if ((((s instanceof VarDeclStmt)) &&
            Util.isGhostVar(((VarDeclStmt) s).decl)) || 
          (s instanceof SetStmtPragma) ||
          (s instanceof ExprStmtPragma)) {
        inv = treatPragma(annos, prop, inv, s);
        x.stmts.removeElement(s);
      } 
      else { // Put annotations to next Java Stmt
        if (!annos.isEmpty()) {
          AnnotationDecoration.inst.setAnnotPre(prop.getBCELDecl(), s, annos);
          annos.clear();
        }
        if (inv != null) { // Add inv as invariant to next Loop Stmt
          if (Util.isLoop(s)) {
            AnnotationDecoration.inst.setInvariant(prop.getBCELDecl(), s, inv, prop); 
            inv = null;
          }
        }
        else {
          s.accept(this, prop);
        }
      }
    }
  }



  private Term treatPragma(final List<AAnnotation> annos, 
                           final MethodProperties prop, 
                           final Term oldInv, final Stmt s) {
    Term inv = oldInv;
    if (s instanceof ExprStmtPragma) { //Asserts, Assumes and Loop Invariants
      if (Util.isInvariant((ExprStmtPragma)s)) {
        inv = treatInvariant((ExprStmtPragma)s, inv, prop);
      }
      else {
        annos.add(treatPragma((ExprStmtPragma)s, prop));
      } 
    }
    else if (s instanceof SetStmtPragma) {
      final Set newSet = treatSetStmt(annos, prop, s);
      annos.add(newSet);
    }
    else if (s instanceof VarDeclStmt) { // Ghost var declarations
      final VarDeclStmt varDecl = (VarDeclStmt) s;
      if (Util.isGhostVar(varDecl.decl)) {
        annos.add(treatGhostDecl(varDecl, prop));
      }
    }
    return inv;
  }

  private AAnnotation treatGhostDecl(final VarDeclStmt s, final MethodProperties prop) {
    return (Set) s.accept(fTranslator, prop);
  }

  private AAnnotation treatPragma(final ExprStmtPragma s, final MethodProperties prop) {
    final Term t = (Term)s.accept(fTranslator, prop);
    switch (s.getTag()) {
      case javafe.parser.TagConstants.ASSERT:
        return new Cut("assert" + prop.getAssertNumber(), 
                       Util.buildArgs(prop), t);
      case TagConstants.ASSUME:
        return new Assume("assume" + prop.getAssertNumber(), 
                          Util.buildArgs(prop), t);
      default:
        break;
    }
    return null;
  }

  private Term treatInvariant(final ExprStmtPragma s,
                              final Term oldInv,
                              final MethodProperties prop) {
    Term inv = oldInv;
    final Term t = (Term) s.accept(fTranslator, prop);
    if (inv != null) {
      inv = Logic.and(inv, t);
    }
    else {
      inv = t;
    }
    return inv;
  }



  private Set treatSetStmt(final List<AAnnotation> annos, 
                           final MethodProperties prop, final Stmt s) {
    final Set.Assignment assignment = 
      (Set.Assignment)s.accept(fTranslator, prop);
    
    QuantVariableRef decl = null;

    for (final AAnnotation annot: annos) {
      if (annot instanceof Set) {
        final Set existingSet = (Set) annot;
        if (existingSet.getDeclaration().equals(assignment.getVar())) {
          annos.remove(existingSet);
          decl = existingSet.getDeclaration();
          break;
        }
      }
    }
    final Set newSet = new Set(decl, assignment);
    return newSet;
  }


  
  @Override
  public final Object visitBlockStmt(final /*@non_null*/ BlockStmt x, final Object o) {
    final List<AAnnotation> annos = new Vector<AAnnotation>();
   
    final MethodProperties prop = (MethodProperties) o;
    prop.fLocalVars.addLast(new Vector<QuantVariableRef>());
    //Save argument's values in prestate as ghosts at beginning of each routine (in annos)
    if (prop.isRoutineBegin()) {
      prop.setRoutineBegin(false);
      argsToGhost(annos, prop);
    }

    handleStmt(x, annos, prop);
    
    // If there is no more Stmt, we generate a dummy SkipStmt 
    // to add last Stmt Pragma as precondition
    if (!annos.isEmpty()) { 
      final SkipStmt skipStmt = SkipStmt.make(0); //FIXME cbr: which location?
      AnnotationDecoration.inst.setAnnotPre(prop.getBCELDecl(), skipStmt, annos);
      x.stmts.addElement(skipStmt);
    }
    prop.fLocalVars.removeLast();
    return null;
  }

  /** {@inheritDoc} */
  @Override
  public Object visitVarDeclStmt(final /*@non_null*/ VarDeclStmt x, final Object o) {
    final MethodProperties prop = (MethodProperties) o;
    prop.fLocalVars.getLast().add(Expression.rvar(x.decl));

    return prop;
  }

  /** {@inheritDoc} */
  @Override
  public final Object visitExprStmtPragma(final /*@non_null*/ ExprStmtPragma x, 
                                          final Object o) {
    return visitASTNode(x, o);
  }

  /** {@inheritDoc} */
  @Override
  public final Object visitGCExpr(final /*@non_null*/ GCExpr x, final Object o) {
    if (x instanceof TypeExpr) { 
      final String name = Types.printName(((TypeExpr)x).type);
      return Expression.rvar(name, Type.sort);
    }
    return visitASTNode(x, o);
  }


  /** {@inheritDoc} */
  @Override
  public final Object visitImportPragma(final /*@non_null*/ ImportPragma x, final Object o) {
    return visitASTNode(x, o);
  }

  /** {@inheritDoc} */
  @Override
  public final Object visitModifiesGroupPragma(final /*@non_null*/ ModifiesGroupPragma x, 
                                               final Object o) {
    return visitASTNode(x, o);
  }

  /** {@inheritDoc} */
  @Override
  public final Object visitSetStmtPragma(final /*@non_null*/ SetStmtPragma x, 
                                         final Object o) {
    
    if (x.target instanceof VariableAccess) {
      return new Set.Assignment((QuantVariableRef) x.target.accept(this, o),
                         (Term) x.value.accept(this, o));
    }
    return new Set.Assignment(null, null);
  }


  // FIXME: totally wrong
  /** {@inheritDoc} */
  @Override
  public /*@non_null*/ Object visitNewInstanceExpr(final /*@non_null*/ NewInstanceExpr x, 
                                                   final Object o) {
//    final String name = Types.printName(x.type);
//    return Expression.rvar(name, Type.typeToSort(x.type)); // Ref.sort);
    return Expression.rvar(Ref.sort);
  }
  

  /**
   * Adds the class invariants and the invariants predicates
   * to the precondition.
   * @param o Properties object also containing all modifiable types.
   */
  public void addInvPredToPreconditions(final /*@non_null*/ Object o) {
    final MethodProperties prop = (MethodProperties) o;
    final QuantVariableRef x = Expression.rvar(Ref.sort);
    final QuantVariableRef type = Expression.rvar(Type.sort);
    final QuantVariable[] vars = {x.qvar, type.qvar};
    final Term invTerm = Logic.inv(Heap.var, x, type);
    final Term typeOfTerm = Logic.assignCompat(Heap.var, x, type);
    final Term allocTerm = Logic.isAlive(Heap.var, x);
    Term andTerm = Logic.and(allocTerm, typeOfTerm);
    if (prop.isConstructor()) {
      final Term notEQThis = Logic.not(Logic.equals(x, Ref.varThis));
      andTerm = Logic.and(andTerm, notEQThis);
    }    
    final Term implTerm = Logic.implies(andTerm, invTerm);
    final Term forAllTerm = Logic.forall(vars, implTerm);
    Lookup.getInst().addPrecondition(prop.getBCELDecl(), forAllTerm);
  }


  
  /**
   * Adds the class invariants and the invariants predicates
   * to the poscondition and the exceptionnal post.
   * @param prop the targeted method
   */
  public void addInvPredToPostconditions(final /*@non_null*/ MethodProperties prop) { 
    LookupJavaFe.getInst().addNormalPostcondition(prop, Logic.invPostPred(fGlobal.getVisibleTypes()));
    Lookup.getInst().addExceptionalPostcondition(prop.getBCELDecl(), Logic.invPostPred(fGlobal.getVisibleTypes()));
  }

  
  /**
   * @param prop containing all field access of the invariant and the class id
   * @return boolean value whether the subset checking of the invariant fields was successfull 
   */
  public boolean doSubsetChecking(final ContextProperties prop) {
    final Identifier parentId = fGlobal.getClassId();    
    boolean result = true;
    
    for (FieldAccess fa: fGlobal.getSubsetCheckingSet()) {
      final Identifier typeId = fa.decl.parent.id;
      if (!parentId.equals(typeId)) {
        System.out.println("Subset checking: failed! " +
            "The field \"" + fa.id + 
            "\" is a field of class " + typeId + 
            " and not as expected of class " + parentId + "!");  
        result = false;
      }
    }

    fGlobal.clearSubsetCheckingSet();
    return result;
  }
  
  /**
   * Adds a Term to the routines postcondition describing 
   * all assignable variables.
   * @param o Properties object also containing all assignable variables
   */
  public void doAssignable(final Object o) {
    final MethodProperties prop = (MethodProperties) o;
    if (prop.isModifiesNothing() || !prop.getAssignableSet().isEmpty()) {
      final QuantVariableRef target = Expression.rvar(Ref.sort);
      final QuantVariableRef field = Expression.rvar(Type.sortField);
      final QuantVariable[] vars = {target.qvar, field.qvar};
      Term t;
      if (!prop.getAssignableSet().isEmpty()) {
        t = Logic.or(JmlVisitor.isAssignable(target, field, prop), 
                          Logic.assignablePred(Heap.var, Heap.varPre, target, field));
      } 
      else {
        t = Logic.assignablePred(Heap.var, Heap.varPre, target, field);
      }
      
      final Term forAllTerm = Logic.forall(vars, t);
      LookupJavaFe.getInst().addNormalPostcondition(prop, forAllTerm);
      Lookup.getInst().addExceptionalPostcondition(prop.getBCELDecl(), forAllTerm);
    } 
  }
 

  /**
   * @param x invariant node containing the parents class declaration
   * @param t translated term to conjoin the class invariants
   * @param prop object containing some context informations
   */
  public void addToInv(final ExprDeclPragma x, final Term t,
                       final ContextProperties prop) {
    if (t != null) {
      boolean invIsValid = true;
      Term invTerm = t;
      final Term allInvs = LookupJavaFe.getInst().getInvariant(x.parent);
      
      if (fDoSubsetChecking) { 
        invIsValid = doSubsetChecking(prop);
      }
      if (invIsValid && allInvs != null) {
        invTerm = Logic.and(allInvs, invTerm); 
      }
      else if (invIsValid) {
        LookupJavaFe.getInst().addInvariant(x.parent, invTerm); 
      }
      else if (!invIsValid) {
        System.out.println("Invariant error (subset check)! " +
            "The following term was not conjoined to the overall type " +
            "invariant: " + t.toString() + "\n");
      }
    }
   
  }

  /**
   * Tells whether or not the subset checking have to be done.
   * @return true if the visitor does subset checkings
   */
  public boolean getDoSubsetChecking() {
    return fDoSubsetChecking;
  }

  /**
   * @param t the object containing the fieldVar
   * @param f the field for which we want to find out whether it's assignable or not
   * @param prop Parameter object also containing a list of modifiable types.
   * @return A Term expressing the check described above.
   */
  public static Term isAssignable(final QuantVariableRef t, 
                                  final QuantVariableRef f, final MethodProperties prop) {
    Term t1 = null;
    Term t2 = null;
    final java.util.Set<Term[]> assignSet = prop.getAssignableSet();
    final Iterator iter = assignSet.iterator();
    
    while (iter.hasNext()) {
      final QuantVariableRef[] setVar = (QuantVariableRef[]) iter.next();
      t1 = Logic.equals(Heap.loc(Heap.var, t, f.qvar), 
                        Heap.loc(Heap.var, setVar[0], setVar[1].qvar));
      if (t2 == null) {
        t2 = t1;
      }
      else {
        t2 = Logic.or(t2, t1);
      }
    }
    return t2;
  }
  
  

}
