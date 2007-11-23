package mobius.directVCGen.formula.jmlTranslator;

import java.util.HashSet;
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
import javafe.ast.UnaryExpr;
import javafe.ast.VarDeclStmt;
import javafe.ast.VariableAccess;
import javafe.util.Location;
import mobius.directVCGen.formula.Bool;
import mobius.directVCGen.formula.Expression;
import mobius.directVCGen.formula.Heap;
import mobius.directVCGen.formula.Logic;
import mobius.directVCGen.formula.Lookup;
import mobius.directVCGen.formula.Num;
import mobius.directVCGen.formula.Ref;
import mobius.directVCGen.formula.Type;
import mobius.directVCGen.formula.Util;
import mobius.directVCGen.formula.annotation.AAnnotation;
import mobius.directVCGen.formula.annotation.AnnotationDecoration;
import mobius.directVCGen.formula.annotation.Assume;
import mobius.directVCGen.formula.annotation.Cut;
import mobius.directVCGen.formula.annotation.Set;
import mobius.directVCGen.formula.jmlTranslator.struct.ContextProperties;
import mobius.directVCGen.formula.jmlTranslator.struct.GlobalProperties;
import mobius.directVCGen.formula.jmlTranslator.struct.MethodProperties;
import escjava.ast.CondExprModifierPragma;
import escjava.ast.EverythingExpr;
import escjava.ast.ExprDeclPragma;
import escjava.ast.ExprModifierPragma;
import escjava.ast.ExprStmtPragma;
import escjava.ast.GCExpr;
import escjava.ast.ImportPragma;
import escjava.ast.ModifiesGroupPragma;
import escjava.ast.NothingExpr;
import escjava.ast.ParsedSpecs;
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
 * 
 */
public class JmlVisitor extends BasicJMLTranslator {
  /** global properties of a class. */
  final GlobalProperties fGlobal = new GlobalProperties();
  
  private JMLTransVisitor fTrans;
  
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

    fTrans = new JMLTransVisitor(fDoSubsetChecking);
     
  }



  public JmlVisitor(final boolean doSubsetChecking, 
                    final JMLTransVisitor trans) {
    fDoSubsetChecking = doSubsetChecking;
    fTrans = trans;
  }

  /* (non-Javadoc)
   * @see javafe.ast.VisitorArgResult#visitClassDecl(javafe.ast.ClassDecl, java.lang.Object)
   */
  @Override
  public final Object visitClassDecl(final /*@non_null*/ ClassDecl x, final Object o) {
    fGlobal.setClassId(x.id);
    
    //Use default properties to start with.
    return visitTypeDecl(x, new ContextProperties());
  }

  
  
  
  /**
   * @param x a routine
   * @param o must be of type MethodProperties
   */
  @Override
  public final Object visitRoutineDecl(final /*@non_null*/ RoutineDecl x, 
                                       final Object o) {
    final MethodProperties prop = (MethodProperties) o;
    fGlobal.visibleTypeSet = VisibleTypeCollector.getVisibleTypeSet(x);
    prop.fIsHelper = false;
    prop.put("routinebegin", Boolean.TRUE);
    prop.fNothing = false;
    
    boolean hasPost = false;
    int tag;
    // Check, if method has at least one postcondition/exceptional 
    // postcondition or is a helper method
    if (x.pmodifiers != null) {
      for (int i = 0; i < x.pmodifiers.size(); i++) {
        tag = x.pmodifiers.elementAt(i).getTag();
        if ((tag == TagConstants.ENSURES) | 
            (tag == TagConstants.POSTCONDITION) | 
            (tag == TagConstants.POSTCONDITION_REDUNDANTLY)) {
          hasPost = true;
        }
        else if (x.pmodifiers.elementAt(i).getTag() == TagConstants.HELPER) {
          prop.fIsHelper = true;
        }
      }
    }
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
    
    // Add dummy exceptional postcondition to Lookup hash map   
    //Lookup.exceptionalPostconditions.put(x, new Post(Expression.rvar(Ref.sort), Logic.True())); 
    //prop.put("firstExPost", Boolean.TRUE);
    
    visitASTNode(x, prop);
//    if (x.body != null) {
//      x.body.accept(this, prop);
//    }
    doAssignable(prop);
    
    if (!prop.fIsHelper) {
      invPredToPreconditions(prop);
      invPredToPostconditions(prop);
      invPredToExceptionalPostconditions(prop);    
    }  
    return null;
  }

  
  
  

  /* (non-Javadoc)
   * @see javafe.ast.VisitorArgResult#visitMethodDecl(javafe.ast.MethodDecl, java.lang.Object)
   */
  @Override
  public final Object visitMethodDecl(final /*@non_null*/ MethodDecl x, final Object o) {
    final MethodProperties prop = new MethodProperties(x);
    prop.fResult =  Expression.rvar(Expression.getResultVar(x));
    
    visitRoutineDecl(x, prop);
    
    if (!prop.fIsHelper) {
      final Term constraints = Lookup.getConstraint(x.getParent());
      Lookup.addNormalPostcondition(prop, constraints);
      Lookup.addExceptionalPostcondition(prop.getDecl(), constraints);
    }  
    return prop;
  }

  /* (non-Javadoc)
   * @see javafe.ast.VisitorArgResult#visitConstructorDecl(javafe.ast.ConstructorDecl, java.lang.Object)
   */
  @Override
  public final Object visitConstructorDecl(final /*@non_null*/ ConstructorDecl x, final Object o) {
    final MethodProperties prop = new MethodProperties(x);
    prop.fResult =  null;
    visitRoutineDecl(x, prop);
    
 
    if (!prop.fIsHelper) {
      final Term initially = (Term) prop.get("initiallyFOL");
      Lookup.addNormalPostcondition(prop, initially);
      Lookup.addExceptionalPostcondition(prop.getDecl(), initially);
    } 
    return prop;
  }




  
  
  
  /* (non-Javadoc)
   * @see javafe.ast.VisitorArgResult#visitLocalVarDecl(javafe.ast.LocalVarDecl, java.lang.Object)
   */
  @Override
  public Object visitLocalVarDecl(final /*@non_null*/ LocalVarDecl x, final Object o) {
    final MethodProperties prop = (MethodProperties) o;
    if (((Boolean) prop.get("quantifier")).booleanValue()) {
      final java.util.Set<QuantVariable> qVarsSet = (HashSet) prop.get("quantVars");
      final QuantVariable qvar = Expression.var(x);
      qVarsSet.add(qvar);
      prop.put("quantVars", qVarsSet);
    }   
    return null;
  }


  
  public /*@non_null*/ Object visitArrayRefExpr(/*@non_null*/ ArrayRefExpr x, Object o) {
    final Term var = (Term) x.array.accept(this, o); 
    final Term idx = (Term) x.index.accept(this, o);
    
    return Heap.selectArray(Heap.var, var, idx, Type.getSort(x));
  }
  

  /* (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitCondExprModifierPragma(escjava.ast.CondExprModifierPragma, java.lang.Object)
   */
  @Override
  public final Object visitCondExprModifierPragma(final /*@non_null*/ CondExprModifierPragma x, final Object o) {
    final MethodProperties prop = ((MethodProperties) o);
    final int tag = x.getTag();
    if (tag == TagConstants.ASSIGNABLE | 
        tag == TagConstants.MODIFIABLE | 
        tag == TagConstants.MODIFIES) {
      if (x.expr instanceof FieldAccess) {
        
        final FieldAccess var = (FieldAccess) x.expr;
        final QuantVariableRef targetVar = (QuantVariableRef) var.od.accept(this, o);
        final QuantVariableRef fieldVar = Expression.rvar(var.decl);
        final QuantVariableRef[] qvars = {targetVar, fieldVar};
        prop.fAssignableSet.add(qvars);   
      } 
      else if (x.expr instanceof NothingExpr) {
        prop.fNothing = true;
      }
    }
    
    return visitASTNode(x, o);
  }
 
  
 

  /* (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitEverythingExpr(escjava.ast.EverythingExpr, java.lang.Object)
   */
  @Override
  public final Object visitEverythingExpr(final /*@non_null*/ EverythingExpr x, final Object o) {
    return visitASTNode(x, o);
  }

  /* (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitExprDeclPragma(escjava.ast.ExprDeclPragma, java.lang.Object)
   */
  @Override
  public Object visitExprDeclPragma(final /*@non_null*/ ExprDeclPragma x, final Object o) {
    
    //FIXME: Should be a call to JML Trans...
    return null;
  }
  
  
  /**
   * @param x constraint node containing the parents class declaration
   * @param t translated term to conjoin the class constraints
   * @param o object containing the flag for subset checking
   */
  public void constrToConstraints(ExprDeclPragma x, Term t, Object o) {
    boolean constIsValid = true;
    Term constTerm = t;
    
    final Term allConst = Lookup.getConstraint(x.parent);
    
    if (fDoSubsetChecking) { 
      constIsValid = doSubsetChecking(o);
    }
    if (constIsValid && allConst != null) {
      constTerm = Logic.and(allConst, constTerm); 
    }
    else if (constIsValid) {
      Lookup.addConstraint(x.parent, constTerm); 
    }
    else if (!constIsValid) {
      System.out.println("Constraint error (subset check)! The following term was not conjoined to the overall type constraints: " + t.toString() + "\n");
    }
  }
  

  /* (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitExprModifierPragma(escjava.ast.ExprModifierPragma, java.lang.Object)
   */
  @Override
  public Object visitExprModifierPragma(final /*@non_null*/ ExprModifierPragma x, final Object o) {
    //FIXME: Should be a call to JML Trans...
    
    return null;
  }

  /* (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitVarExprModifierPragma(escjava.ast.VarExprModifierPragma, java.lang.Object)
   */
  @Override
  public Object visitVarExprModifierPragma(final /*@non_null*/ VarExprModifierPragma x, final Object o) {
    //FIXME: Should be a call to JML Trans...
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
    final RoutineDecl m = ((MethodProperties) o).getDecl();
    
//    for (final FormalParaDecl p: m.args.toArray()) {
//      final Term t1 = Expression.rvar(p);
//      final Term t2 = Expression.old(p);
//      final Set.Assignment assignment = new Set.Assignment((QuantVariableRef) t2, t1);
//      annos.add(new Set((QuantVariableRef) t2, assignment)); 
//    }
  }
  
  /**
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
          AnnotationDecoration.inst.setAnnotPre(s, annos);
          annos.clear();
        }
        if (inv != null) { // Add inv as invariant to next Loop Stmt
          if (Util.isLoop(s)) {
            AnnotationDecoration.inst.setInvariant(s, inv, prop); 
            inv = null;
          }
        }
//        if (s instanceof WhileStmt ||  // Visit body of Loop Stmt
//            s instanceof ForStmt || 
//            s instanceof DoStmt || 
//            s instanceof BlockStmt || 
//            s instanceof TryCatchStmt ||
//            s instanceof IfStmt ||
//            s instanceof VarDeclStmt) {
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
      if (isInvariant((ExprStmtPragma)s)) {
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

  private AAnnotation treatGhostDecl(VarDeclStmt s, MethodProperties prop) {
    return (Set) s.accept(fTrans, prop);
  }

  private AAnnotation treatPragma(ExprStmtPragma s, MethodProperties prop) {
    final Term t = (Term)s.accept(fTrans, prop);
    switch (s.getTag()) {
      case javafe.parser.TagConstants.ASSERT:
        return new Cut("assert" + prop.getAssertNumber(), 
                       Util.buildArgs(prop), t);
      case TagConstants.ASSUME:
        return new Assume(t);
      default:
        break;
    }
    return null;
  }

  private Term treatInvariant(final ExprStmtPragma s,
                              final Term oldInv,
                              final MethodProperties prop) {
    Term inv = oldInv;
    final Term t = (Term) s.accept(fTrans, prop);
    if (inv != null) {
      inv = Logic.and(inv, t);
    }
    else {
      inv = t;
    }
    return inv;
  }

  private boolean isInvariant(final ExprStmtPragma s) {
    final int tag = s.getTag();
    return tag == TagConstants.LOOP_INVARIANT ||
           tag == TagConstants.LOOP_INVARIANT_REDUNDANTLY ||
           tag == TagConstants.MAINTAINING ||
           tag == TagConstants.MAINTAINING_REDUNDANTLY;
  }

  private Set treatSetStmt(final List<AAnnotation> annos, 
                           final MethodProperties prop, final Stmt s) {
    Set.Assignment assignment;
    assignment = (Set.Assignment)s.accept(fTrans, prop);
    final Set newSet = new Set();
    newSet.assignment = assignment;
    final Iterator iter = annos.iterator();

    while (iter.hasNext()) { 
      final AAnnotation annot = (AAnnotation) iter.next();
      if (annot instanceof Set) {
        final Set existingSet = (Set) annot;
        if (existingSet.declaration.equals(newSet.assignment.fVar)) {
          annos.remove(existingSet);
          newSet.declaration = existingSet.declaration;
          break;
        }
      }
    }
    return newSet;
  }


  
  
  
  
  /* (non-Javadoc)
   * @see javafe.ast.VisitorArgResult#visitBlockStmt(javafe.ast.BlockStmt, java.lang.Object)
   */
  @Override
  public final Object visitBlockStmt(final /*@non_null*/ BlockStmt x, final Object o) {
    final List<AAnnotation> annos = new Vector<AAnnotation>();
   
    final MethodProperties prop = (MethodProperties) o;
    prop.fLocalVars.addLast(new Vector<QuantVariableRef>());
    //Save argument's values in prestate as ghosts at beginning of each routine (in annos)
    if (((Boolean) prop.get("routinebegin"))) {
      prop.put("routinebegin", Boolean.FALSE);
      argsToGhost(annos, prop);
    }

    handleStmt(x, annos, prop);
    
    // If there is no more Stmt, we generate a dummy SkipStmt 
    // to add last Stmt Pragma as precondition
    if (!annos.isEmpty()) { 
      final SkipStmt skipStmt = SkipStmt.make(0); //FIXME cbr: which location?
      AnnotationDecoration.inst.setAnnotPre(skipStmt, annos);
      x.stmts.addElement(skipStmt);
    }
    prop.fLocalVars.removeLast();
    return null;
  }

  /* (non-Javadoc)
   * @see javafe.ast.VisitorArgResult#visitVarDeclStmt(javafe.ast.VarDeclStmt, java.lang.Object)
   */
  @Override
  public Object visitVarDeclStmt(final /*@non_null*/ VarDeclStmt x, final Object o) {
    final MethodProperties prop = (MethodProperties) o;
    prop.fLocalVars.getLast().add(Expression.rvar(x.decl));

    return prop;
  }

  /* (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitExprStmtPragma(escjava.ast.ExprStmtPragma, java.lang.Object)
   */
  @Override
  public final Object visitExprStmtPragma(final /*@non_null*/ ExprStmtPragma x, final Object o) {
    return visitASTNode(x, o);
  }

  /* (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitGCExpr(escjava.ast.GCExpr, java.lang.Object)
   */
  @Override
  public final Object visitGCExpr(final /*@non_null*/ GCExpr x, final Object o) {
    
    if (x instanceof TypeExpr) { 
      final String name = Types.printName(((TypeExpr)x).type);
      return Expression.rvar(name, Type.sort);
    }
    return visitASTNode(x, o);
  }


  
  /* (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitImportPragma(escjava.ast.ImportPragma, java.lang.Object)
   */
  @Override
  public final Object visitImportPragma(final /*@non_null*/ ImportPragma x, final Object o) {
    return visitASTNode(x, o);
  }



  
  /* (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitModifiesGroupPragma(escjava.ast.ModifiesGroupPragma, java.lang.Object)
   */
  @Override
  public final Object visitModifiesGroupPragma(final /*@non_null*/ ModifiesGroupPragma x, final Object o) {
    return visitASTNode(x, o);
  }



  
  /* (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitParsedSpecs(escjava.ast.ParsedSpecs, java.lang.Object)
   */
  @Override
  public final Object visitParsedSpecs(final /*@non_null*/ ParsedSpecs x, final Object o) {
    //FIXME hel: what's up here?
    //return visitASTNode(x, o); //generates a stack overflow... but should be used
    return null;
  }

  

  

  

  

  
  /* (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitSetStmtPragma(escjava.ast.SetStmtPragma, java.lang.Object)
   */
  public final Object visitSetStmtPragma(final /*@non_null*/ SetStmtPragma x, final Object o) {
    final Set.Assignment res = new Set.Assignment();
    if (x.target instanceof VariableAccess) {
      res.fVar = (QuantVariableRef) x.target.accept(this, o);
      res.fExpr = (Term) x.value.accept(this, o);
    }
    return res;
  }

  
 

  /* (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitNewInstanceExpr(escjava.ast.NewInstanceExpr, java.lang.Object)
   */
  public /*@non_null*/ Object visitNewInstanceExpr(/*@non_null*/ NewInstanceExpr x, Object o) {
    final String name = Types.printName(x.type);
    return Expression.rvar(name, Type.typeToSort(x.type)); // Ref.sort);
  }
  

  
  




  /**
   * @param o Properties object also containing all modifiable types.
   * 
   */
  public void invPredToPreconditions(final /*@non_null*/ Object o) {
    final MethodProperties prop = (MethodProperties) o;
    final QuantVariableRef x = Expression.rvar(Ref.sort);
    final QuantVariableRef type = Expression.rvar(Type.sort);
    final QuantVariable[] vars = {x.qvar, type.qvar};
    final Term invTerm = Logic.inv(Heap.var, x, type);
    final Term typeOfTerm = Logic.assignCompat(Heap.var, x, type);
    final Term allocTerm = Logic.isAlive(Heap.var, x);
    Term andTerm = Logic.and(allocTerm, typeOfTerm);
    if (((MethodProperties)o).fIsConstructor) {
      final Term notEQThis = Logic.not(Logic.equals(x, Ref.varThis));
      andTerm = Logic.and(andTerm, notEQThis);
    }    
    final Term implTerm = Logic.implies(andTerm, invTerm);
    final Term forAllTerm = Logic.forall(vars, implTerm);
    Lookup.addPrecondition(prop.getDecl(), forAllTerm);
  }


  public Term invPostPred(final /*@non_null*/ Object o) {
    final QuantVariableRef x = Expression.rvar(Ref.sort);
    final QuantVariableRef type = Expression.rvar(Type.sort);
    final QuantVariable[] vars = {x.qvar, type.qvar}; 
    final Term invTerm = Logic.inv(Heap.var, x, type);
    final Term typeOfTerm = Logic.assignCompat(Heap.var, x, type);
    final Term allocTerm = Logic.isAlive(Heap.var, x);
    Term andTerm = Logic.and(allocTerm, typeOfTerm);
    final java.util.Set<javafe.ast.Type> visSet = fGlobal.visibleTypeSet;
    if (!visSet.isEmpty()) {
      final Term visibleTerm = Logic.isVisibleIn(type, fGlobal);
      andTerm = Logic.and(andTerm, visibleTerm);
    }
    
    final Term implTerm = Logic.implies(andTerm, invTerm);
    final Term forAllTerm = Logic.forall(vars, implTerm);
    return forAllTerm;
  }
  
  
  public void invPredToPostconditions(final /*@non_null*/ MethodProperties prop) { 
    Lookup.addNormalPostcondition(prop, 
                                  invPostPred(prop));
  }

  
  private void invPredToExceptionalPostconditions(MethodProperties prop) {
    Lookup.addExceptionalPostcondition(prop.getDecl(), invPostPred(prop));
  }
  

  
  /**
   * @param o containing all field access of the invariant and the class id
   * @return boolean value whether the subset checking of the invariant fields was successfull 
   */
  @SuppressWarnings("unchecked")
  public boolean doSubsetChecking(final Object o) {
    final MethodProperties prop = (MethodProperties) o;
    final java.util.Set<FieldAccess> subSet = (HashSet) prop.get("subsetCheckingSet");
    FieldAccess fa;
    final Identifier parentId = fGlobal.getClassId();
    Identifier typeId;
    boolean result = true;
    final Iterator iter = subSet.iterator();
    while (iter.hasNext()) {   
      fa = (FieldAccess)iter.next();
      typeId = fa.decl.parent.id;
      if (!parentId.equals(typeId)) {
        System.out.println("Subset checking: failed! " +
            "The field \"" + fa.id + 
            "\" is a field of class " + typeId + 
            " and not as expected of class " + parentId + "!");  
        result = false;
      }
    }
    prop.put("subsetCheckingSet", new HashSet<FieldAccess>()); //empty set
    return result;
  }
  
  /**
   * Adds a Term to the routines postcondition describing 
   * all assignable variables.
   * @param o Properties object also containing all assignable variables
   */
  public void doAssignable(final Object o) {
    final MethodProperties prop = (MethodProperties) o;
    if (prop.fNothing || !prop.fAssignableSet.isEmpty()) {
      final QuantVariableRef target = Expression.rvar(Ref.sort);
      final QuantVariableRef field = Expression.rvar(Type.sortField);
      final QuantVariable[] vars = {target.qvar, field.qvar};
      Term t;
      if (!prop.fAssignableSet.isEmpty()) {
        t = Logic.or(Logic.isAssignable(target, field, o), 
                          Logic.assignablePred(Heap.var, Heap.varPre, target, field));
      } 
      else {
        t = Logic.assignablePred(Heap.var, Heap.varPre, target, field);
      }
      
      final Term forAllTerm = Logic.forall(vars, t);
      Lookup.addNormalPostcondition(prop, forAllTerm);
      Lookup.addExceptionalPostcondition(prop.getDecl(), forAllTerm);
    } 
  }

  
  
  
  


  
  

  /**
   * @param x invariant node containing the parents class declaration
   * @param t translated term to conjoin the class invariants
   * @param o object containing the flag for subset checking
   */
  public void addToInv(final ExprDeclPragma x, final Term t, final Object o) {
    if (t != null) {
      boolean invIsValid = true;
      Term invTerm = t;
      final Term allInvs = Lookup.getInvariant(x.parent);
      
      if (fDoSubsetChecking) { 
        invIsValid = doSubsetChecking(o);
      }
      if (invIsValid && allInvs != null) {
        invTerm = Logic.and(allInvs, invTerm); 
      }
      else if (invIsValid) {
        Lookup.addInvariant(x.parent, invTerm); 
      }
      else if (!invIsValid) {
        System.out.println("Invariant error (subset check)! " +
            "The following term was not conjoined to the overall type " +
            "invariant: " + t.toString() + "\n");
      }
    }
   
  }
  
  

}
