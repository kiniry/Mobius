package mobius.directVCGen.formula.jmlTranslator;

import mobius.directVCGen.formula.Bool;
import mobius.directVCGen.formula.Expression;
import mobius.directVCGen.formula.Formula;
import mobius.directVCGen.formula.Heap;
import mobius.directVCGen.formula.Logic;
import mobius.directVCGen.formula.Lookup;
import mobius.directVCGen.formula.Ref;
import mobius.directVCGen.formula.Type;
import mobius.directVCGen.formula.annotation.AAnnotation;
import mobius.directVCGen.formula.annotation.AnnotationDecoration;
import mobius.directVCGen.formula.annotation.Assume;
import mobius.directVCGen.formula.annotation.Cut;
import mobius.directVCGen.formula.annotation.Set;
import mobius.directVCGen.vcgen.struct.Post;

import java.util.HashSet;
import java.util.Properties;
import java.util.Vector;
import javafe.ast.ASTNode;
import javafe.ast.AmbiguousVariableAccess;
import javafe.ast.BinaryExpr;
import javafe.ast.BlockStmt;
import javafe.ast.ClassDecl;
import javafe.ast.ConstructorDecl;
import javafe.ast.DoStmt;
import javafe.ast.ExprObjectDesignator;
import javafe.ast.FieldAccess;
import javafe.ast.FieldDecl;
import javafe.ast.ForStmt;
import javafe.ast.FormalParaDecl;
import javafe.ast.GenericVarDecl;
import javafe.ast.IfStmt;
import javafe.ast.InstanceOfExpr;
import javafe.ast.LiteralExpr;
import javafe.ast.LocalVarDecl;
import javafe.ast.MethodDecl;
import javafe.ast.ModifierPragma;
import javafe.ast.ObjectDesignator;
import javafe.ast.RoutineDecl;
import javafe.ast.SkipStmt;
import javafe.ast.Stmt;
import javafe.ast.ThisExpr;
import javafe.ast.TryCatchStmt;
import javafe.ast.VarDeclStmt;
import javafe.ast.VariableAccess;
import javafe.ast.WhileStmt;
import escjava.ast.AnOverview;
import escjava.ast.ArrayRangeRefExpr;
import escjava.ast.CondExprModifierPragma;
import escjava.ast.Condition;
import escjava.ast.DecreasesInfo;
import escjava.ast.DefPred;
import escjava.ast.DefPredApplExpr;
import escjava.ast.DefPredLetExpr;
import escjava.ast.DependsPragma;
import escjava.ast.EscPrimitiveType;
import escjava.ast.EverythingExpr;
import escjava.ast.ExprDeclPragma;
import escjava.ast.ExprModifierPragma;
import escjava.ast.ExprStmtPragma;
import escjava.ast.GCExpr;
import escjava.ast.GhostDeclPragma;
import escjava.ast.GuardExpr;
import escjava.ast.GuardedCmd;
import escjava.ast.IdExprDeclPragma;
import escjava.ast.IdentifierModifierPragma;
import escjava.ast.ImportPragma;
import escjava.ast.LockSetExpr;
import escjava.ast.MapsExprModifierPragma;
import escjava.ast.ModelConstructorDeclPragma;
import escjava.ast.ModelDeclPragma;
import escjava.ast.ModelMethodDeclPragma;
import escjava.ast.ModelProgamModifierPragma;
import escjava.ast.ModelTypePragma;
import escjava.ast.ModifiesGroupPragma;
import escjava.ast.NamedExprDeclPragma;
import escjava.ast.NaryExpr;
import escjava.ast.NestedModifierPragma;
import escjava.ast.NotModifiedExpr;
import escjava.ast.NotSpecifiedExpr;
import escjava.ast.NothingExpr;
import escjava.ast.NowarnPragma;
import escjava.ast.ParsedSpecs;
import escjava.ast.ReachModifierPragma;
import escjava.ast.RefinePragma;
import escjava.ast.ResExpr;
import escjava.ast.SetCompExpr;
import escjava.ast.SetStmtPragma;
import escjava.ast.SimpleModifierPragma;
import escjava.ast.SimpleStmtPragma;
import escjava.ast.SkolemConstantPragma;
import escjava.ast.Spec;
import escjava.ast.StillDeferredDeclPragma;
import escjava.ast.TagConstants;
import escjava.ast.VarDeclModifierPragma;
import escjava.ast.VarExprModifierPragma;
import escjava.ast.VisitorArgResult;
import escjava.ast.WildRefExpr;
import escjava.sortedProver.Lifter.FnTerm;
import escjava.sortedProver.Lifter.QuantVariable;
import escjava.sortedProver.Lifter.QuantVariableRef;
import escjava.sortedProver.Lifter.Term;


/**
 * @author Claudia Brauchli (claudia@vis.ethz.ch)
 * @author Hermann Lehner (hermann.lehner@inf.ethz.ch)
 * 
 */
public class JmlVisitor extends VisitorArgResult {

  /**
   * Reference to JML Expression Translator.
   */
  private final JmlExprToFormula fTranslator;
  /**
   * Properties that are passed as argument of the visitor.
   */
  private final Properties fProperties;

  /**
   * Visitor that translates JML Constructs to FOL by using JmlExprToFormula to
   * translate expressions.
   */
  public JmlVisitor() {
    fProperties = new Properties();
    fProperties.put("pred", Boolean.TRUE);
    fProperties.put("old", Boolean.FALSE);
    fProperties.put("fieldSet", new HashSet<QuantVariableRef>());
    fProperties.put("assignableSet", new HashSet<QuantVariableRef[]>());
    fProperties.put("nothing", Boolean.FALSE); //used for assignable
    fProperties.put("interesting", Boolean.FALSE);
    // firstPost: To add invariant only once to Lookup.postcondition
    fProperties.put("firstPost", Boolean.TRUE);
    fProperties.put("routinebegin", Boolean.TRUE);    
    fTranslator = new JmlExprToFormula(this);
     
  }

  /* (non-Javadoc)
   * @see javafe.ast.VisitorArgResult#visitASTNode(javafe.ast.ASTNode, java.lang.Object)
   */
  @Override
  public final Object visitASTNode(final ASTNode x, final Object prop) {
    Object o = null;
    final int max = x.childCount();
    for (int i = 0; i < max; i++) {
      final Object child = x.childAt(i);
      if (child instanceof ASTNode) {
        o = ((ASTNode) child).accept(this, prop);
        if (o != null) {
          if (!o.equals(child)) {
            System.out.println(o);
          }
        }
      }

    }
    return o;
  }

  /* (non-Javadoc)
   * @see javafe.ast.VisitorArgResult#visitClassDecl(javafe.ast.ClassDecl, java.lang.Object)
   */
  @Override
  public final Object visitClassDecl(final /*@non_null*/ ClassDecl x, final Object o) {
    //Use default properties to start with.
    return visitTypeDecl(x, this.fProperties);
  }

  
  
  
  /* (non-Javadoc 
   * @see javafe.ast.VisitorArgResult#visitRoutineDecl(javafe.ast.RoutineDecl, java.lang.Object)
   */
  @Override
  public final Object visitRoutineDecl(final /*@non_null*/ RoutineDecl x, final Object o) {
    x.accept(new VisibleTypeCollector(), o); 
    ((Properties) o).put("method", x);
    ((Properties) o).put("firstPost", Boolean.TRUE);
    ((Properties) o).put("routinebegin", Boolean.TRUE);
    ((Properties) o).put("nothing", Boolean.FALSE);
    final QuantVariableRef result = (QuantVariableRef) ((Properties) o).get("result");
    Lookup.postconditions.put(x, new Post(result, Logic.True()));
    Lookup.exceptionalPostconditions.put(x, new Post(Expression.rvar(Ref.sort), Logic.True()));
    final Object fObj = visitASTNode(x, o);
    doAssignable(o);
    return fObj;
  }

  
  
  

  /* (non-Javadoc)
   * @see javafe.ast.VisitorArgResult#visitMethodDecl(javafe.ast.MethodDecl, java.lang.Object)
   */
  @Override
  public final Object visitMethodDecl(final /*@non_null*/ MethodDecl x, final Object o) {
    ((Properties) o).put("result", Expression.rvar(Expression.getResultVar(x)));
    return visitRoutineDecl(x, o);
  }

  /* (non-Javadoc)
   * @see javafe.ast.VisitorArgResult#visitConstructorDecl(javafe.ast.ConstructorDecl, java.lang.Object)
   */
  @Override
  public final Object visitConstructorDecl(final /*@non_null*/ ConstructorDecl x, final Object o) {
    return visitRoutineDecl(x, o);
  }

  /* (non-Javadoc)
   * @see javafe.ast.VisitorArgResult#visitFormalParaDecl(javafe.ast.FormalParaDecl, java.lang.Object)
   */
  @Override
  public final Object visitFormalParaDecl(final /*@non_null*/ FormalParaDecl x, final Object o) {
    return this.fTranslator.genericVarDecl(x, o);
  }

  /* (non-Javadoc)
   * @see javafe.ast.VisitorArgResult#visitLiteralExpr(javafe.ast.LiteralExpr, java.lang.Object)
   */
  @Override
  public final Object visitLiteralExpr(final /*@non_null*/ LiteralExpr x, final Object o) {
    final Properties prop = (Properties) o;
    if (((Boolean) prop.get("interesting")).booleanValue()) {
      return this.fTranslator.literal(x, o);
    }
    else {
      return null;
    }
  }

  /* (non-Javadoc)
   * @see javafe.ast.VisitorArgResult#visitVariableAccess(javafe.ast.VariableAccess, java.lang.Object)
   */
  @Override
  public final Object visitVariableAccess(final /*@non_null*/ VariableAccess x, final Object o) {
    if (((Boolean) ((Properties) o).get("interesting")).booleanValue()) {
      return this.fTranslator.variableAccess(x, o);
    }
    else {
      return null;
    }
  }

  /* (non-Javadoc)
   * @see javafe.ast.VisitorArgResult#visitFieldAccess(javafe.ast.FieldAccess, java.lang.Object)
   */
  @Override
  public final Object visitFieldAccess(final /*@non_null*/ FieldAccess x, final Object o) {
    if (((Boolean) ((Properties) o).get("interesting")).booleanValue()) {
      return this.fTranslator.fieldAccess(x, o);
    }
    else {
      return null;
    }
  }
  
  
  
  /* (non-Javadoc)
   * @see javafe.ast.VisitorArgResult#visitLocalVarDecl(javafe.ast.LocalVarDecl, java.lang.Object)
   */
  @Override
  public Object visitLocalVarDecl(final /*@non_null*/ LocalVarDecl x, final Object o) {
    return null;
  }

  /* (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitNaryExpr(escjava.ast.NaryExpr, java.lang.Object)
   */
  @Override
  public final Object visitNaryExpr(final /*@non_null*/ NaryExpr x, final Object o) {
    if (((Boolean) ((Properties) o).get("interesting")).booleanValue()) {
      if (x.op == TagConstants.PRE) {
        return this.fTranslator.naryExpr(x, o);
      }
      else {
        return visitGCExpr(x, o);
      }
    }
    else {
      return null;
    }
  }

  /* (non-Javadoc)
   * @see javafe.ast.VisitorArgResult#visitInstanceOfExpr(javafe.ast.InstanceOfExpr, java.lang.Object)
   */
  @Override
  public final Object visitInstanceOfExpr(final /*@non_null*/ InstanceOfExpr x, final Object o) {
    if (((Boolean) ((Properties) o).get("interesting")).booleanValue()) {
      return this.fTranslator.instanceOfExpr(x, o);
    }
    else {
      return null;
    }
  }

  /* (non-Javadoc)
   * @see javafe.ast.VisitorArgResult#visitThisExpr(javafe.ast.ThisExpr, java.lang.Object)
   */
  @Override
  public final Object visitThisExpr(final /*@non_null*/ ThisExpr x, final Object o) {
    if (((Boolean) ((Properties) o).get("interesting")).booleanValue()) {
      return this.fTranslator.thisLiteral(x, o);
    }
    else {
      return null;
    }
  }

  /* (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitArrayRangeRefExpr(escjava.ast.ArrayRangeRefExpr, java.lang.Object)
   */
  @Override
  public final Object visitArrayRangeRefExpr(final /*@non_null*/ ArrayRangeRefExpr x, final Object o) {
    return null;
  }

  /* (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitCondExprModifierPragma(escjava.ast.CondExprModifierPragma, java.lang.Object)
   */
  @Override
  public final Object visitCondExprModifierPragma(final /*@non_null*/ CondExprModifierPragma x, final Object o) {
    
    switch (x.getTag()) {
    case TagConstants.ASSIGNABLE:
      if (x.expr instanceof FieldAccess){
        final HashSet<QuantVariableRef[]> fAssignableSet = (HashSet<QuantVariableRef[]>) ((Properties) o).get("assignableSet");
        final FieldAccess var = (FieldAccess) x.expr;
        final QuantVariableRef targetVar = (QuantVariableRef) var.od.accept(this,o);
        final QuantVariableRef fieldVar = Expression.rvar(var.decl);
        final QuantVariableRef[] qvars = {targetVar, fieldVar};
        fAssignableSet.add(qvars);
        ((Properties) o).put("assignableSet",fAssignableSet);    
      }
      else if (x.expr instanceof NothingExpr)
      {
        ((Properties) o).put("nothing",Boolean.TRUE);
      }
      break;
   
   
    default:
      break;
  }
    
    return visitASTNode(x, o);
  }
 
  
  
  /* (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitCondition(escjava.ast.Condition, java.lang.Object)
   */
  @Override
  public final Object visitCondition(final /*@non_null*/ Condition x, final Object o) {
    return null;
  }

  /* (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitDecreasesInfo(escjava.ast.DecreasesInfo, java.lang.Object)
   */
  @Override
  public final Object visitDecreasesInfo(final /*@non_null*/ DecreasesInfo x, final Object o) {
    return null;
  }

  /* (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitDefPred(escjava.ast.DefPred, java.lang.Object)
   */
  @Override
  public final Object visitDefPred(final /*@non_null*/ DefPred x, final Object o) {
    return null;
  }

  /* (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitDefPredApplExpr(escjava.ast.DefPredApplExpr, java.lang.Object)
   */
  @Override
  public final Object visitDefPredApplExpr(final /*@non_null*/ DefPredApplExpr x, final Object o) {
    return null;
  }

  /* (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitDefPredLetExpr(escjava.ast.DefPredLetExpr, java.lang.Object)
   */
  @Override
  public final Object visitDefPredLetExpr(final /*@non_null*/ DefPredLetExpr x, final Object o) {
    return null;
  }

  /* (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitDependsPragma(escjava.ast.DependsPragma, java.lang.Object)
   */
  @Override
  public final Object visitDependsPragma(final /*@non_null*/ DependsPragma x, final Object o) {
    return null;
  }

  /* (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitEscPrimitiveType(escjava.ast.EscPrimitiveType, java.lang.Object)
   */
  @Override
  public final Object visitEscPrimitiveType(final /*@non_null*/ EscPrimitiveType x, final Object o) {
    return null;
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
  public final Object visitExprDeclPragma(final /*@non_null*/ ExprDeclPragma x, final Object o) {
    ((Properties) o).put("interesting", Boolean.TRUE);
    final Term  t = (Term) x.expr.accept(this, o);
    Lookup.invariants.put(x.parent, t);
    return null;
  }

  /* (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitExprModifierPragma(escjava.ast.ExprModifierPragma, java.lang.Object)
   */
  @Override
  public final Object visitExprModifierPragma(final /*@non_null*/ ExprModifierPragma x, final Object o) {
    ((Properties) o).put("interesting", Boolean.TRUE);
    final RoutineDecl rd = (RoutineDecl)((Properties) o).get("method");
    Term t = (Term)visitASTNode(x, o);
    switch (x.getTag()) {
      case TagConstants.REQUIRES:
        if (rd  instanceof MethodDecl) { 
          final Term invToPre = (Term) invToPreconditions(o);
          t = Logic.Safe.and(t, invToPre);
        }
        if (rd instanceof ConstructorDecl){
          t = Logic.boolToProp(t);
        }
        Lookup.preconditions.put(rd, t);
        break;
      case TagConstants.ENSURES:
        Post allPosts = Lookup.postconditions.get(rd);
        // FIXME jgc: I don't know if fVar should be needed here; needs a review
        allPosts = new Post(allPosts.getRVar(), Logic.and(allPosts.getPost(), t));
        if (((Boolean) ((Properties) o).get("firstPost")).booleanValue()) {
          final Term invToPost = (Term) invToPostconditions(o);
          allPosts = new Post(allPosts.getRVar(), Logic.and(allPosts.getPost(), invToPost));
          ((Properties) o).put("firstPost", Boolean.FALSE);
        }
        Lookup.postconditions.put(rd, allPosts);
        break;
      case TagConstants.ASSIGNABLE:
      final int a = 8;
        break;
      case TagConstants.DIVERGES:
        final int ad = 8;
          break;
      default:
        break;
    }
    return null;
  }

  /* (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitVarExprModifierPragma(escjava.ast.VarExprModifierPragma, java.lang.Object)
   */
  @Override
  public final Object visitVarExprModifierPragma(final /*@non_null*/ VarExprModifierPragma x, final Object o) {
    ((Properties) o).put("interesting", Boolean.TRUE);

    final RoutineDecl currentRoutine = (RoutineDecl) ((Properties) o).get("method");
    Post allExPosts = Lookup.exceptionalPostconditions.get(currentRoutine);
    final QuantVariableRef commonExceptionVar = allExPosts.getRVar();

    final Term typeOfException = Type.translate(x.arg.type);
    final QuantVariableRef newExceptionVar = Expression.rvar(x.arg);

    Term newExPost = (Term)x.expr.accept(this, o);
    newExPost = newExPost.subst(newExceptionVar, commonExceptionVar);
    final Term guard = Logic.assignCompat(Heap.var, commonExceptionVar, typeOfException);
    final Term result = Logic.Safe.implies(guard, newExPost);
    allExPosts = new Post(allExPosts.getRVar(), Logic.and(allExPosts.getPost(), result));
    Lookup.exceptionalPostconditions.put(currentRoutine, allExPosts);


    return null;
  }

  /* (non-Javadoc)
   * @see javafe.ast.VisitorArgResult#visitBlockStmt(javafe.ast.BlockStmt, java.lang.Object)
   */
  @Override
  public final Object visitBlockStmt(final /*@non_null*/ BlockStmt x, final Object o) {
    Term t = null;
    Term t1 = null;
    Term t2 = null;
    Set  set = null;
    Set.Assignment assignment = null;
    boolean interesting;
    final Vector<AAnnotation> annos = new Vector<AAnnotation>();
    Term inv = null;

    //Save arguments values in prestate as ghosts.
    if (((Boolean)((Properties) o).get("routinebegin")).booleanValue()){
      ((Properties) o).put("routinebegin", Boolean.FALSE);
      final RoutineDecl m = (RoutineDecl) ((Properties) o).get("method");
      for (final FormalParaDecl p: m.args.toArray()) {
        t1 = Expression.rvar(p);
        t2 = Expression.old(p);
        assignment = new Set.Assignment((QuantVariableRef) t2, t1);
        annos.add(new Set((QuantVariableRef) t2, assignment)); 
      }
    }

    //
    for (final Stmt s: x.stmts.toArray()) {
      interesting = false;
      //We are interested in Asserts, Assumes and Loop Invariants
      if (s instanceof ExprStmtPragma) {
        interesting = true; 
        ((Properties) o).put("interesting", new Boolean(true));
        t = (Term)s.accept(this, o);
        switch (s.getTag()) {
          case javafe.parser.TagConstants.ASSERT:
            annos.add(new Cut(t));
            break;
          case TagConstants.ASSUME:
            annos.add(new Assume(t));
            break;
          case TagConstants.LOOP_INVARIANT:
          case TagConstants.MAINTAINING:
            inv = t;
            break;
            //decreases, decreasing, loop_predicate
          default:
            break;
        }
      }
      else

        //We are also interested in ghost var declarations
        if (s instanceof VarDeclStmt) {

          for (final ModifierPragma p: ((VarDeclStmt) s).decl.pmodifiers.toArray()) {
            if (p.getTag() == TagConstants.GHOST) {
              interesting = true;
              break;
            }
          }
          if (interesting) {
            ((Properties) o).put("interesting", new Boolean(true));
            t = (Term)s.accept(this, o);
            final Set ghostVar = new Set();
            ghostVar.declaration = (QuantVariableRef) t;
            annos.add(ghostVar);
          }
        }
        else
          
          //Also set statements should be processed
          if (s instanceof SetStmtPragma) {
            interesting = true;
            ((Properties) o).put("interesting", new Boolean(true));
            assignment = (Set.Assignment)s.accept(this, o);
            set = new Set();
            set.assignment = assignment;
            annos.add(set);
          }

      if (interesting) {
        x.stmts.removeElement(s);
      } 
      else {
        ((Properties) o).put("interesting", new Boolean(false));
        if (!annos.isEmpty()) {
          AnnotationDecoration.inst.setAnnotPre(s, annos);
          annos.clear();
        }
        if (inv != null) {
          if (s instanceof WhileStmt || 
              s instanceof ForStmt || 
              s instanceof DoStmt) {
            AnnotationDecoration.inst.setInvariant(s, inv);
            inv = null;
          }
        }
        if (s instanceof WhileStmt || 
            s instanceof ForStmt || 
            s instanceof DoStmt || 
            s instanceof BlockStmt || 
            s instanceof TryCatchStmt ||
            s instanceof IfStmt) {
          s.accept(this, o);
        }
      }
    }
    
    //If there is no more Stmt, we generate a dummy SkipStmt and add the last precondition to it
    if (!annos.isEmpty()) { 
      final SkipStmt skipStmt = SkipStmt.make(0); //FIXME cbr: which location?
      AnnotationDecoration.inst.setAnnotPre(skipStmt, annos);
      x.stmts.addElement(skipStmt);
      annos.clear();
    }    
    return null;
  }

  /* (non-Javadoc)
   * @see javafe.ast.VisitorArgResult#visitVarDeclStmt(javafe.ast.VarDeclStmt, java.lang.Object)
   */
  @Override
  public final Object visitVarDeclStmt(final /*@non_null*/ VarDeclStmt x, final Object o) {
    //It's only called if we have a ghost variable declaration
    return Expression.rvar(x.decl);
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
    return visitASTNode(x, o);
  }

  /* (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitGhostDeclPragma(escjava.ast.GhostDeclPragma, java.lang.Object)
   */
  @Override
  public final Object visitGhostDeclPragma(final /*@non_null*/ GhostDeclPragma x, final Object o) {
    return null;
  }

  /* (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitGuardExpr(escjava.ast.GuardExpr, java.lang.Object)
   */
  @Override
  public final Object visitGuardExpr(final /*@non_null*/ GuardExpr x, final Object o) {
    return null;
  }

  /* (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitGuardedCmd(escjava.ast.GuardedCmd, java.lang.Object)
   */
  @Override
  public final Object visitGuardedCmd(final /*@non_null*/ GuardedCmd x, final Object o) {
    return null;
  }

  /* (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitIdExprDeclPragma(escjava.ast.IdExprDeclPragma, java.lang.Object)
   */
  @Override
  public final Object visitIdExprDeclPragma(final /*@non_null*/ IdExprDeclPragma x, final Object o) {
    return null;
  }

  
  /* (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitIdentifierModifierPragma(escjava.ast.IdentifierModifierPragma, java.lang.Object)
   */
  @Override
  public final Object visitIdentifierModifierPragma(final /*@non_null*/ IdentifierModifierPragma x, final Object o) {
    return null;
  }

  
  /* (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitImportPragma(escjava.ast.ImportPragma, java.lang.Object)
   */
  @Override
  public final Object visitImportPragma(final /*@non_null*/ ImportPragma x, final Object o) {
    return visitASTNode(x, o);
  }

  
  /* (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitLockSetExpr(escjava.ast.LockSetExpr, java.lang.Object)
   */
  @Override
  public final Object visitLockSetExpr(final /*@non_null*/ LockSetExpr x, final Object o) {
    return null;
  }

  
  /* (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitMapsExprModifierPragma(escjava.ast.MapsExprModifierPragma, java.lang.Object)
   */
  @Override
  public final Object visitMapsExprModifierPragma(final /*@non_null*/ MapsExprModifierPragma x, final Object o) {
    return null;
  }

  
  /* (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitModelConstructorDeclPragma(escjava.ast.ModelConstructorDeclPragma, java.lang.Object)
   */
  @Override
  public final Object visitModelConstructorDeclPragma(final /*@non_null*/ ModelConstructorDeclPragma x, final Object o) {
    return null;
  }

  
  /* (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitModelDeclPragma(escjava.ast.ModelDeclPragma, java.lang.Object)
   */
  @Override
  public final Object visitModelDeclPragma(final /*@non_null*/ ModelDeclPragma x, final Object o) {
    return null;
  }

  
  /* (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitModelMethodDeclPragma(escjava.ast.ModelMethodDeclPragma, java.lang.Object)
   */
  @Override
  public final Object visitModelMethodDeclPragma(final /*@non_null*/ ModelMethodDeclPragma x, final Object o) {
    return null;
  }

  
  /* (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitModelProgamModifierPragma(escjava.ast.ModelProgamModifierPragma, java.lang.Object)
   */
  @Override
  public final Object visitModelProgamModifierPragma(final /*@non_null*/ ModelProgamModifierPragma x, final Object o) {
    return null;
  }

  
  /* (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitModelTypePragma(escjava.ast.ModelTypePragma, java.lang.Object)
   */
  @Override
  public final Object visitModelTypePragma(final /*@non_null*/ ModelTypePragma x, final Object o) {
    return null;
  }

  
  /* (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitModifiesGroupPragma(escjava.ast.ModifiesGroupPragma, java.lang.Object)
   */
  @Override
  public final Object visitModifiesGroupPragma(final /*@non_null*/ ModifiesGroupPragma x, final Object o) {
    return visitASTNode(x, o);
  }

  
  /* (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitNamedExprDeclPragma(escjava.ast.NamedExprDeclPragma, java.lang.Object)
   */
  @Override
  public final Object visitNamedExprDeclPragma(final /*@non_null*/ NamedExprDeclPragma x, final Object o) {
    return null;
  }

  
  /* (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitNestedModifierPragma(escjava.ast.NestedModifierPragma, java.lang.Object)
   */
  @Override
  public final Object visitNestedModifierPragma(final /*@non_null*/ NestedModifierPragma x, final Object o) {
    return null;
  }

  
  /* (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitNotModifiedExpr(escjava.ast.NotModifiedExpr, java.lang.Object)
   */
  @Override
  public final Object visitNotModifiedExpr(final /*@non_null*/ NotModifiedExpr x, final Object o) {
    return null;
  }

  
  /* (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitNotSpecifiedExpr(escjava.ast.NotSpecifiedExpr, java.lang.Object)
   */
  @Override
  public final Object visitNotSpecifiedExpr(final /*@non_null*/ NotSpecifiedExpr x, final Object o) {
    return null;
  }

  
  /* (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitNothingExpr(escjava.ast.NothingExpr, java.lang.Object)
   */
  @Override
  public final Object visitNothingExpr(final /*@non_null*/ NothingExpr x, final Object o) {
    return null;
  }

  
  /* (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitNowarnPragma(escjava.ast.NowarnPragma, java.lang.Object)
   */
  @Override
  public final Object visitNowarnPragma(final /*@non_null*/ NowarnPragma x, final Object o) {
    return null;
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
   * @see escjava.ast.VisitorArgResult#visitReachModifierPragma(escjava.ast.ReachModifierPragma, java.lang.Object)
   */
  public final Object visitReachModifierPragma(final /*@non_null*/ ReachModifierPragma x, final Object o) {
    return null;
  }

  
  /* (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitRefinePragma(escjava.ast.RefinePragma, java.lang.Object)
   */
  public final Object visitRefinePragma(final /*@non_null*/ RefinePragma x, final Object o) {
    return null;
  }

  
  /* (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitResExpr(escjava.ast.ResExpr, java.lang.Object)
   */
  public final Object visitResExpr(final /*@non_null*/ ResExpr x, final Object o) {
    if (((Boolean) ((Properties) o).get("interesting")).booleanValue()) {
      return this.fTranslator.resultLiteral(x, o);
    }
    else {
      return null;
    }
  }

  
  /* (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitSetCompExpr(escjava.ast.SetCompExpr, java.lang.Object)
   */
  public final Object visitSetCompExpr(final /*@non_null*/ SetCompExpr x, final Object o) {
    return null;
  }

  
  /* (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitSetStmtPragma(escjava.ast.SetStmtPragma, java.lang.Object)
   */
  public final Object visitSetStmtPragma(final /*@non_null*/ SetStmtPragma x, final Object o) {
    final Set.Assignment res = new Set.Assignment();
    res.var = (QuantVariableRef) x.target.accept(this, o);
    res.expr = (Term) x.value.accept(this, o);
    return res;
  }

  
  /* (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitSimpleModifierPragma(escjava.ast.SimpleModifierPragma, java.lang.Object)
   */
  public final Object visitSimpleModifierPragma(final /*@non_null*/ SimpleModifierPragma x, final Object o) {
    return null;
  }

  
  /* (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitSimpleStmtPragma(escjava.ast.SimpleStmtPragma, java.lang.Object)
   */
  public final Object visitSimpleStmtPragma(final /*@non_null*/ SimpleStmtPragma x, final Object o) {
    return null;
  }

  
  /* (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitSkolemConstantPragma(escjava.ast.SkolemConstantPragma, java.lang.Object)
   */
  public final Object visitSkolemConstantPragma(final /*@non_null*/ SkolemConstantPragma x, final Object o) {
    return null;
  }

  
  /* (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitSpec(escjava.ast.Spec, java.lang.Object)
   */
  public final Object visitSpec(final /*@non_null*/ Spec x, final Object o) {
    return null;
  }

  
  /* (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitStillDeferredDeclPragma(escjava.ast.StillDeferredDeclPragma, java.lang.Object)
   */
  public final Object visitStillDeferredDeclPragma(final /*@non_null*/ StillDeferredDeclPragma x, final Object o) {
    return null;
  }

  
  /* (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitVarDeclModifierPragma(escjava.ast.VarDeclModifierPragma, java.lang.Object)
   */
  public final Object visitVarDeclModifierPragma(final /*@non_null*/ VarDeclModifierPragma x, final Object o) {
    return null;
  }

  
  /* (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitWildRefExpr(escjava.ast.WildRefExpr, java.lang.Object)
   */
  public final Object visitWildRefExpr(final /*@non_null*/ WildRefExpr x, final Object o) {
    return null;
  }

  
  /* (non-Javadoc)
   * @see javafe.ast.VisitorArgResult#visitBinaryExpr(javafe.ast.BinaryExpr, java.lang.Object)
   */
  public final Object visitBinaryExpr(final /*@non_null*/ BinaryExpr expr, final Object o) {
    if (((Boolean) ((Properties) o).get("interesting")).booleanValue()) {
      switch(expr.op) {
        case TagConstants.EQ: 
          return this.fTranslator.eq(expr, o);
        case TagConstants.OR: 
          return this.fTranslator.or(expr, o);
        case TagConstants.AND: 
          return this.fTranslator.and(expr, o);
        case TagConstants.NE:
          return this.fTranslator.ne(expr, o);
        case TagConstants.GE: 
          return this.fTranslator.ge(expr, o);
        case TagConstants.GT: 
          return this.fTranslator.gt(expr, o);
        case TagConstants.LE: 
          return this.fTranslator.le(expr, o);
        case TagConstants.LT:  
          return this.fTranslator.lt(expr, o);
        case TagConstants.BITOR: 
          return this.fTranslator.bitor(expr, o);
        case TagConstants.BITXOR: 
          return this.fTranslator.bitxor(expr, o);
        case TagConstants.BITAND: 
          return this.fTranslator.bitand(expr, o);
        case TagConstants.LSHIFT:
          return this.fTranslator.lshift(expr, o);
        case TagConstants.RSHIFT: 
          return this.fTranslator.rshift(expr, o);
        case TagConstants.URSHIFT:
          return this.fTranslator.urshift(expr, o);
        case TagConstants.ADD: 
          return this.fTranslator.add(expr, o);
        case TagConstants.SUB: 
          return this.fTranslator.sub(expr, o);
        case TagConstants.DIV: 
          return this.fTranslator.div(expr, o);
        case TagConstants.MOD: 
          return this.fTranslator.mod(expr, o);
        case TagConstants.STAR: 
          return this.fTranslator.star(expr, o);
        case TagConstants.ASSIGN:
          return this.fTranslator.assign(expr, o);
        case TagConstants.ASGMUL: 
          return this.fTranslator.asgmul(expr, o);
        case TagConstants.ASGDIV: 
          return this.fTranslator.asgdiv(expr, o);
        case TagConstants.ASGREM: 
          return this.fTranslator.asgrem(expr, o);
        case TagConstants.ASGADD: 
          return this.fTranslator.asgadd(expr, o);
        case TagConstants.ASGSUB: 
          return this.fTranslator.asgsub(expr, o);
        case TagConstants.ASGLSHIFT: 
          return this.fTranslator.asglshift(expr, o);
        case TagConstants.ASGRSHIFT: 
          return this.fTranslator.asgrshift(expr, o);
        case TagConstants.ASGURSHIFT: 
          return this.fTranslator.asgurshif(expr, o);
        case TagConstants.ASGBITAND: 
          return this.fTranslator.asgbitand(expr, o);
          // jml specific operators 
        case TagConstants.IMPLIES: 
          return this.fTranslator.implies(expr, o);
        case TagConstants.EXPLIES:
          return this.fTranslator.explies(expr, o);
        case TagConstants.IFF: // equivalence (equality)
          return this.fTranslator.iff(expr, o);
        case TagConstants.NIFF:    // discrepance (xor)
          return this.fTranslator.niff(expr, o);
        case TagConstants.SUBTYPE: 
          return this.fTranslator.subtype(expr, o);
        case TagConstants.DOTDOT: 
          return this.fTranslator.dotdot(expr, o);
  
        default:
          throw new IllegalArgumentException("Unknown construct :" +
                                             TagConstants.toString(expr.op) +
                                             " " +  expr);
      }
    } 
    else {
      return null;
    }
  }

  /* (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitAnOverview(escjava.ast.AnOverview, java.lang.Object)
   */
  public final Object visitAnOverview(final /*@non_null*/ AnOverview x, final Object o) {
    return null;
  }  

  /**
   * @param o Properties object also containing all modifiable types.
   * @return Returns a term that says that all invariants have to hold.
   */
  public Object invToPreconditions(final /*@non_null*/ Object o) {
    final QuantVariableRef x = Expression.rvar(Ref.sort);
    final QuantVariableRef type = Expression.rvar(Type.sort);
    final QuantVariable[] vars = {x.qvar, type.qvar};
    final Term invTerm = Logic.inv(x, type);
    final Term typeOfTerm = Logic.assignCompat(Heap.var, x, type);
    final Term allocTerm = Logic.isAllocated(Heap.var, x);
    final Term andTerm = Logic.and(allocTerm, typeOfTerm);
    final Term implTerm = Logic.implies(andTerm, invTerm);
    final Term forAllTerm = Logic.forall(vars, implTerm);
    return forAllTerm;
  }



  /**
   * @param o Properties object also containing all modifiable types.
   * @return Returns a Term containing the invariants that have to be checked
   * at the end of a method.
   */
  public Object invToPostconditions(final /*@non_null*/ Object o) { 
    final QuantVariableRef x = Expression.rvar(Ref.sort);
    final QuantVariableRef type = Expression.rvar(Type.sort);
    final QuantVariable[] vars = {x.qvar, type.qvar}; 
    final Term invTerm = Logic.inv(x, type);
    final Term typeOfTerm = Logic.assignCompat(Heap.var , x, type);
    final Term allocTerm = Logic.isAllocated(Heap.var, x);
    final Term visibleTerm = Logic.isVisibleIn(type, o);
    Term andTerm = Logic.and(allocTerm, typeOfTerm);
    andTerm = Logic.and(andTerm, visibleTerm);
    final Term implTerm = Logic.implies(andTerm, invTerm);
    final Term forAllTerm = Logic.forall(vars, implTerm);
    return forAllTerm;
  }

  
  /**
   * Adds a Term to the routines postcondition describing all assignable variables
   * @param o Properties object also containing all assignable variables
   */
  private void doAssignable(final Object o) {
    final HashSet fAssignable    = (HashSet) ((Properties) o).get("assignableSet");
    
    if (((Boolean) ((Properties) o).get("nothing")).booleanValue() | !fAssignable.isEmpty())
    {
      final RoutineDecl rd = (RoutineDecl)((Properties) o).get("method");
      Post allPosts = Lookup.postconditions.get(rd);
      Term forAllTerm = null;
      final QuantVariableRef targetVar = Expression.rvar(Ref.sort); 
      //    FIXME: sortAny should be available (now deprecated in Formula.sort)
      final QuantVariableRef fieldVar = Expression.rvar(Formula.sort);
      final Term equalsTerm = Logic.equals(Heap.select(Heap.varPre, (Term) targetVar, fieldVar.qvar), Heap.select(Heap.var, (Term) targetVar, fieldVar.qvar)); //gibt noch kein any
      final QuantVariable[] vars = {targetVar.qvar, fieldVar.qvar}; 
      Term assigTerm = Logic.not(Logic.isAllocated(Heap.varPre, targetVar));
      if (!fAssignable.isEmpty()) {
        assigTerm = Logic.or(assigTerm, Logic.isAssignable((Term) targetVar, fieldVar, o));       
      }
      assigTerm = Logic.or(assigTerm, equalsTerm); 
      forAllTerm = Logic.forall(vars, assigTerm);
      //    FIXME jgc: I don't know if fVar should be needed here; needs a review
      allPosts = new Post(allPosts.getRVar(), Logic.and(allPosts.getPost(), forAllTerm));
      Lookup.postconditions.put(rd, allPosts);
     ((Properties) o).put("nothing", Boolean.FALSE); //set default values for next routine
     ((Properties) o).put("assignableSet", new HashSet<QuantVariableRef>()); 
    } 
  }


}
