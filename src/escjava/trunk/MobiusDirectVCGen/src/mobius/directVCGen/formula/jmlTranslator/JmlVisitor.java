package mobius.directVCGen.formula.jmlTranslator;

import mobius.directVCGen.formula.Expression;
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

import java.util.Properties;
import java.util.Vector;
import javafe.ast.ASTNode;
import javafe.ast.BinaryExpr;
import javafe.ast.BlockStmt;
import javafe.ast.ClassDecl;
import javafe.ast.ConstructorDecl;
import javafe.ast.DoStmt;
import javafe.ast.FieldAccess;
import javafe.ast.ForStmt;
import javafe.ast.FormalParaDecl;
import javafe.ast.IfStmt;
import javafe.ast.InstanceOfExpr;
import javafe.ast.LiteralExpr;
import javafe.ast.LocalVarDecl;
import javafe.ast.MethodDecl;
import javafe.ast.ModifierPragma;
import javafe.ast.RoutineDecl;
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
  private JmlExprToFormula fTranslator;
  /**
   * Properties that are passed as argument of the visitor.
   */
  private Properties fProperties;

  /**
   * Visitor that translates JML Constructs to FOL by using JmlExprToFormula to
   * translate expressions.
   */
  public JmlVisitor() {
    fProperties = new Properties();
    fProperties.put("pred", new Boolean(true));
    fProperties.put("old", new Boolean(false));
    fProperties.put("interesting", new Boolean(false));
    fTranslator = new JmlExprToFormula(this);
  }

  /* (non-Javadoc)
   * @see javafe.ast.VisitorArgResult#visitASTNode(javafe.ast.ASTNode, java.lang.Object)
   */
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
  public final Object visitClassDecl(final /*@non_null*/ ClassDecl x, final Object o) {
    //Use default properties to start with.
    return visitTypeDecl(x, fProperties);
  }

  /* (non-Javadoc 
   * @see javafe.ast.VisitorArgResult#visitRoutineDecl(javafe.ast.RoutineDecl, java.lang.Object)
   */
  public final Object visitRoutineDecl(final /*@non_null*/ RoutineDecl x, final Object o) {
    x.accept(new VisibleTypeCollector(), o); // Visible Type Collector
    ((Properties) o).put("method", x);
    //  invariante wird nur einmal zu Lookup.postcond angehängt
    ((Properties) o).put("firstPost", new Boolean(true));
    ((Properties) o).put("routinebegin", new Boolean(true));
    final QuantVariableRef result = (QuantVariableRef) ((Properties) o).get("result");
    Lookup.postconditions.put(x, new Post(result, Logic.True()));
    Lookup.exceptionalPostconditions.put(x, new Post(result, Logic.True()));
    return visitASTNode(x, o);
  }

  /* (non-Javadoc)
   * @see javafe.ast.VisitorArgResult#visitMethodDecl(javafe.ast.MethodDecl, java.lang.Object)
   */
  public final Object visitMethodDecl(final /*@non_null*/ MethodDecl x, final Object o) {
    ((Properties) o).put("result", Expression.rvar(Expression.getResultVar(x)));
    return visitRoutineDecl(x, o);
  }

  /* (non-Javadoc)
   * @see javafe.ast.VisitorArgResult#visitConstructorDecl(javafe.ast.ConstructorDecl, java.lang.Object)
   */
  public final Object visitConstructorDecl(final /*@non_null*/ ConstructorDecl x, final Object o) {
    return visitRoutineDecl(x, o);
  }

  /* (non-Javadoc)
   * @see javafe.ast.VisitorArgResult#visitFormalParaDecl(javafe.ast.FormalParaDecl, java.lang.Object)
   */
  public final Object visitFormalParaDecl(final /*@non_null*/ FormalParaDecl x, final Object o) {
    return fTranslator.genericVarDecl(x, o);
  }

  /* (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitAnOverview(escjava.ast.AnOverview, java.lang.Object)
   */
  public final Object visitAnOverview(final /*@non_null*/ AnOverview x, final Object o) {
    return null;
  }

  /* (non-Javadoc)
   * @see javafe.ast.VisitorArgResult#visitLiteralExpr(javafe.ast.LiteralExpr, java.lang.Object)
   */
  public final Object visitLiteralExpr(final /*@non_null*/ LiteralExpr x, final Object o) {
    final Properties prop = (Properties) o;
    if (((Boolean) prop.get("interesting")).booleanValue()) {
      return fTranslator.literal(x, o);
    }
    else {
      return null;
    }
  }

  /* (non-Javadoc)
   * @see javafe.ast.VisitorArgResult#visitVariableAccess(javafe.ast.VariableAccess, java.lang.Object)
   */
  public final Object visitVariableAccess(final /*@non_null*/ VariableAccess x, final Object o) {
    if (((Boolean) ((Properties) o).get("interesting")).booleanValue()) {
      return fTranslator.variableAccess(x, o);
    }
    else {
      return null;
    }
  }

  /* (non-Javadoc)
   * @see javafe.ast.VisitorArgResult#visitFieldAccess(javafe.ast.FieldAccess, java.lang.Object)
   */
  public final Object visitFieldAccess(final /*@non_null*/ FieldAccess x, final Object o) {
    if (((Boolean) ((Properties) o).get("interesting")).booleanValue()) {
      return fTranslator.fieldAccess(x, o);
    }
    else {
      return null;
    }
  }

  /* (non-Javadoc)
   * @see javafe.ast.VisitorArgResult#visitLocalVarDecl(javafe.ast.LocalVarDecl, java.lang.Object)
   */
  public Object visitLocalVarDecl(final /*@non_null*/ LocalVarDecl x, final Object o) {
    return null;
  }

  /* (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitNaryExpr(escjava.ast.NaryExpr, java.lang.Object)
   */
  public final Object visitNaryExpr(final /*@non_null*/ NaryExpr x, final Object o) {
    if (((Boolean) ((Properties) o).get("interesting")).booleanValue()) {
      if (x.op == TagConstants.PRE) {
        return fTranslator.naryExpr(x, o);
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
  public final Object visitInstanceOfExpr(final /*@non_null*/ InstanceOfExpr x, final Object o) {
    if (((Boolean) ((Properties) o).get("interesting")).booleanValue()) {
      return fTranslator.instanceOfExpr(x, o);
    }
    else {
      return null;
    }
  }

  /* (non-Javadoc)
   * @see javafe.ast.VisitorArgResult#visitThisExpr(javafe.ast.ThisExpr, java.lang.Object)
   */
  public final Object visitThisExpr(final /*@non_null*/ ThisExpr x, final Object o) {
    if (((Boolean) ((Properties) o).get("interesting")).booleanValue()) {
      return fTranslator.thisLiteral(x, o);
    }
    else {
      return null;
    }
  }

  /* (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitArrayRangeRefExpr(escjava.ast.ArrayRangeRefExpr, java.lang.Object)
   */
  public final Object visitArrayRangeRefExpr(final /*@non_null*/ ArrayRangeRefExpr x, final Object o) {
    // TODO Auto-generated method stub
    return null;
  }

  /* (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitCondExprModifierPragma(escjava.ast.CondExprModifierPragma, java.lang.Object)
   */
  public final Object visitCondExprModifierPragma(final /*@non_null*/ CondExprModifierPragma x, final Object o) {
    // TODO Auto-generated method stub
    //return null;
    return visitASTNode(x, o);
  }

  /* (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitCondition(escjava.ast.Condition, java.lang.Object)
   */
  public final Object visitCondition(final /*@non_null*/ Condition x, final Object o) {
    // TODO Auto-generated method stub
    return null;
  }

  /* (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitDecreasesInfo(escjava.ast.DecreasesInfo, java.lang.Object)
   */
  public final Object visitDecreasesInfo(final /*@non_null*/ DecreasesInfo x, final Object o) {
    // TODO Auto-generated method stub
    return null;
  }

  /* (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitDefPred(escjava.ast.DefPred, java.lang.Object)
   */
  public final Object visitDefPred(final /*@non_null*/ DefPred x, final Object o) {
    // TODO Auto-generated method stub
    return null;
  }

  /* (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitDefPredApplExpr(escjava.ast.DefPredApplExpr, java.lang.Object)
   */
  public final Object visitDefPredApplExpr(final /*@non_null*/ DefPredApplExpr x, final Object o) {
    // TODO Auto-generated method stub
    return null;
  }

  /* (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitDefPredLetExpr(escjava.ast.DefPredLetExpr, java.lang.Object)
   */
  public final Object visitDefPredLetExpr(final /*@non_null*/ DefPredLetExpr x, final Object o) {
    // TODO Auto-generated method stub
    return null;
  }

  /* (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitDependsPragma(escjava.ast.DependsPragma, java.lang.Object)
   */
  public final Object visitDependsPragma(final /*@non_null*/ DependsPragma x, final Object o) {
    // TODO Auto-generated method stub
    return null;
  }

  /* (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitEscPrimitiveType(escjava.ast.EscPrimitiveType, java.lang.Object)
   */
  public final Object visitEscPrimitiveType(final /*@non_null*/ EscPrimitiveType x, final Object o) {
    // TODO Auto-generated method stub
    return null;
  }

  /* (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitEverythingExpr(escjava.ast.EverythingExpr, java.lang.Object)
   */
  public final Object visitEverythingExpr(final /*@non_null*/ EverythingExpr x, final Object o) {
    // TODO Auto-generated method stub
    //return null;
    return visitASTNode(x, o);
  }

  /* (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitExprDeclPragma(escjava.ast.ExprDeclPragma, java.lang.Object)
   */
  public final Object visitExprDeclPragma(final /*@non_null*/ ExprDeclPragma x, final Object o) {
    // TODO Auto-generated method stub
    return null;
  }

  /* (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitExprModifierPragma(escjava.ast.ExprModifierPragma, java.lang.Object)
   */
  public final Object visitExprModifierPragma(final /*@non_null*/ ExprModifierPragma x, final Object o) {
    ((Properties) o).put("interesting", new Boolean(true));
    final RoutineDecl rd = (RoutineDecl)((Properties) o).get("method");
    Term t = (Term)visitASTNode(x, o);
    switch (x.getTag()) {
      case TagConstants.REQUIRES:
        if (rd  instanceof MethodDecl) { 
          final Term invToPre = (Term) invToPreconditions(o);
          t = Logic.Safe.and(t, invToPre);
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
          ((Properties) o).put("firstPost", new Boolean(false));
        }
        Lookup.postconditions.put(rd, allPosts);
        break;
      default:
        break;
    }
    return null;
  }

  /* (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitVarExprModifierPragma(escjava.ast.VarExprModifierPragma, java.lang.Object)
   */
  public final Object visitVarExprModifierPragma(final /*@non_null*/ VarExprModifierPragma x, final Object o) {
    ((Properties) o).put("interesting", new Boolean(true));

    RoutineDecl currentRoutine = (RoutineDecl)((Properties) o).get("method");
    Post allExPosts = Lookup.exceptionalPostconditions.get(currentRoutine);
    QuantVariableRef commonExceptionVar = allExPosts.getRVar();

    Term typeOfException = Type.translate(x.arg.type);
    QuantVariableRef newExceptionVar = Expression.rvar(x.arg);

    Term newExPost = (Term)x.expr.accept(this, o);
    newExPost = newExPost.subst(newExceptionVar, commonExceptionVar);
    Term  guard = Logic.assignCompat(Heap.var, commonExceptionVar,typeOfException);
    Term result = Logic.Safe.implies(guard, newExPost);
    allExPosts = new Post(allExPosts.getRVar(), Logic.and(allExPosts.getPost(), result));
    Lookup.exceptionalPostconditions.put(currentRoutine, allExPosts);


    return null;
  }

  /* (non-Javadoc)
   * @see javafe.ast.VisitorArgResult#visitBlockStmt(javafe.ast.BlockStmt, java.lang.Object)
   */
  public final Object visitBlockStmt(final /*@non_null*/ BlockStmt x, final Object o) {
    Term t = null;
    Term t1 = null;
    Term t2 = null;
    Set  set = null;
    Set.Assignment assignment = null;
    boolean interesting;
    Vector<AAnnotation> annos = new Vector<AAnnotation>();
    Term inv = null;

    //Save arguments values in prestate as ghosts.
    if (((Boolean)((Properties) o).get("routinebegin")).booleanValue()){
      ((Properties) o).put("routinebegin", new Boolean(false));
      RoutineDecl m = (RoutineDecl) ((Properties) o).get("method");
      for(FormalParaDecl p: m.args.toArray()){
        t1 = Expression.rvar(p);
        t2 = Expression.old(p);
        assignment = new Set.Assignment((QuantVariableRef) t2, t1);
        annos.add(new Set((QuantVariableRef) t2, assignment)); 
      }
    }

    //
    for(Stmt s: x.stmts.toArray()){
      interesting = false;
      //We are interested in Asserts, Assumes and Loop Invariants
      if (s instanceof ExprStmtPragma){
        interesting = true; 
        ((Properties) o).put("interesting", new Boolean(true));
        t = (Term)s.accept(this, o);
        switch (s.getTag()){
        case TagConstants.ASSERT:
          annos.add(new Cut(t));
          break;
        case TagConstants.ASSUME:
          annos.add(new Assume(t));
          break;
        case TagConstants.LOOP_INVARIANT:
        case TagConstants.MAINTAINING:
          inv = t;
          break;
        }
      } else

        //We are also interested in ghost var declarations
        if (s instanceof VarDeclStmt){

          for (ModifierPragma p: ((VarDeclStmt) s).decl.pmodifiers.toArray()){
            if (p.getTag() == TagConstants.GHOST) {
              interesting = true;
              break;
            }
          }
          if (interesting){
            ((Properties) o).put("interesting", new Boolean(true));
            t = (Term)s.accept(this, o);
            Set ghostVar = new Set();
            ghostVar.declaration = (QuantVariableRef) t;
            annos.add(ghostVar);
          }
        } else

          //Also set statements should be processed
          if (s instanceof SetStmtPragma) {
            interesting = true;
            ((Properties) o).put("interesting", new Boolean(true));
            assignment = (Set.Assignment)s.accept(this, o);
            set = new Set();
            set.assignment = assignment;
            annos.add(set);
          }

      if (interesting){
        x.stmts.removeElement(s);
      } else {
        ((Properties) o).put("interesting", new Boolean(false));
        if (!annos.isEmpty()){
          AnnotationDecoration.inst.setAnnotPre(s, annos);
          annos.clear();
        }
        if (inv != null){
          if (s instanceof WhileStmt || 
              s instanceof ForStmt || 
              s instanceof DoStmt){
            AnnotationDecoration.inst.setInvariant(s, inv);
            inv = null;
          }
        }	
        if (s instanceof WhileStmt || 
            s instanceof ForStmt || 
            s instanceof DoStmt || 
            s instanceof BlockStmt || 
            s instanceof TryCatchStmt ||
            s instanceof IfStmt){
          s.accept(this,o);
        }	
      }
    }
    return null;
  }	

  /* (non-Javadoc)
   * @see javafe.ast.VisitorArgResult#visitVarDeclStmt(javafe.ast.VarDeclStmt, java.lang.Object)
   */
  public final Object visitVarDeclStmt(final /*@non_null*/ VarDeclStmt x, final Object o) {
    //It's only called if we have a ghost variable declaration
    return Expression.rvar(x.decl);
  }	

  /* (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitExprStmtPragma(escjava.ast.ExprStmtPragma, java.lang.Object)
   */
  public final Object visitExprStmtPragma(final /*@non_null*/ ExprStmtPragma x, final Object o) {
    // TODO Auto-generated method stub
    return visitASTNode(x, o);
  }

  /* (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitGCExpr(escjava.ast.GCExpr, java.lang.Object)
   */
  public final Object visitGCExpr(final /*@non_null*/ GCExpr x, final Object o) {
    return visitASTNode(x, o);
  }

  /* (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitGhostDeclPragma(escjava.ast.GhostDeclPragma, java.lang.Object)
   */
  public final Object visitGhostDeclPragma(final /*@non_null*/ GhostDeclPragma x, final Object o) {
    // TODO Auto-generated method stub
    return null;
  }

  /* (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitGuardExpr(escjava.ast.GuardExpr, java.lang.Object)
   */
  public final Object visitGuardExpr(final /*@non_null*/ GuardExpr x, final Object o) {
    // TODO Auto-generated method stub
    return null;
  }

  /* (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitGuardedCmd(escjava.ast.GuardedCmd, java.lang.Object)
   */
  public final Object visitGuardedCmd(final /*@non_null*/ GuardedCmd x, final Object o) {
    // TODO Auto-generated method stub
    return null;
  }

  /* (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitIdExprDeclPragma(escjava.ast.IdExprDeclPragma, java.lang.Object)
   */
  public final Object visitIdExprDeclPragma(final /*@non_null*/ IdExprDeclPragma x, final Object o) {
    // TODO Auto-generated method stub
    return null;
  }

  
  /* (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitIdentifierModifierPragma(escjava.ast.IdentifierModifierPragma, java.lang.Object)
   */
  public final Object visitIdentifierModifierPragma(final /*@non_null*/ IdentifierModifierPragma x, final Object o) {
    // TODO Auto-generated method stub
    return null;
  }

  
  /* (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitImportPragma(escjava.ast.ImportPragma, java.lang.Object)
   */
  public final Object visitImportPragma(final /*@non_null*/ ImportPragma x, final Object o) {
    // TODO Auto-generated method stub
    //return null;
    return visitASTNode(x, o);
  }

  
  /* (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitLockSetExpr(escjava.ast.LockSetExpr, java.lang.Object)
   */
  public final Object visitLockSetExpr(final /*@non_null*/ LockSetExpr x, final Object o) {
    // TODO Auto-generated method stub
    return null;
  }

  
  /* (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitMapsExprModifierPragma(escjava.ast.MapsExprModifierPragma, java.lang.Object)
   */
  public final Object visitMapsExprModifierPragma(final /*@non_null*/ MapsExprModifierPragma x, final Object o) {
    // TODO Auto-generated method stub
    return null;
  }

  
  /* (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitModelConstructorDeclPragma(escjava.ast.ModelConstructorDeclPragma, java.lang.Object)
   */
  public final Object visitModelConstructorDeclPragma(final /*@non_null*/ ModelConstructorDeclPragma x, final Object o) {
    // TODO Auto-generated method stub
    return null;
  }

  
  /* (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitModelDeclPragma(escjava.ast.ModelDeclPragma, java.lang.Object)
   */
  public final Object visitModelDeclPragma(final /*@non_null*/ ModelDeclPragma x, final Object o) {
    // TODO Auto-generated method stub
    return null;
  }

  
  /* (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitModelMethodDeclPragma(escjava.ast.ModelMethodDeclPragma, java.lang.Object)
   */
  public final Object visitModelMethodDeclPragma(final /*@non_null*/ ModelMethodDeclPragma x, final Object o) {
    // TODO Auto-generated method stub
    return null;
  }

  
  /* (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitModelProgamModifierPragma(escjava.ast.ModelProgamModifierPragma, java.lang.Object)
   */
  public final Object visitModelProgamModifierPragma(final /*@non_null*/ ModelProgamModifierPragma x, final Object o) {
    // TODO Auto-generated method stub
    return null;
  }

  
  /* (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitModelTypePragma(escjava.ast.ModelTypePragma, java.lang.Object)
   */
  public final Object visitModelTypePragma(final /*@non_null*/ ModelTypePragma x, final Object o) {
    // TODO Auto-generated method stub
    return null;
  }

  
  /* (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitModifiesGroupPragma(escjava.ast.ModifiesGroupPragma, java.lang.Object)
   */
  public final Object visitModifiesGroupPragma(final /*@non_null*/ ModifiesGroupPragma x, final Object o) {
    // TODO Auto-generated method stub
    //return null;
    return visitASTNode(x, o);
  }

  
  /* (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitNamedExprDeclPragma(escjava.ast.NamedExprDeclPragma, java.lang.Object)
   */
  public final Object visitNamedExprDeclPragma(final /*@non_null*/ NamedExprDeclPragma x, final Object o) {
    // TODO Auto-generated method stub
    return null;
  }

  
  /* (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitNestedModifierPragma(escjava.ast.NestedModifierPragma, java.lang.Object)
   */
  public final Object visitNestedModifierPragma(final /*@non_null*/ NestedModifierPragma x, final Object o) {
    // TODO Auto-generated method stub
    return null;
  }

  
  /* (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitNotModifiedExpr(escjava.ast.NotModifiedExpr, java.lang.Object)
   */
  public final Object visitNotModifiedExpr(final /*@non_null*/ NotModifiedExpr x, final Object o) {
    // TODO Auto-generated method stub
    return null;
  }

  
  /* (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitNotSpecifiedExpr(escjava.ast.NotSpecifiedExpr, java.lang.Object)
   */
  public final Object visitNotSpecifiedExpr(final /*@non_null*/ NotSpecifiedExpr x, final Object o) {
    // TODO Auto-generated method stub
    return null;
  }

  
  /* (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitNothingExpr(escjava.ast.NothingExpr, java.lang.Object)
   */
  public final Object visitNothingExpr(final /*@non_null*/ NothingExpr x, final Object o) {
    // TODO Auto-generated method stub
    return null;
  }

  
  /* (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitNowarnPragma(escjava.ast.NowarnPragma, java.lang.Object)
   */
  public final Object visitNowarnPragma(final /*@non_null*/ NowarnPragma x, final Object o) {
    // TODO Auto-generated method stub
    return null;
  }

  
  /* (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitParsedSpecs(escjava.ast.ParsedSpecs, java.lang.Object)
   */
  public final Object visitParsedSpecs(final /*@non_null*/ ParsedSpecs x, final Object o) {
    // TODO Auto-generated method stub
    //return visitASTNode(x, o); //generates a stack overflow... but should be used
    return null;
  }

  
  /* (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitReachModifierPragma(escjava.ast.ReachModifierPragma, java.lang.Object)
   */
  public final Object visitReachModifierPragma(final /*@non_null*/ ReachModifierPragma x, final Object o) {
    // TODO Auto-generated method stub
    return null;
  }

  
  /* (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitRefinePragma(escjava.ast.RefinePragma, java.lang.Object)
   */
  public final Object visitRefinePragma(final /*@non_null*/ RefinePragma x, final Object o) {
    // TODO Auto-generated method stub
    return null;
  }

  
  /* (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitResExpr(escjava.ast.ResExpr, java.lang.Object)
   */
  public final Object visitResExpr(final /*@non_null*/ ResExpr x, final Object o) {
    if (((Boolean) ((Properties) o).get("interesting")).booleanValue())
      return fTranslator.resultLiteral(x,o);
    else
      return null;
  }

  
  /* (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitSetCompExpr(escjava.ast.SetCompExpr, java.lang.Object)
   */
  public final Object visitSetCompExpr(final /*@non_null*/ SetCompExpr x, final Object o) {
    // TODO Auto-generated method stub
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
    // TODO Auto-generated method stub
    return null;
  }

  
  /* (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitSimpleStmtPragma(escjava.ast.SimpleStmtPragma, java.lang.Object)
   */
  public final Object visitSimpleStmtPragma(final /*@non_null*/ SimpleStmtPragma x, final Object o) {
    // TODO Auto-generated method stub
    return null;
  }

  
  /* (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitSkolemConstantPragma(escjava.ast.SkolemConstantPragma, java.lang.Object)
   */
  public final Object visitSkolemConstantPragma(final /*@non_null*/ SkolemConstantPragma x, final Object o) {
    // TODO Auto-generated method stub
    return null;
  }

  
  /* (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitSpec(escjava.ast.Spec, java.lang.Object)
   */
  public final Object visitSpec(final /*@non_null*/ Spec x, final Object o) {
    // TODO Auto-generated method stub
    return null;
  }

  
  /* (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitStillDeferredDeclPragma(escjava.ast.StillDeferredDeclPragma, java.lang.Object)
   */
  public final Object visitStillDeferredDeclPragma(final /*@non_null*/ StillDeferredDeclPragma x, final Object o) {
    // TODO Auto-generated method stub
    return null;
  }

  
  /* (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitVarDeclModifierPragma(escjava.ast.VarDeclModifierPragma, java.lang.Object)
   */
  public final Object visitVarDeclModifierPragma(final /*@non_null*/ VarDeclModifierPragma x, final Object o) {
    // TODO Auto-generated method stub
    return null;
  }

  
  /* (non-Javadoc)
   * @see escjava.ast.VisitorArgResult#visitWildRefExpr(escjava.ast.WildRefExpr, java.lang.Object)
   */
  public final Object visitWildRefExpr(final /*@non_null*/ WildRefExpr x, final Object o) {
    // TODO Auto-generated method stub
    return null;
  }


  
  /* (non-Javadoc)
   * @see javafe.ast.VisitorArgResult#visitBinaryExpr(javafe.ast.BinaryExpr, java.lang.Object)
   */
  public final Object visitBinaryExpr(final /*@non_null*/ BinaryExpr expr, final Object o) {
    if (((Boolean) ((Properties) o).get("interesting")).booleanValue()) {
      switch(expr.op) {
        case TagConstants.EQ: 
          return fTranslator.eq(expr, o);
        case TagConstants.OR: 
          return fTranslator.or(expr, o);
        case TagConstants.AND: 
          return fTranslator.and(expr, o);
        case TagConstants.NE:
          return fTranslator.ne(expr, o);
        case TagConstants.GE: 
          return fTranslator.ge(expr, o);
        case TagConstants.GT: 
          return fTranslator.gt(expr, o);
        case TagConstants.LE: 
          return fTranslator.le(expr, o);
        case TagConstants.LT:  
          return fTranslator.lt(expr, o);
        case TagConstants.BITOR: 
          return fTranslator.bitor(expr, o);
        case TagConstants.BITXOR: 
          return fTranslator.bitxor(expr, o);
        case TagConstants.BITAND: 
          return fTranslator.bitand(expr, o);
        case TagConstants.LSHIFT:
          return fTranslator.lshift(expr, o);
        case TagConstants.RSHIFT: 
          return fTranslator.rshift(expr, o);
        case TagConstants.URSHIFT:
          return fTranslator.urshift(expr, o);
        case TagConstants.ADD: 
          return fTranslator.add(expr, o);
        case TagConstants.SUB: 
          return fTranslator.sub(expr, o);
        case TagConstants.DIV: 
          return fTranslator.div(expr, o);
        case TagConstants.MOD: 
          return fTranslator.mod(expr, o);
        case TagConstants.STAR: 
          return fTranslator.star(expr, o);
        case TagConstants.ASSIGN:
          return fTranslator.assign(expr, o);
        case TagConstants.ASGMUL: 
          return fTranslator.asgmul(expr, o);
        case TagConstants.ASGDIV: 
          return fTranslator.asgdiv(expr, o);
        case TagConstants.ASGREM: 
          return fTranslator.asgrem(expr, o);
        case TagConstants.ASGADD: 
          return fTranslator.asgadd(expr, o);
        case TagConstants.ASGSUB: 
          return fTranslator.asgsub(expr, o);
        case TagConstants.ASGLSHIFT: 
          return fTranslator.asglshift(expr, o);
        case TagConstants.ASGRSHIFT: 
          return fTranslator.asgrshift(expr, o);
        case TagConstants.ASGURSHIFT: 
          return fTranslator.asgurshif(expr, o);
        case TagConstants.ASGBITAND: 
          return fTranslator.asgbitand(expr, o);
          // jml specific operators 
        case TagConstants.IMPLIES: 
          return fTranslator.implies(expr, o);
        case TagConstants.EXPLIES:
          return fTranslator.explies(expr, o);
        case TagConstants.IFF: // equivalence (equality)
          return fTranslator.iff(expr, o);
        case TagConstants.NIFF:    // discrepance (xor)
          return fTranslator.niff(expr, o);
        case TagConstants.SUBTYPE: 
          return fTranslator.subtype(expr, o);
        case TagConstants.DOTDOT: 
          return fTranslator.dotdot(expr, o);
  
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



}
