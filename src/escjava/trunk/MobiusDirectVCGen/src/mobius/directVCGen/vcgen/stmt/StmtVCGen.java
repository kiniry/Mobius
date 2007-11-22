package mobius.directVCGen.vcgen.stmt;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Vector;

import javafe.ast.ASTNode;
import javafe.ast.ArrayInit;
import javafe.ast.AssertStmt;
import javafe.ast.BlockStmt;
import javafe.ast.BreakStmt;
import javafe.ast.CatchClause;
import javafe.ast.CatchClauseVec;
import javafe.ast.ConstructorInvocation;
import javafe.ast.ContinueStmt;
import javafe.ast.DoStmt;
import javafe.ast.EvalStmt;
import javafe.ast.ExprVec;
import javafe.ast.ForStmt;
import javafe.ast.FormalParaDecl;
import javafe.ast.FormalParaDeclVec;
import javafe.ast.Identifier;
import javafe.ast.IfStmt;
import javafe.ast.LabelStmt;
import javafe.ast.MethodDecl;
import javafe.ast.ReturnStmt;
import javafe.ast.RoutineDecl;
import javafe.ast.SkipStmt;
import javafe.ast.Stmt;
import javafe.ast.StmtPragma;
import javafe.ast.SwitchLabel;
import javafe.ast.SwitchStmt;
import javafe.ast.SynchronizeStmt;
import javafe.ast.ThrowStmt;
import javafe.ast.TryCatchStmt;
import javafe.ast.TryFinallyStmt;
import javafe.ast.VarDeclStmt;
import javafe.ast.VarInit;
import javafe.ast.WhileStmt;
import mobius.directVCGen.formula.Bool;
import mobius.directVCGen.formula.Expression;
import mobius.directVCGen.formula.Heap;
import mobius.directVCGen.formula.Logic;
import mobius.directVCGen.formula.Lookup;
import mobius.directVCGen.formula.Ref;
import mobius.directVCGen.formula.Type;
import mobius.directVCGen.formula.Util;
import mobius.directVCGen.formula.annotation.AAnnotation;
import mobius.directVCGen.formula.annotation.AnnotationDecoration;
import mobius.directVCGen.vcgen.expression.ExpressionVisitor;
import mobius.directVCGen.vcgen.struct.ExcpPost;
import mobius.directVCGen.vcgen.struct.Post;
import mobius.directVCGen.vcgen.struct.VCEntry;
import escjava.ast.ExprStmtPragma;
import escjava.ast.SetStmtPragma;
import escjava.sortedProver.Lifter.QuantVariable;
import escjava.sortedProver.Lifter.QuantVariableRef;
import escjava.sortedProver.Lifter.Term;

/**
 * This class does the weakest precondition calculus for the statements.
 * @author B. Grégoire (benjamin.gregoire@inria.fr), 
 * J. Charles (julien.charles@inria.fr)
 */
public class StmtVCGen extends ExpressionVisitor {
  /** the side conditions that were generated. */
  private List<Term> fVcs = new Vector<Term>();
  
  /** the visitor to visit expressions. */
  private final ExpressionVisitor fExprVisitor = new ExpressionVisitor();
  
  /** the decorator that add the annotations or read the annotations from a node. */
  private final AnnotationDecoration fAnnot = AnnotationDecoration.inst;
  
  /** the current method or constructor that is being inspected. */
  private final RoutineDecl fMeth;

  /** the correspondence from source to bytecode for the variables. */
  private List<QuantVariableRef> fVariables;
  
  
  public List<QuantVariableRef> getVars() {
    return fVariables;
  }

  public StmtVCGen(final RoutineDecl meth, List<QuantVariableRef> variables) {
    fMeth = meth;
    fVariables = variables;
    
  }


  /**
   * The method to treat the annotations.
   * @param vce the current post condition 
   * @param annot the annotation to treat
   * @return a postcondition computed from the annotation
   */
  public Post treatAnnot(final VCEntry vce, final List<AAnnotation> annot) {
    if (annot == null) {
      return vce.fPost;
    }
    Term post = vce.fPost.getPost();
    final int len = annot.size();
    for (int i = len - 1; i >= 0; i--) {
      final AAnnotation aa = annot.get(i);
      switch(aa.getID()) {
        case AAnnotation.annotAssert:
          fVcs.add(Logic.implies(aa.formula, post));
          post = aa.formula;
          break;
        case AAnnotation.annotCut:
          post = Logic.and(aa.formula, Logic.implies(aa.formula, post));
          break;
        case AAnnotation.annotAssume:
          post = Logic.implies(aa.formula, post);
          break;
        case AAnnotation.annotSet: {
          final mobius.directVCGen.formula.annotation.Set s = 
            (mobius.directVCGen.formula.annotation.Set) aa;
          if (s.assignment != null) {
            post.subst(s.assignment.fVar, s.assignment.fExpr);
          }
          else if (s.declaration != null) {
            if (s.assignment == null) {
              post = Logic.forall(s.declaration.qvar, post);
            }
            addVarDecl(s.declaration.qvar);
          }
          break;
        }
  
        case AAnnotation.undef:
        default:
          throw new UnsupportedOperationException(aa.toString());
      }
    }

    return new Post(post);
  }

  @Override
  public /*@non_null*/ Object visitAssertStmt(final /*@non_null*/ AssertStmt x, 
                                              final Object o) {
    // TODO: understand the difference 'tween x.pred and x.IfStmt
    final VCEntry entry = (VCEntry) o;
    Post post = treatAnnot(entry, fAnnot.getAnnotPost(x));
    final QuantVariableRef b  = Expression.rvar(Bool.sort);

    post = new Post(b, Logic.and(b, Logic.implies(b, post.getPost())));
    entry.fPost = post;
    post = (Post)x.pred.accept(fExprVisitor, entry);
    return treatAnnot(entry, fAnnot.getAnnotPre(x));
  }

  // TODO: add comments
  public VCEntry mkEntryBlock (final VCEntry vce) {
    final VCEntry res = new VCEntry(vce);
    res.fBrPost = vce.fPost;
    return res;

  }

  // TODO: add comments
  @Override
  public /*@non_null*/ Object visitBlockStmt(final /*@non_null*/ BlockStmt x, final Object o) {
    final int max = x.childCount();
    VCEntry vce = (VCEntry) o;
    vce = mkEntryBlock(vce);
    vce.fPost = treatAnnot(vce, fAnnot.getAnnotPost(x));

    for (int i = max - 1; i >= 0; i--) {
      final Object child = x.childAt(i);
      if (child instanceof ASTNode) {
        vce.fPost = (Post) ((ASTNode) child).accept(this, vce);
      }
    }
    return treatAnnot(vce, fAnnot.getAnnotPre(x));
  }

  // TODO: add comments
  public Post visitInnerBlockStmt (final /*@non_null*/ Stmt x, final VCEntry vce) {
    if (!(x instanceof BlockStmt)) {
      return (Post)x.accept(this, vce);
    }
    final int max = x.childCount();
    
    // checking that the annotations are null
    List<AAnnotation> tmp = fAnnot.getAnnotPost(x); 
    assert (tmp == null);
    tmp = fAnnot.getAnnotPre(x);
    assert (tmp == null);
    
    for (int i = max - 1; i >= 0; i--) {
      final Object child = x.childAt(i);
      if (child instanceof ASTNode) {
        vce.fPost = (Post) ((ASTNode) child).accept(this, vce);
      }
    }
    return vce.fPost;
  }

  /*
   * (non-Javadoc)
   * @see javafe.ast.VisitorArgResult#visitStmt(javafe.ast.Stmt, java.lang.Object)
   */
  @Override
  public Object visitStmt(final Stmt x, final Object o) {
    throw new IllegalArgumentException("Not yet implememented");
  }



  // TODO: add comments
  public VCEntry mkEntryWhile(final VCEntry ve, final Post inv) {
    final VCEntry res = new VCEntry(ve);
    res.fBrPost = ve.fPost;
    res.fPost = inv;
    res.fContPost = inv;
    return res;
  }

  // TODO: add comments
  public /*@non_null*/ Object visitWhileStmt(final /*@non_null*/ WhileStmt x, final Object o) {
    final VCEntry vce = (VCEntry)o;
    vce.fPost = treatAnnot(vce, fAnnot.getAnnotPost(x));
    final Term inv = Util.getAssertion(fMeth, fAnnot.getInvariant(x));

    
    final Term post = vce.fPost.getPost();
    final Post pinv = new Post(inv);
    final VCEntry vceBody = mkEntryWhile(vce, pinv);
    Post bodypre;
    if (x.stmt instanceof BlockStmt) {
      bodypre = visitInnerBlockStmt((BlockStmt)x.stmt, vceBody);
    }
    else { 
      bodypre = (Post) x.stmt.accept(this, vceBody);
    }

    final QuantVariableRef v = Expression.rvar(Bool.sort);
    vce.fPost = new Post(v,
                        Logic.and(Logic.implies(Logic.boolToPred(v), bodypre.getPost()),
                                  Logic.implies(Logic.not(Logic.boolToPred(v)), post)));
    // the only field that can be modified in a VCentry is post 
    final Term aux = ((Post) x.expr.accept(fExprVisitor, vce)).getPost();
    fVcs.add(Logic.implies(inv, aux));

    vce.fPost = pinv;
    return treatAnnot(vce, fAnnot.getAnnotPre(x));
  }

  // TODO: add comments
  public /*@non_null*/ Object visitEvalStmt(final /*@non_null*/ EvalStmt x, final Object o) {
    final VCEntry vce = (VCEntry) o;
    vce.fPost = treatAnnot(vce, fAnnot.getAnnotPost(x));
    final Post p = vce.fPost;
    vce.fPost = new Post(Expression.rvar(Type.getSort(x.expr)),
                        p.getPost());
    vce.fPost = (Post)x.expr.accept(fExprVisitor, vce);
    return treatAnnot(vce, fAnnot.getAnnotPre(x));
  }

  // TODO: add comments
  @Override
  public /*@non_null*/ Object visitReturnStmt(final /*@non_null*/ ReturnStmt x, 
                                              final Object o) {
    
    // Goog to ensure that x.annotPost == Null
    // and so remove this check
    final List<AAnnotation> tmp = fAnnot.getAnnotPost(x);
    assert (tmp == null); // if the method type is not void there should 
    // also be the variable \result
    
    final VCEntry vce = (VCEntry) o;
    final String name = Util.getMethodAnnotModule(fMeth);
    final Term[] tab = Util.getNormalPostconditionArgs(fMeth);
    final Post normPost = new Post(Lookup.getNormalPostcondition(fMeth).getRVar(), 
                        Expression.sym(name + ".mk_post", tab));

    vce.fPost = normPost;
    vce.fPost = (Post) x.expr.accept(fExprVisitor, vce);
    return treatAnnot(vce, fAnnot.getAnnotPre(x));
  }

  public static Post getExcpPostExact(final Term typ, final VCEntry vce) {
    final Iterator iter = vce.lexcpost.iterator();
    while (iter.hasNext()) {
      final ExcpPost p = (ExcpPost)iter.next();
      if (Type.isSubClassOrEq(typ, p.type)) {
        return p.post;
      }
    }
    return vce.fExcPost;

  }



  // TODO: add comments
  public /*@non_null*/ Object visitThrowStmt(final /*@non_null*/ ThrowStmt x, final Object o) {
    final VCEntry vce = (VCEntry)o;
    vce.fPost = treatAnnot(vce, fAnnot.getAnnotPost(x));
    final Term typ = Type.getTypeName(x.expr);
    vce.fPost = Util.getExcpPost(typ, vce);
    vce.fPost = ((Post)x.expr.accept(fExprVisitor, vce));
    return treatAnnot(vce, fAnnot.getAnnotPre(x));
  }

  /**
   * Return the break postcondition corresponding to the
   * given label.
   * @param label a valid label or null if no label was specified.
   * @param vce the entry where the postcondition for the labels was stocked
   * @return a valid post condition or null if the label was not found
   */
  public static Post getBreakPost(final Identifier label, final VCEntry vce) {
    if (label == null) {
      return vce.fBrPost; 
    }
    return vce.lbrpost.get(label);
  }

  // TODO: add comments
  public /*@non_null*/ Object visitBreakStmt(final /*@non_null*/ BreakStmt x, final Object o) {
    final VCEntry vce = (VCEntry) o;
    // there should be no annot post since it is a control flow exit sttment
    vce.fPost = getBreakPost(x.label, vce);
    return treatAnnot(vce, fAnnot.getAnnotPre(x));
  }

  /**
   * Return the continue postcondition corresponding to the given label.
   * @param label a valid label or null
   * @param vce the entry containing <em>all</em> the postconditions
   * @return the postcondition corresponding to the label or null.
   */
  public static Post getContinuePost(final Identifier label, final VCEntry vce) {
    if (label == null) {
      if (vce.fContPost == null) {
        throw new NullPointerException();
      }
      return vce.fContPost; 
    }
    return vce.lcontpost.get(label);
  }

  // TODO: add comments
  @Override
  public /*@non_null*/ Object visitContinueStmt(final /*@non_null*/ ContinueStmt x, 
                                                final Object o) {
    final VCEntry vce = (VCEntry) o;
    vce.fPost = getContinuePost(x.label, vce);
    return treatAnnot(vce, fAnnot.getAnnotPre(x));
  }

  // TODO: add comments
  public VCEntry mkEntryLoopLabel(final Identifier label, final VCEntry ve, 
                                  final Post continu) {
    final VCEntry res = new VCEntry(ve);
    res.fBrPost = ve.fPost;
    res.fContPost = continu;
    res.lbrpost.put(label, ve.fPost);
    res.lcontpost.put(label, continu);
    return res;
  }

  // TODO: add comments
  @Override
  public /*@non_null*/ Object visitLabelStmt(final /*@non_null*/ LabelStmt x, 
                                             final Object o) {
    final Stmt s = x.stmt;
    VCEntry vce = (VCEntry)o;
    vce.fPost = treatAnnot(vce, fAnnot.getAnnotPost(x));
    
    if (s instanceof WhileStmt || s instanceof DoStmt || s instanceof ForStmt) {
      final Term t =  Util.getAssertion(fMeth, fAnnot.getInvariant(s));
      vce = mkEntryLoopLabel(x.label, vce, new Post(t));
    }
    vce.fPost = (Post) x.stmt.accept(fExprVisitor, vce);
    return treatAnnot(vce, fAnnot.getAnnotPre(x));
  }

  // TODO: add comments
  @Override
  public /*@non_null*/ Object visitIfStmt(final /*@non_null*/ IfStmt x, 
                                          final Object o) {
    final VCEntry vce = (VCEntry) o;
    final Post postBranch = treatAnnot(vce, fAnnot.getAnnotPost(x));
    vce.fPost = postBranch;
    final Post preT = (Post) x.thn.accept(this, vce);
    vce.fPost = postBranch;
    final Post preF = (Post) x.els.accept(this, vce);

    final QuantVariableRef v = Expression.rvar(Bool.sort);

    vce.fPost = new Post(v,
                        Logic.and(Logic.implies(Logic.boolToPred(v), preT.getPost()),
                                  Logic.implies(Logic.not(Logic.boolToPred(v)), 
                                                preF.getPost())));

    vce.fPost = (Post) x.accept(fExprVisitor, vce);
    return treatAnnot(vce, fAnnot.getAnnotPre(x));
  }

  // TODO: add comments
  @Override
  public /*@non_null*/ Object visitSkipStmt(final /*@non_null*/ SkipStmt x, final Object o) {
    final VCEntry vce = (VCEntry) o;
    vce.fPost = treatAnnot(vce, fAnnot.getAnnotPost(x));
    return treatAnnot(vce, fAnnot.getAnnotPre(x));
  }

  // TODO: add comments
  @Override
  public /*@non_null*/ Object visitTryFinallyStmt(final /*@non_null*/ TryFinallyStmt x, 
                                                  final Object o) {
    final VCEntry vce = (VCEntry) o;
    vce.fPost = treatAnnot(vce, fAnnot.getAnnotPost(x));
    final Stmt sTry = x.tryClause;
    final Stmt sFinally = x.finallyClause;
    final VCEntry vcetmp = new VCEntry(vce);
    final Post post = visitInnerBlockStmt(sFinally,  vcetmp);

    // brpost
    vcetmp.fPost = vce.fBrPost;
    final Post brpost = (Post) visitInnerBlockStmt(sFinally,  vcetmp);
    // lbrpost
    final Map<Identifier, Post> lbrpost = new HashMap<Identifier, Post>();
    Set<Identifier> keys = vce.lbrpost.keySet();
    for (Identifier k: keys) {
      vcetmp.fPost = vce.lbrpost.get(k);
      final Post p = visitInnerBlockStmt(sFinally,  vcetmp);
      lbrpost.put(k, p);
    }

    // contpost
    vcetmp.fPost = vce.fContPost;
    final Post contpost = visitInnerBlockStmt(sFinally,  vcetmp);
    //lcontpost
    final Map<Identifier, Post> lcontpost = new HashMap<Identifier, Post>();
    keys = vce.lcontpost.keySet();
    for (Identifier k : keys) {
      vcetmp.fPost = vce.lcontpost.get(k);
      final Post p = visitInnerBlockStmt(sFinally,  vcetmp);
      lcontpost.put(k, p);
    }

    //excpost
    vcetmp.fPost = vce.fExcPost;
    final Post excpost = visitInnerBlockStmt(sFinally,  vcetmp);
    //lexcpost
    final List<ExcpPost> lexcpost = new ArrayList<ExcpPost>();
    for (ExcpPost exc: vce.lexcpost) {
      vcetmp.fPost = exc.post;
      final Post p = visitInnerBlockStmt(sFinally,  vcetmp);
      lexcpost.add(new ExcpPost(exc.type, p));
    }

    final VCEntry entFinally = new VCEntry(post, excpost, brpost, contpost);
    entFinally.lbrpost.putAll(lbrpost);
    entFinally.lcontpost.putAll(lcontpost);
    entFinally.lexcpost.addAll(lexcpost);
    visitInnerBlockStmt(sTry, entFinally);
    return treatAnnot(vce, fAnnot.getAnnotPre(x));
  }

  // TODO: add comments
  @Override
  public /*@non_null*/ Object visitTryCatchStmt(final /*@non_null*/ TryCatchStmt x, 
                                                final Object o) {
    final VCEntry vce = (VCEntry) o;
    vce.fPost = treatAnnot(vce, fAnnot.getAnnotPost(x));
    final CatchClauseVec ccv = x.catchClauses;
    final CatchClause[] catches = ccv.toArray();
    final LinkedList<ExcpPost> l = new LinkedList<ExcpPost>();
    final Post olpost = vce.fPost;
    for (CatchClause c: catches) {
      ExcpPost ep;
      final Term t = Type.translateToType(c.arg.type);
      final QuantVariableRef excp = Expression.rvar(c.arg);
      vce.fPost = olpost;
      Post epost = (Post)c.body.accept(this, vce);
      epost = new Post(excp, epost);
      ep = new ExcpPost(t, epost);
      l.addLast(ep);
    }
    final VCEntry post = new VCEntry(vce);
    post.lexcpost.clear();
    post.lexcpost.addAll(l);
    //System.out.println(l);
    post.lexcpost.addAll(vce.lexcpost);
    vce.fPost = (Post)x.tryClause.accept(this, post);
    //visitInnerBlockStmt(x.tryClause, post);
    return treatAnnot(vce, fAnnot.getAnnotPre(x));
  }

  // TODO: add comments
  @Override
  public /*@non_null*/ Object visitVarDeclStmt(final /*@non_null*/ VarDeclStmt x, 
                                               final Object o) {
    final VCEntry vce = (VCEntry) o;
    vce.fPost = treatAnnot(vce, fAnnot.getAnnotPost(x));
    final VarInit init = x.decl.init;
    //final QuantVariable qv = Expression.var(x.decl);
    if (init != null) {
      final Term var = Expression.rvar(x.decl);
      // the init value replaces the quantification
      final QuantVariableRef val = Expression.rvar(x.decl);
      vce.fPost = new Post(val, Util.substVarWithVal(vce.fPost, var, val));
      vce.fPost = (Post)init.accept(this, vce);
      if (init instanceof ArrayInit) {
        // FIXME should add the array new too
        //vce.fPost = new Post(Logic.forall(qv, vce.fPost.getPost()));
      }

    }
    else {
      final QuantVariableRef qvr = Expression.rvar(x.decl);
      // the quantification is preemptive
      vce.fPost = new Post(vce.fPost.getRVar(), 
                           vce.fPost);
      //vce.fPost = new Post(Logic.forall(qv, vce.fPost.getPost()));
      
    }
    // we must anyway declare it for every vc:
    //addVarDecl(qv);
    return treatAnnot(vce, fAnnot.getAnnotPre(x));
  }



  /**
   * Add the variable to the list of the declared variables.
   * The variable is added to each vcs.
   * @param qv the variable to declare
   */
  private void addVarDecl(final QuantVariable qv) {
    final List<Term> oldvcs = fVcs;

    final QuantVariableRef qvr = Expression.rvar(qv);
    fVcs = new Vector<Term>();
    for (Term t: oldvcs) {
      // the quantification is preemptive
      fVcs.add(t);
      //fVcs.add(Logic.forall(qv, t));
    }

  }


  // TODO: add comments
  // already treated in the try clause
  @Override
  public /*@non_null*/ Object visitCatchClause(final /*@non_null*/ CatchClause x, 
                                               final Object o) {
    return visitASTNode(x, o);
  }




  // TODO: add comments
  @Override
  public /*@non_null*/ Object visitConstructorInvocation(
                                      final /*@non_null*/ ConstructorInvocation ci, 
                                      final Object o) {
    final VCEntry entry = (VCEntry)o;
    final Post normalPost = Lookup.getNormalPostcondition(ci.decl);
    final Post excpPost = Lookup.getExceptionalPostcondition(ci.decl);
    final Term pre = Lookup.getPrecondition(ci.decl);
    final QuantVariableRef newThis = Expression.rvar(Ref.sort);

    // first: the exceptional post
    final QuantVariableRef exc = Expression.rvar(Heap.sortValue);
    final Term tExcp = Logic.forall(exc.qvar, 
               Logic.implies(excpPost.substWith(exc).subst(Ref.varThis, 
                                                           newThis), 
                             Util.getExcpPost(Type.javaLangThrowable(), 
                                                   entry).substWith(exc)));
    // the normal post
    //QuantVariableRef res = entry.post.var;
    Term tNormal = normalPost.getPost();
    tNormal = Logic.implies(tNormal, entry.fPost.getPost()).subst(Ref.varThis, newThis);

    entry.fPost = new Post(Logic.and(pre, Logic.implies(pre, Logic.and(tNormal, tExcp))));
    final List<QuantVariableRef> v = mkArguments(ci);
    final ExprVec ev = ci.args;
    for (int i = ev.size() - 1; i >= 0; i--) {
      entry.fPost = new Post(v.get(i), entry.fPost);
      entry.fPost = (Post) ev.elementAt(i).accept(this, entry);
    }
    entry.fPost = new Post(newThis, entry.fPost);
    return entry.fPost;
  }

  // TODO: add comments
  public static List<QuantVariableRef> mkArguments(final ConstructorInvocation mi) {
    final List<QuantVariableRef> v = new Vector<QuantVariableRef>();
    final FormalParaDeclVec fpdvec = mi.decl.args;
    final FormalParaDecl[] args = fpdvec.toArray();
    for (FormalParaDecl fpd: args) {
      v.add(Expression.rvar(fpd));
    }
    return v;
  }

  @Override
  public /*@non_null*/ Object visitForStmt(final /*@non_null*/ ForStmt x, 
                                           final Object o) {

    final VCEntry vce = (VCEntry)o;
    vce.fPost = treatAnnot(vce, fAnnot.getAnnotPost(x));
    final Term inv =  Util.getAssertion(fMeth, fAnnot.getInvariant(x));
    final Term post = vce.fPost.getPost();
    final Post pinv = new Post(inv);
    final VCEntry vceBody = mkEntryWhile(vce, pinv);
    for (int i = x.forUpdate.size() - 1; i >= 0; i--) {
      vceBody.fPost = (Post) x.forUpdate.elementAt(i).accept(this, vceBody);
    }
    Post bodypre;
    if (x.body instanceof BlockStmt) {
      bodypre = visitInnerBlockStmt((BlockStmt)x.body, vceBody);
    }
    else {
      bodypre = (Post) x.body.accept(this, vceBody);
    }

    final QuantVariableRef v = Expression.rvar(Logic.sort);
    vce.fPost = new Post(v, 
                        Logic.and(Logic.implies(v, bodypre.getPost()),
                                  Logic.implies(Logic.not(v), post)));

    final Term aux = ((Post) x.test.accept(fExprVisitor, vce)).getPost();
    final Term vc = Logic.implies(inv, aux);
    // we add the for declared variables
//    for (int i = x.forInit.size() - 1; i >= 0; i--) {
//      final Stmt s = (Stmt) x.forInit.elementAt(i);
//      final VCEntry newEntry = new VCEntry(vce);
//      newEntry.fPost = new Post(vc);
//      vc = //((Post)s.accept(this, newEntry)).getPost();
//    }
    Term sideCondition = vc; //Util.mkNewEnv(vc);

    //sideCondition = MethodVisitor.addVarDecl(fMeth, sideCondition);
    
    fVcs.add(sideCondition);
    vce.fPost = pinv;
    for (int i = x.forInit.size() - 1; i >= 0; i--) {
      final Stmt s =  (Stmt) x.forInit.elementAt(i);
      vce.fPost = (Post)s.accept(this, vce);
    }
    //vce.fPost = Post.and(new Post(vce.fPost.getRVar(), sideCondition), vce.fPost);
    return treatAnnot(vce, fAnnot.getAnnotPre(x));
  }





  //pas implementer

  /**
   * right now, it is ignored.
   */
  @Override
  public /*@non_null*/ Object visitDoStmt(final /*@non_null*/ DoStmt x, final Object o) {
    return visitStmt(x, o);
  }

  @Override
  public /*@non_null*/ Object visitSwitchStmt(final /*@non_null*/ SwitchStmt x, 
                                              final Object o) {
    return visitStmt(x, o);
  }

  @Override
  public /*@non_null*/ Object visitSwitchLabel(final /*@non_null*/ SwitchLabel x, 
                                               final Object o) {
    return visitStmt(x, o);
  }

  @Override
  public /*@non_null*/ Object visitStmtPragma(final /*@non_null*/ StmtPragma x, 
                                              final Object o) {
    // just ignore it return illegalStmt(x, o);
    return ((VCEntry) o).fPost;
  }

  @Override
  public /*@non_null*/ Object visitSynchronizeStmt(final /*@non_null*/ SynchronizeStmt x, 
                                                   final Object o) {
    return illegalStmt(x, o);
  }
  
  @Override
  public Object visitExprStmtPragma(final ExprStmtPragma x, final Object o) {
    return ((VCEntry) o).fPost;
  }

  @Override
  public Object visitSetStmtPragma(final SetStmtPragma x, final Object o) {
    return ((VCEntry) o).fPost;
  }


  public List<Term> getVcs() {
    return fVcs;
  }

}
