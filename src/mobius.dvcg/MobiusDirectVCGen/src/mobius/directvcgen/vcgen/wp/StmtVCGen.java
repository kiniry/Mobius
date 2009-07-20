package mobius.directvcgen.vcgen.wp;

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
import javafe.ast.ReturnStmt;
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
import mobius.directVCGen.formula.Translator;
import mobius.directVCGen.formula.Ref;
import mobius.directVCGen.formula.Type;
import mobius.directVCGen.formula.Util;
import mobius.directVCGen.formula.annotation.AAnnotation;
import mobius.directVCGen.formula.annotation.AnnotationDecoration;
import mobius.directVCGen.formula.annotation.Set.Assignment;
import mobius.directvcgen.vcgen.MethodVisitor;
import mobius.directvcgen.vcgen.VarCorrDecoration;
import mobius.directvcgen.vcgen.struct.ExcpPost;
import mobius.directvcgen.vcgen.struct.Post;
import mobius.directvcgen.vcgen.struct.VCEntry;

import org.apache.bcel.generic.MethodGen;

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
  private LinkedList<Term> fVcs = new LinkedList<Term>();
  
  /** the visitor to visit expressions. */
  private final ExpressionVisitor fExprVisitor = new ExpressionVisitor();
  
  /** the decorator that add the annotations or read the annotations from a node. */
  private final AnnotationDecoration fAnnot = AnnotationDecoration.inst;
  
  /** the current method or constructor that is being inspected. */
  private final MethodGen fMeth;

  /** the correspondence from source to bytecode for the variables. */
  private List<QuantVariableRef> fVariables;
  
  
  
  public List<QuantVariableRef> getVars() {
    return fVariables;
  }

  public StmtVCGen(final MethodGen meth) {
    fMeth = meth;
    final List<QuantVariableRef> variables = VarCorrDecoration.inst.get(fMeth);
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
      return vce.getPost();
    }
    Term post = null;
    final int len = annot.size();
    for (int i = len - 1; i >= 0; i--) {
      final AAnnotation aa = annot.get(i);
      switch(aa.getID()) {
        case AAnnotation.annotAssert:
          fVcs.add(Post.implies(aa.getFormula(), vce.getPost()));
          post = aa.getFormula();
          break;
        case AAnnotation.annotCut:
          post = Logic.and(aa.getFormula(), Post.implies(aa.getFormula(), vce.getPost()));
          break;
        case AAnnotation.annotAssume:
          post = Post.implies(aa.getFormula(), vce.getPost());
          break;
        case AAnnotation.annotSet: {
          final mobius.directVCGen.formula.annotation.Set s = 
            (mobius.directVCGen.formula.annotation.Set) aa;
          Term p = vce.getPost().getPost();
          if (s.getAssignment() != null) {
            final Assignment ass = s.getAssignment();
            p = p.subst(ass.getVar(), ass.getExpr());
          }
          else if (s.getDeclaration() != null) {
            if (s.getAssignment() == null) {
              p = Logic.forall(s.getDeclaration().qvar, p);
            }
            addVarDecl(s.getDeclaration().qvar);
          }
          post = p;
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
    Post post = treatAnnot(entry, getAnnotPost(x));
    final QuantVariableRef b  = Expression.rvar(Bool.sort);

    post = new Post(b, Logic.and(b, Post.implies(b, post)));
    entry.setPost(post);
    post = (Post)x.pred.accept(fExprVisitor, entry);
    return treatAnnot(entry, getAnnotPre(x));
  }

  // TODO: add comments
  public VCEntry mkEntryBlock (final VCEntry vce) {
    final VCEntry res = new VCEntry(vce);
    res.fBrPost = vce.getPost();
    return res;

  }

  // TODO: add comments
  @Override
  public /*@non_null*/ Object visitBlockStmt(final /*@non_null*/ BlockStmt x, final Object o) {
    final int max = x.childCount();
    VCEntry vce = (VCEntry) o;
    vce = mkEntryBlock(vce);
    vce.setPost(treatAnnot(vce, getAnnotPost(x)));

    for (int i = max - 1; i >= 0; i--) {
      final Object child = x.childAt(i);
      if (child instanceof ASTNode) {
        vce.setPost((Post) ((ASTNode) child).accept(this, vce));
      }
    }
    return treatAnnot(vce, getAnnotPre(x));
  }

  // TODO: add comments
  public Post visitInnerBlockStmt (final /*@non_null*/ Stmt x, final VCEntry vce) {
    if (!(x instanceof BlockStmt)) {
      return (Post)x.accept(this, vce);
    }
    final int max = x.childCount();
    
    // checking that the annotations are null
    List<AAnnotation> tmp = getAnnotPost(x); 
    assert (tmp == null);
    tmp = getAnnotPre(x);
    assert (tmp == null);
    
    for (int i = max - 1; i >= 0; i--) {
      final Object child = x.childAt(i);
      if (child instanceof ASTNode) {
        vce.setPost((Post) ((ASTNode) child).accept(this, vce));
      }
    }
    return vce.getPost();
  }

  /** {@inheritDoc} */
  @Override
  public Object visitStmt(final Stmt x, final Object o) {
    throw new IllegalArgumentException("Not yet implememented");
  }



  // TODO: add comments
  public VCEntry mkEntryWhile(final VCEntry ve, final Post inv) {
    final VCEntry res = new VCEntry(ve);
    res.fBrPost = ve.getPost();
    res.setPost(inv);
    res.fContPost = inv;
    return res;
  }

  // TODO: add comments
  public /*@non_null*/ Object visitWhileStmt(final /*@non_null*/ WhileStmt x, final Object o) {
    final VCEntry vce = (VCEntry)o;
    vce.setPost(treatAnnot(vce, getAnnotPost(x)));
    final Term inv = Util.getAssertion(fMeth, getInvariant(x));

    
    final Term post = vce.getPost().getPost();
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
    vce.setPost(new Post(v,
                        Logic.and(Post.implies(Logic.boolToPred(v), bodypre),
                                  Logic.implies(Logic.not(Logic.boolToPred(v)), post))));
    // the only field that can be modified in a VCentry is post 
    final Post aux = ((Post) x.expr.accept(fExprVisitor, vce));
    fVcs.add(Post.implies(inv, aux));

    vce.setPost(pinv);
    return treatAnnot(vce, getAnnotPre(x));
  }

  // TODO: add comments
  public /*@non_null*/ Object visitEvalStmt(final /*@non_null*/ EvalStmt x, final Object o) {
    final VCEntry vce = (VCEntry) o;
    vce.setPost(treatAnnot(vce, getAnnotPost(x)));
    final Post p = vce.getPost();
    vce.setPost(new Post(Expression.rvar(Type.getSort(x.expr)),
                        p.getPost()));
    vce.setPost((Post)x.expr.accept(fExprVisitor, vce));
    return treatAnnot(vce, getAnnotPre(x));
  }

  // TODO: add comments
  @Override
  public /*@non_null*/ Object visitReturnStmt(final /*@non_null*/ ReturnStmt x, 
                                              final Object o) {
    
    // Goog to ensure that x.annotPost == Null
    // and so remove this check
    final List<AAnnotation> tmp = getAnnotPost(x);
    assert (tmp == null); // if the method type is not void there should 
    // also be the variable \result
    
    final VCEntry vce = (VCEntry) o;
    final String name = Util.getMethodAnnotModule(fMeth);
    final Term[] tab = Lookup.getInst().getNormalPostconditionArgs(fMeth);
    final Post normPost = new Post(Lookup.getInst().getNormalPostcondition(fMeth).getRVar(), 
                        Expression.sym(name + ".mk_post", tab));

    vce.setPost(normPost);
    vce.setPost((Post) x.expr.accept(fExprVisitor, vce));
    return treatAnnot(vce, getAnnotPre(x));
  }

  public static Post getExcpPostExact(final Term typ, final VCEntry vce) {
    final Iterator iter = vce.lexcpost.iterator();
    while (iter.hasNext()) {
      final ExcpPost p = (ExcpPost)iter.next();
      if (Type.isSubClassOrEq(typ, p.getType())) {
        return p.getPost();
      }
    }
    return vce.getExcPost();

  }



  // TODO: add comments
  public /*@non_null*/ Object visitThrowStmt(final /*@non_null*/ ThrowStmt x, final Object o) {
    final VCEntry vce = (VCEntry)o;
    vce.setPost(treatAnnot(vce, getAnnotPost(x)));
    final Term typ = Type.getTypeName(x.expr);
    vce.setPost(Util.getExcpPost(typ, vce));
    vce.setPost(((Post)x.expr.accept(fExprVisitor, vce)));
    return treatAnnot(vce, getAnnotPre(x));
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
    vce.setPost(getBreakPost(x.label, vce));
    return treatAnnot(vce, getAnnotPre(x));
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
    vce.setPost(getContinuePost(x.label, vce));
    return treatAnnot(vce, getAnnotPre(x));
  }

  // TODO: add comments
  public VCEntry mkEntryLoopLabel(final Identifier label, final VCEntry ve, 
                                  final Post continu) {
    final VCEntry res = new VCEntry(ve);
    res.fBrPost = ve.getPost();
    res.fContPost = continu;
    res.lbrpost.put(label, ve.getPost());
    res.lcontpost.put(label, continu);
    return res;
  }

  // TODO: add comments
  @Override
  public /*@non_null*/ Object visitLabelStmt(final /*@non_null*/ LabelStmt x, 
                                             final Object o) {
    final Stmt s = x.stmt;
    VCEntry vce = (VCEntry)o;
    vce.setPost(treatAnnot(vce, getAnnotPost(x)));
    
    if (s instanceof WhileStmt || s instanceof DoStmt || s instanceof ForStmt) {
      final Term t =  Util.getAssertion(fMeth, getInvariant(s));
      vce = mkEntryLoopLabel(x.label, vce, new Post(t));
    }
    vce.setPost((Post) x.stmt.accept(fExprVisitor, vce));
    return treatAnnot(vce, getAnnotPre(x));
  }

  // TODO: add comments
  @Override
  public /*@non_null*/ Object visitIfStmt(final /*@non_null*/ IfStmt x, 
                                          final Object o) {
    final VCEntry vce = (VCEntry) o;
    final Post postBranch = treatAnnot(vce, getAnnotPost(x));
    vce.setPost(postBranch);
    final Post preT = (Post) x.thn.accept(this, vce);
    vce.setPost(postBranch);
    final Post preF = (Post) x.els.accept(this, vce);

    final QuantVariableRef v = Expression.rvar(Logic.sort);

    vce.setPost(new Post(v,
                        Logic.and(Post.implies(v, preT),
                                  Post.implies(Logic.not(v), preF))));

    vce.setPost((Post) x.expr.accept(fExprVisitor, vce));
  
    return treatAnnot(vce, getAnnotPre(x));
  }

  // TODO: add comments
  @Override
  public /*@non_null*/ Object visitSkipStmt(final /*@non_null*/ SkipStmt x, final Object o) {
    final VCEntry vce = (VCEntry) o;
    vce.setPost(treatAnnot(vce, getAnnotPost(x)));
    return treatAnnot(vce, getAnnotPre(x));
  }

  // TODO: add comments
  @Override
  public /*@non_null*/ Object visitTryFinallyStmt(final /*@non_null*/ TryFinallyStmt x, 
                                                  final Object o) {
    final VCEntry vce = (VCEntry) o;
    vce.setPost(treatAnnot(vce, getAnnotPost(x)));
    final Stmt sTry = x.tryClause;
    final Stmt sFinally = x.finallyClause;
    final VCEntry vcetmp = new VCEntry(vce);
    final Post post = visitInnerBlockStmt(sFinally,  vcetmp);

    // brpost
    vcetmp.setPost(vce.fBrPost);
    final Post brpost = (Post) visitInnerBlockStmt(sFinally,  vcetmp);
    // lbrpost
    final Map<Identifier, Post> lbrpost = new HashMap<Identifier, Post>();
    Set<Identifier> keys = vce.lbrpost.keySet();
    for (Identifier k: keys) {
      vcetmp.setPost(vce.lbrpost.get(k));
      final Post p = visitInnerBlockStmt(sFinally,  vcetmp);
      lbrpost.put(k, p);
    }

    // contpost
    vcetmp.setPost(vce.fContPost);
    final Post contpost = visitInnerBlockStmt(sFinally,  vcetmp);
    //lcontpost
    final Map<Identifier, Post> lcontpost = new HashMap<Identifier, Post>();
    keys = vce.lcontpost.keySet();
    for (Identifier k : keys) {
      vcetmp.setPost(vce.lcontpost.get(k));
      final Post p = visitInnerBlockStmt(sFinally,  vcetmp);
      lcontpost.put(k, p);
    }

    //excpost
    vcetmp.setPost(vce.getExcPost());
    final Post excpost = visitInnerBlockStmt(sFinally,  vcetmp);
    //lexcpost
    final List<ExcpPost> lexcpost = new ArrayList<ExcpPost>();
    for (ExcpPost exc: vce.lexcpost) {
      vcetmp.setPost(exc.getPost());
      final Post p = visitInnerBlockStmt(sFinally,  vcetmp);
      lexcpost.add(new ExcpPost(exc.getType(), p));
    }

    final VCEntry entFinally = new VCEntry(post, excpost, brpost, contpost);
    entFinally.lbrpost.putAll(lbrpost);
    entFinally.lcontpost.putAll(lcontpost);
    entFinally.lexcpost.addAll(lexcpost);
    visitInnerBlockStmt(sTry, entFinally);
    return treatAnnot(vce, getAnnotPre(x));
  }

  // TODO: add comments
  @Override
  public /*@non_null*/ Object visitTryCatchStmt(final /*@non_null*/ TryCatchStmt x, 
                                                final Object o) {
    final VCEntry vce = (VCEntry) o;
    vce.setPost(treatAnnot(vce, getAnnotPost(x)));
    final CatchClauseVec ccv = x.catchClauses;
    final CatchClause[] catches = ccv.toArray();
    final LinkedList<ExcpPost> l = new LinkedList<ExcpPost>();
    final Post olpost = vce.getPost();
    for (CatchClause c: catches) {
      ExcpPost ep;
      final Term t = Type.translateToType(c.arg.type);
      final QuantVariableRef excp = Expression.rvar(c.arg);
      vce.setPost(olpost);
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
    vce.setPost((Post)x.tryClause.accept(this, post));
    //visitInnerBlockStmt(x.tryClause, post);
    return treatAnnot(vce, getAnnotPre(x));
  }

  // TODO: add comments
  @Override
  public /*@non_null*/ Object visitVarDeclStmt(final /*@non_null*/ VarDeclStmt x, 
                                               final Object o) {
    final VCEntry vce = (VCEntry) o;
    vce.setPost(treatAnnot(vce, getAnnotPost(x)));
    final VarInit init = x.decl.init;
    final QuantVariableRef qv = Expression.rvar(x.decl);
    if (init != null) {
      // the init value replaces the quantification
      
      
      vce.setPost(new Post(qv, vce.getPost()));
               //Util.substVarWithVal(vce.getPost(), var, val)));
      vce.setPost((Post)init.accept(this, vce));
      if (init instanceof ArrayInit) {
        // FIXME should add the array new too
        //vce.fPost = new Post(Logic.forall(qv, vce.fPost.getPost()));
      }

    }
    else {
      // the quantification is preemptive
      vce.setPost(new Post(vce.getPost().getRVar(), 
                           vce.getPost()));
      //vce.fPost = new Post(Logic.forall(qv, vce.fPost.getPost()));
      
    }
    // we must anyway declare it for every vc:
    addVarDecl(qv.qvar);
    return treatAnnot(vce, getAnnotPre(x));
  }



  /**
   * Add the variable to the list of the declared variables.
   * The variable is added to each vcs.
   * @param qv the variable to declare
   */
  private void addVarDecl(final QuantVariable qv) {
    final List<Term> oldvcs = fVcs;

    //final QuantVariableRef qvr = Expression.rvar(qv);
    fVcs = new LinkedList<Term>();
    for (Term t: oldvcs) {
      // the quantification is preemptive
      //fVcs.add(t);
      fVcs.add(Logic.forall(qv, t));
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
    final MethodGen mg = Translator.getInst().translate(ci.decl);
    final Post normalPost = Lookup.getInst().getNormalPostcondition(mg);
    final Post excpPost = Lookup.getInst().getExceptionalPostcondition(mg);
    final Term pre = Lookup.getInst().getPrecondition(mg);
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
    tNormal = Post.implies(tNormal, entry.getPost()).subst(Ref.varThis, newThis);

    entry.setPost(new Post(Logic.and(pre, Logic.implies(pre, Logic.and(tNormal, tExcp)))));
    final List<QuantVariableRef> v = mkArguments(ci);
    final ExprVec ev = ci.args;
    for (int i = ev.size() - 1; i >= 0; i--) {
      entry.setPost(new Post(v.get(i), entry.getPost()));
      entry.setPost((Post) ev.elementAt(i).accept(this, entry));
    }
    entry.setPost(new Post(newThis, entry.getPost()));
    return entry.getPost();
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
    vce.setPost(treatAnnot(vce, getAnnotPost(x)));
    final Term inv =  Util.getAssertion(fMeth, getInvariant(x));
    final Term post = vce.getPost().getPost();
    final Post pinv = new Post(inv);
    final VCEntry vceBody = mkEntryWhile(vce, pinv);
    for (int i = x.forUpdate.size() - 1; i >= 0; i--) {
      vceBody.setPost((Post) x.forUpdate.elementAt(i).accept(this, vceBody));
    }
    Post bodypre;
    if (x.body instanceof BlockStmt) {
      bodypre = visitInnerBlockStmt((BlockStmt)x.body, vceBody);
    }
    else {
      bodypre = (Post) x.body.accept(this, vceBody);
    }

    final QuantVariableRef v = Expression.rvar(Logic.sort);
    vce.setPost(new Post(v, 
                        Logic.and(Post.implies(v, bodypre),
                                  Logic.implies(Logic.not(v), post))));

    final Post aux = ((Post) x.test.accept(fExprVisitor, vce));
    final Term vc = Post.implies(inv, aux);
    // we add the for declared variables
//    for (int i = x.forInit.size() - 1; i >= 0; i--) {
//      final Stmt s = (Stmt) x.forInit.elementAt(i);
//      final VCEntry newEntry = new VCEntry(vce);
//      newEntry.fPost = new Post(vc);
//      vc = //((Post)s.accept(this, newEntry)).getPost();
//    }
    final Term sideCondition = vc; //Util.mkNewEnv(vc);

    //sideCondition = MethodVisitor.addVarDecl(fMeth, sideCondition);
    
    fVcs.add(sideCondition);
    vce.setPost(pinv);
    for (int i = x.forInit.size() - 1; i >= 0; i--) {
      final Stmt s =  (Stmt) x.forInit.elementAt(i);
      vce.setPost((Post)s.accept(this, vce));
    }
    //vce.fPost = Post.and(new Post(vce.fPost.getRVar(), sideCondition), vce.fPost);
    return treatAnnot(vce, getAnnotPre(x));
  }





  //pas implementer

  /**
   * right now, it is ignored.
   */
  /** {@inheritDoc} */
  @Override
  public /*@non_null*/ Object visitDoStmt(final /*@non_null*/ DoStmt x, final Object o) {
    return visitStmt(x, o);
  }

  /** {@inheritDoc} */
  @Override
  public /*@non_null*/ Object visitSwitchStmt(final /*@non_null*/ SwitchStmt x, 
                                              final Object o) {
    return visitStmt(x, o);
  }

  /** {@inheritDoc} */
  @Override
  public /*@non_null*/ Object visitSwitchLabel(final /*@non_null*/ SwitchLabel x, 
                                               final Object o) {
    return visitStmt(x, o);
  }
  
  /** {@inheritDoc} */
  @Override
  public /*@non_null*/ Object visitStmtPragma(final /*@non_null*/ StmtPragma x, 
                                              final Object o) {
    // just ignore it return illegalStmt(x, o);
    return ((VCEntry) o).getPost();
  }

  /** {@inheritDoc} */
  @Override
  public /*@non_null*/ Object visitSynchronizeStmt(final /*@non_null*/ SynchronizeStmt x, 
                                                   final Object o) {
    return illegalStmt(x, o);
  }
  
  /** {@inheritDoc} */
  @Override
  public Object visitExprStmtPragma(final ExprStmtPragma x, final Object o) {
    return ((VCEntry) o).getPost();
  }

  /** {@inheritDoc} */
  @Override
  public Object visitSetStmtPragma(final SetStmtPragma x, final Object o) {
    return ((VCEntry) o).getPost();
  }


  public LinkedList<Term> getVcs() {
    return fVcs;
  }
  
  List<AAnnotation> getAnnotPre(final ASTNode n) {
    return fAnnot.getAnnotPre(fMeth, n);
  }
  List<AAnnotation> getAnnotPost(final ASTNode n) {
    return fAnnot.getAnnotPost(fMeth, n);
  }
  
  AAnnotation getInvariant(final ASTNode n) {
    return fAnnot.getInvariant(fMeth, n);
  }

  public static List<Term> doWp(final MethodGen meth, final BlockStmt x, 
                          final Term precondition, final VCEntry post) {
    final StmtVCGen dvcg = new StmtVCGen(meth);
    final Post wp = (Post)x.accept(dvcg, post);
    
    Term pre = Post.implies(precondition, wp);    
    pre = MethodVisitor.addVarDecl(meth, pre);
    final List<QuantVariableRef> largs = Lookup.getInst().getPreconditionArgs(meth);
    for (Term vars: largs) {
      final QuantVariableRef qvr = (QuantVariableRef) vars;
      pre = pre.subst(Expression.old(qvr), qvr);
    }
    final LinkedList<Term> vcs = dvcg.getVcs();
    vcs.addFirst(pre);
    return vcs;
  }
}
