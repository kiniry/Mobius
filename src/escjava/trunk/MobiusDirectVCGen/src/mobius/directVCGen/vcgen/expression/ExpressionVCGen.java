package mobius.directVCGen.vcgen.expression;

import java.util.LinkedList;
import java.util.List;
import java.util.Vector;

import javafe.ast.ArrayInit;
import javafe.ast.ArrayRefExpr;
import javafe.ast.CastExpr;
import javafe.ast.CondExpr;
import javafe.ast.ExprObjectDesignator;
import javafe.ast.ExprVec;
import javafe.ast.FieldAccess;
import javafe.ast.FormalParaDecl;
import javafe.ast.FormalParaDeclVec;
import javafe.ast.InstanceOfExpr;
import javafe.ast.MethodDecl;
import javafe.ast.MethodInvocation;
import javafe.ast.NewArrayExpr;
import javafe.ast.NewInstanceExpr;
import javafe.ast.ObjectDesignator;
import javafe.ast.RoutineDecl;
import javafe.ast.UnaryExpr;
import javafe.ast.VarInit;
import javafe.ast.VarInitVec;
import mobius.directVCGen.formula.Bool;
import mobius.directVCGen.formula.Expression;
import mobius.directVCGen.formula.Heap;
import mobius.directVCGen.formula.Logic;
import mobius.directVCGen.formula.Lookup;
import mobius.directVCGen.formula.Num;
import mobius.directVCGen.formula.Ref;
import mobius.directVCGen.formula.Type;
import mobius.directVCGen.formula.Util;
import mobius.directVCGen.vcgen.struct.Post;
import mobius.directVCGen.vcgen.struct.VCEntry;
import escjava.ast.Modifiers;
import escjava.ast.TagConstants;
import escjava.sortedProver.Lifter.QuantVariable;
import escjava.sortedProver.Lifter.QuantVariableRef;
import escjava.sortedProver.Lifter.Term;


public class ExpressionVCGen extends BinaryExpressionVCGen {

  public ExpressionVCGen(final ExpressionVisitor vis) {
    super(vis);
  }

  public static List<QuantVariableRef> mkArguments(final RoutineDecl decl) {
    final List<QuantVariableRef> v = new Vector<QuantVariableRef>();
    final FormalParaDeclVec fpdvec = decl.args;
    final FormalParaDecl[] args = fpdvec.toArray();
    for (FormalParaDecl fpd: args) {
      v.add(Expression.rvar(fpd));
    }
    return v;
  }
  public static List<QuantVariableRef> mkArguments(final NewInstanceExpr mi) {
    final List<QuantVariableRef> v = new Vector<QuantVariableRef>();
    final FormalParaDeclVec fpdvec = mi.decl.args;
    final FormalParaDecl[] args = fpdvec.toArray();
    for (FormalParaDecl fpd: args) {
      v.add(Expression.rvar(fpd));
    }
    return v;
  }
  
  public Post methodInvocation(final MethodInvocation mi, final VCEntry entry) {
    getInvocation(mi.decl, mi.args, entry);
    entry.fPost = getPre(mi.od, entry);
    final List<QuantVariableRef> v = mkArguments(mi.decl);
    final ExprVec ev = mi.args;
    for (int i = ev.size() - 1; i >= 0; i--) {
      entry.fPost = new Post(v.get(i), entry.fPost);
      entry.fPost = getPre(ev.elementAt(i), entry);
    }
    return entry.fPost;
  }

  private void getInvocation(final RoutineDecl meth, ExprVec methArgs, final VCEntry entry) {
    
    final QuantVariableRef newThis = Expression.rvar(Heap.sortValue);
    final QuantVariableRef newHeap = Heap.newVar();
    
    //mking the args
    final String name = Util.getMethodAnnotModule(meth);
    final LinkedList<Term> args = new LinkedList<Term> ();
    args.add(Heap.varPre);
    args.addAll(Lookup.getInst().getPreconditionArgs(meth));
    
    // mking the meth norm post
    final QuantVariableRef resVar = Lookup.getNormalPostcondition(meth).getRVar();
    if (!Util.isVoid(meth)) {
      args.addFirst(Expression.normal(Expression.some(Heap.sortToValue(resVar))));
    }
    else {
      args.addFirst(Expression.normal(Expression.none()));
    }
    Term[] tab = args.toArray(new Term [args.size()]);
    for (int i = 0; i < tab.length; i++) {
      if (tab[i].equals(Heap.var)) {
        tab[i] = newHeap;
      }
      else if (tab[i].equals(Ref.varThis)) {
        tab[i] = newThis;
      }
      else if (tab[i].equals(Heap.varPre)) {
        tab[i] = Heap.var;
      }
    }
    final Post methNormPost = new Post(resVar, Expression.sym(name + ".mk_post", tab));
    
    // mking the meth excp post
    final QuantVariableRef excVar = Lookup.getExceptionalPostcondition(meth).getRVar();
    tab = args.toArray(new Term [args.size()]);
    tab [0] = Expression.sym("Exception", new Term [] {excVar});
    for (int i = 0; i < tab.length; i++) {
      if (tab[i].equals(Heap.var)) {
        tab[i] = newHeap;
      }
      else if (tab[i].equals(Ref.varThis)) {
        tab[i] = newThis;
      }
      else if (tab[i].equals(Heap.varPre)) {
        tab[i] = Heap.var;
      }
    }
    final Post methExcpPost = new Post(excVar, Expression.sym(name + ".mk_post", tab));

   
   
    // mking the meth pre
    final List<QuantVariableRef> preArgs = Lookup.getInst().getPreconditionArgs(meth);
    
    tab = preArgs.toArray(new Term [preArgs.size()]);
    for (int i = 0; i < tab.length; i++) {
      if (tab[i].equals(Ref.varThis)) {
        tab[i] = newThis;
      }
      else if (tab[i].equals(Heap.var)) {
        tab[i] = Heap.var;
      }
      else if (tab[i].equals(Heap.varPre)) {
        throw new IllegalArgumentException("but, where does it come from?");
      }
    }
    final Term pre = Expression.sym(name + ".mk_pre", tab);
      
    

    // first: the exceptional post
    final QuantVariableRef exc = Expression.rvar(Heap.sortValue);
    final Term excpPost =  Util.getExcpPost(Type.javaLangThrowable(), entry).substWith(exc)
                                    .subst(Heap.var, newHeap);
    final Term methExcp = Logic.implies(pre, methExcpPost.substWith(exc));
    final Term tExcp = Logic.forall(exc, Logic.implies(methExcp, excpPost));
    
    // the normal post
    final QuantVariableRef res = Expression.rvar(entry.fPost.getRVar().getSort());
    final Term normPost = entry.fPost.substWith(res).subst(Heap.var, newHeap);
    final Term methNorm = Logic.implies(pre, methNormPost.substWith(res));
    final Term tNormal = Logic.forall(res, Logic.implies(methNorm, normPost));

    entry.fPost = new Post(Logic.forall(newHeap, Logic.and(tNormal, tExcp)));
    //entry.fPost = new Post(Logic.and(pre, Logic.implies(pre, Logic.and(tNormal, tExcp))));
  
    entry.fPost = new Post(newThis, entry.fPost);
  }







  public Post instanceOf(final InstanceOfExpr x, final VCEntry entry) {
    Post p = entry.fPost;
    final QuantVariableRef r = Expression.rvar(Ref.sort);
    p = new Post(r,
                 Logic.and(Logic.implies(Logic.assignCompat(Heap.var, r, 
                                                            Type.translateToType(x.type)),
                                        p.substWith(Bool.value(true))), 
                           Logic.implies(Logic.not(Logic.typeLE(Type.of(Heap.var, r), 
                                                                Type.translateToType(x.type))),
                                         p.substWith(Bool.value(false)))));
    entry.fPost = p;
    final Post pre = getPre(x.expr, entry);
    return pre;
  }

  public Post condExpr(final CondExpr x, final VCEntry e) {
    // of the form (cond ? st1 : st2 )
    final QuantVariableRef cond = Expression.rvar(Logic.sort);

    final QuantVariableRef st1 = Expression.rvar(Type.getSort(x.thn));
    Post pthen = new Post(st1, e.fPost.substWith(st1));
    e.fPost = pthen;
    pthen = getPre(x.thn, e);


    final QuantVariableRef st2 = Expression.rvar(Type.getSort(x.els));
    Post pelse = new Post(st2, e.fPost.substWith(st2));
    e.fPost = pelse;
    pelse = getPre(x.els, e);

    Post pcond = new Post(cond, Logic.and(Logic.implies(Logic.boolToPred(cond), 
                                                        pthen.getPost()),
                                          Logic.implies(Logic.not(Logic.boolToPred(cond)), 
                                                        pelse.getPost())));
    // now for the wp...
    e.fPost = pcond;
    pcond = getPre(x.test, e);
    return pcond;
  }

  public Post castExpr(final CastExpr x, final VCEntry e) {
    Post p = new Post(e.fPost.getRVar(), 
                      Logic.implies(Logic.assignCompat(Heap.var, 
                                                       e.fPost.getRVar(),
                                                       Type.translate(x.type)),
                                    e.fPost.getPost()));
    e.fPost = p;
    p = getPre(x.expr, e);
    return p;
  }

  public Post objectDesignator(final ObjectDesignator od, final VCEntry entry) {
    switch(od.getTag()) {
      case TagConstants.EXPROBJECTDESIGNATOR: {
        // can be null
        //System.out.println(field.decl.parent);
        final ExprObjectDesignator eod = (ExprObjectDesignator) od;
        //QuantVariable f = Expression.var(field.decl);
        //Sort s = f.type;
        final QuantVariableRef obj = entry.fPost.getRVar();
        final Term excPost =  
          Util.getNewExcpPost(Type.javaLangNullPointerExceptionName(), entry);
        entry.fPost = 
          new Post(obj, 
                   Logic.and(Logic.implies(Logic.equalsNull(obj), excPost),
                             Logic.implies(Logic.not(Logic.equalsNull(obj)), 
                                           entry.fPost.getPost())));
        return getPre(eod.expr, entry);
  
      }
      case TagConstants.SUPEROBJECTDESIGNATOR:
        // I believe strongly (gasp) that super is not useful as it is 
        // contained in the method/field signature...
      case TagConstants.TYPEOBJECTDESIGNATOR: {
        // cannot be null
        //System.out.println(field);
        return entry.fPost;
      }
      default: 
        throw new IllegalArgumentException("Unknown object designator type ! " + od);

    }
  }

  public Post newInstance(final NewInstanceExpr ni, final VCEntry entry) {
    getInvocation(ni.decl, ni.args, entry);
    final QuantVariableRef newThis = entry.fPost.getRVar();
    final QuantVariableRef newHeap = Heap.newVar();
    final Term newObject = Heap.newObject(Heap.var, 
                                          Type.translateToName(ni.type),
                                          newHeap, newThis);
    entry.fPost = 
      new Post(Logic.forall(newThis, 
                            Logic.forall(newHeap, 
                                         Logic.implies(newObject, 
                                                       entry.fPost.subst(Heap.var, 
                                                                         newHeap)))));
    final List<QuantVariableRef> v = mkArguments(ni.decl);
    final ExprVec ev = ni.args;
    for (int i = ev.size() - 1; i >= 0; i--) {
      entry.fPost = new Post(v.get(i), entry.fPost);
      entry.fPost = getPre(ev.elementAt(i), entry);
    }
    return entry.fPost;
  }

  public Post fieldAccess(final FieldAccess field, final VCEntry entry) {
    final QuantVariable f = Expression.var(field.decl);
    //Lookup.fieldsToDeclare.add(f);
    if (Modifiers.isStatic(field.decl.modifiers)) {
      return new Post(entry.fPost.substWith(Heap.select(Heap.var, f)));
    }
    else { // not static :)
      final QuantVariableRef obj = Expression.rvar(Heap.sortValue);
      final Term normal = entry.fPost.substWith(Heap.select(Heap.var, obj, f,
                                                            Type.getSort(field)));
      
      entry.fPost = new Post(obj, normal);
      final Post p = objectDesignator(field.od, entry);

      return p;
    }

  }

  public Post newArray(final NewArrayExpr narr, final VCEntry entry) {
    final QuantVariableRef newHeap = Heap.newVar();
    final QuantVariableRef loc = entry.fPost.getRVar();
    QuantVariableRef dim;
    //ArrayInit init= narr.init;
    Term arr;
    Post pre = entry.fPost;
    final Term type =  Type.translate(narr.type);

    // init expressions.
    if (narr.init != null) {
      entry.fPost = new Post(loc, entry.fPost);
      entry.fPost = getPre(narr.init, entry);
    }


    final List<QuantVariableRef> dimVec = new Vector<QuantVariableRef>();


    // multi array creation note: it is not working
    for (int i = narr.dims.size() - 1;  i > 0; i--) {
      //Term res;
      dim = Expression.rvar(Num.sortInt);
      final QuantVariableRef idx = Expression.rvar(Num.sortInt);

      Logic.forall(dim, 
                   Logic.implies(Logic.interval0To(dim, idx),
                                 Logic.implies(Heap.newArray(Heap.var, 
                                                             type, newHeap, 
                                                             dim, loc), 
                                               pre.getPost())));
      //type = Type.arrayof(type);
    }
    dim = Expression.rvar(Num.sortInt);
    arr = Heap.newArray(Heap.var, type, newHeap, dim, loc);
    pre = new Post(dim, 
                   Logic.forall(loc, 
                                Logic.forall(newHeap, 
                                             Logic.implies(arr, pre.getPost()))));
    dimVec.add(dim);


    // dim handling
    for (int i = narr.dims.size() - 1;  i >= 0; i--) {
      entry.fPost = new Post(dimVec.get(i), pre);
      pre = getPre(narr.dims.elementAt(i), entry);
    }

    return pre;
  }

  public Post arrayRef(final ArrayRefExpr arr, final VCEntry entry) {
    final QuantVariableRef var = Expression.rvar(Ref.sort);
    final QuantVariableRef idx = Expression.rvar(Num.sortInt);
    Term pre = entry.fPost.getPost();
    final Term length = Heap.select(Heap.var, var, Expression.length, Num.sortInt);

    pre = entry.fPost.substWith(Heap.selectArray(Heap.var, var, idx, Type.getSort(arr)));
    Term norm = Logic.implies(Logic.interval0To(length, idx), pre);

    Term tExcp = Logic.implies(Logic.not(Logic.interval0To(length, idx)), 
                                            Util.getNewExcpPost(
                                                  Type.javaLangArrayOutOfBoundException(), 
                                                                  entry));

    pre = Logic.and(norm, tExcp);
    entry.fPost = new Post(idx, pre);
    pre = getPre(arr.index, entry).getPost();

    norm = Logic.implies(Logic.not(Logic.equalsNull(var)), pre);
    tExcp = Logic.implies(Logic.equalsNull(var), 
                                       Util.getNewExcpPost(
                                                Type.javaLangNullPointerException(), 
                                                entry));

    pre = Logic.and(norm, tExcp);
    entry.fPost = new Post(var, pre);
    pre = getPre(arr.array, entry).getPost();

    return new Post(pre);
  }

  public Post arrayInit(final ArrayInit init, final VCEntry entry) {
    final VarInitVec vec = init.elems;
    final QuantVariableRef loc = entry.fPost.getRVar();
    for (int i = vec.size() - 1; i >= 0; i--) {
      final VarInit vi = vec.elementAt(i);
      final QuantVariableRef qvr = Expression.rvar(Type.getSort(vi));
      final Term store = Heap.storeArray(Heap.var, loc, Num.value(i), qvr);
      entry.fPost = new Post(qvr, entry.fPost.subst(Heap.var, store));
      entry.fPost = getPre(vi, entry);
    }
    return entry.fPost;
  }



  public Post bitNot(final UnaryExpr expr, final VCEntry post) {
    post.fPost = new Post(post.fPost.getRVar(), 
                          post.fPost.substWith(Num.bitnot(post.fPost.getRVar())));
    return getPre(expr.expr, post);
  }

  public Post unarySub(final UnaryExpr expr, final VCEntry post) {
    post.fPost = new Post(post.fPost.getRVar(), 
                          post.fPost.substWith(Num.sub(post.fPost.getRVar())));
    return getPre(expr.expr, post);
  }

  public Post not(final UnaryExpr expr, final VCEntry post) {
    post.fPost = new Post(post.fPost.getRVar(), 
                          post.fPost.substWith(Bool.not(post.fPost.getRVar())));
    return getPre(expr.expr, post);
  }

  public Post postfixInc(final UnaryExpr expr, final VCEntry entry) {
    final Term between = Expression.sym("(Byte.range 1)", new Term [] {});
    
      
    final Post oldp = entry.fPost;
    final QuantVariableRef var = Expression.rvar(Type.getSort(expr));
    entry.fPost = new Post(var, oldp);
    Post newpost = assign(expr.expr, entry);
    entry.fPost = new Post(var, newpost.substWith(Num.inc(newpost.getRVar())));
    newpost = getPre(expr.expr, entry);
    entry.fPost = new Post(oldp.getRVar(), Post.implies(between, newpost));
    return getPre(expr.expr, entry);
  }
  public Post postfixDec(final UnaryExpr expr, final VCEntry entry) {
    final Post oldp = entry.fPost;
    final QuantVariableRef var = Expression.rvar(Type.getSort(expr));
    entry.fPost = new Post(var, oldp);
    Post newpost = assign(expr.expr, entry);
    entry.fPost = new Post(var, newpost.substWith(Num.dec(newpost.getRVar())));
    newpost = getPre(expr.expr, entry);
    entry.fPost = new Post(oldp.getRVar(), newpost);
    return getPre(expr.expr, entry);
  }


  public Post inc(final UnaryExpr expr, final VCEntry entry) {
    final Post oldp = entry.fPost;
    final Term between = Expression.sym("(Byte.range 1)", new Term[] {});
    
                                  
    entry.fPost = new Post (oldp.getRVar(), 
                            Logic.implies(between,
                                          oldp.substWith(Num.inc(oldp.getRVar()))));
    return getPre(expr.expr, entry);
  }


  public Post dec(final UnaryExpr expr, final VCEntry entry) {
    final Post oldp = entry.fPost;
    entry.fPost = new Post (oldp.getRVar(), oldp.substWith(Num.dec(oldp.getRVar())));
    return getPre(expr.expr, entry);
  }


}
