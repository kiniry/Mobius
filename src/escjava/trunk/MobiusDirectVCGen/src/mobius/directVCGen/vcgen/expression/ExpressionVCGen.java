package mobius.directVCGen.vcgen.expression;

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
import javafe.ast.MethodInvocation;
import javafe.ast.NewArrayExpr;
import javafe.ast.NewInstanceExpr;
import javafe.ast.ObjectDesignator;
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
import mobius.directVCGen.vcgen.stmt.StmtVCGen;
import mobius.directVCGen.vcgen.struct.Post;
import mobius.directVCGen.vcgen.struct.VCEntry;
import escjava.ast.Modifiers;
import escjava.ast.TagConstants;
import escjava.sortedProver.Lifter.QuantVariable;
import escjava.sortedProver.Lifter.QuantVariableRef;
import escjava.sortedProver.Lifter.Term;


public class ExpressionVCGen extends BinaryExpressionVCGen{

	public ExpressionVCGen(ExpressionVisitor vis) {
		super(vis);
	}

	public static Vector<QuantVariableRef> mkArguments(MethodInvocation mi) {
		Vector<QuantVariableRef> v = new Vector<QuantVariableRef>();
		FormalParaDeclVec fpdvec = mi.decl.args;
		FormalParaDecl[] args = fpdvec.toArray();
		for (FormalParaDecl fpd: args) {
			v.add(Expression.rvar(fpd));
		}
		return v;
	}
	public static Vector<QuantVariableRef> mkArguments(NewInstanceExpr mi) {
		Vector<QuantVariableRef> v = new Vector<QuantVariableRef>();
		FormalParaDeclVec fpdvec = mi.decl.args;
		FormalParaDecl[] args = fpdvec.toArray();
		for (FormalParaDecl fpd: args) {
			v.add(Expression.rvar(fpd));
		}
		return v;
	}
	public Post methodInvocation(MethodInvocation mi, VCEntry entry) {
		Post normalPost = Lookup.normalPostcondition(mi.decl);
		Post excpPost = Lookup.exceptionalPostcondition(mi.decl);
		Term pre = Lookup.precondition(mi.decl);
		QuantVariableRef newThis = Expression.rvar(Ref.sort);
		
		// first: the exceptional post
		QuantVariableRef exc = Expression.rvar(Ref.sort);
		Term tExcp = Logic.forall(exc.qvar, Logic.implies(excpPost.substWith(exc).subst(Ref.varThis, newThis), 
				               		StmtVCGen.getExcpPost(Type.javaLangThrowable(), entry).substWith(exc)));
		// the normal post
		QuantVariableRef res = entry.post.var;		
		Term tNormal = normalPost.substWith(res);
		tNormal = Logic.forall(res, Logic.implies(tNormal, entry.post.substWith(res)).subst(Ref.varThis, newThis));

		entry.post = new Post(Logic.and(pre, Logic.implies(pre, Logic.and(tNormal, tExcp))));
		Vector<QuantVariableRef> v = mkArguments(mi);
		ExprVec ev = mi.args;
		for (int i = ev.size() - 1; i >= 0; i--) {
			entry.post = new Post(v.elementAt(i), entry.post.post);
			entry.post = getPre(ev.elementAt(i), entry);
		}
		entry.post = new Post(newThis, entry.post.post);
		entry.post = getPre(mi.od, entry);
		return entry.post;
	}



	public Post instanceOf(InstanceOfExpr x, VCEntry entry) {
		Post p = entry.post;
		
		QuantVariableRef r = Expression.rvar(Ref.sort);
		p = new Post(r,
			Logic.and(Logic.implies(Logic.assignCompat(Heap.var, r, 
												 Type.translate(x.type)),
								    p.substWith(Bool.value(true))), 
				      Logic.implies(Logic.not(Logic.typeLE(Type.of(Heap.var, r), 
						  								   Type.translate(x.type))),
						  			p.substWith(Bool.value(false)))));
		entry.post = p;
		Post pre = getPre(x.expr, entry);
		return pre;
	}

	public Post condExpr(CondExpr x, VCEntry e) {
		// of the form (cond ? st1 : st2 )
		QuantVariableRef cond = Expression.rvar(Bool.sort);


		QuantVariableRef st1 = Expression.rvar(Type.getSort(x.thn));		
		Post pthen = new Post(st1, e.post.substWith(st1));
		e.post = pthen;
		pthen = getPre(x.thn, e);

		
		QuantVariableRef st2 = Expression.rvar(Type.getSort(x.els));
		Post pelse = new Post(st2, e.post.substWith(st2));
		e.post = pelse;
		pelse = getPre(x.els, e);
		
		Post pcond = new Post(cond, Logic.and(Logic.implies(Logic.boolToProp(cond), pthen.post),
											  Logic.implies(Logic.not(Logic.boolToProp(cond)), pelse.post)));
		// now for the wp...
		e.post = pcond;
		pcond = getPre(x.test, e);
		return pcond;
	}

	public Post castExpr(CastExpr x, VCEntry e) {
		Post p = new Post(e.post.var, 
							Logic.implies(Logic.assignCompat(Heap.var, e.post.var, Type.translateToType(x.type)),
										  e.post.post));
		e.post = p;
		p = getPre(x.expr, e);
		return p;
	}

	public Post objectDesignator(ObjectDesignator od, VCEntry entry) {
		switch(od.getTag()) {
			case TagConstants.EXPROBJECTDESIGNATOR: {
				// can be null
				//System.out.println(field.decl.parent);
				ExprObjectDesignator eod = (ExprObjectDesignator) od;
				//QuantVariable f = Expression.var(field.decl);
				//Sort s = f.type;
				QuantVariableRef obj = entry.post.var;
				entry.post = new Post(obj, Logic.and(
						Logic.implies(Logic.not(Logic.equalsNull(obj)), entry.post.post), 
						Logic.implies(Logic.equalsNull(obj), getNewExcpPost(Type.javaLangNullPointerException(), entry))
													 ));
				return getPre(eod.expr, entry);

			}
			case TagConstants.SUPEROBJECTDESIGNATOR:
				// TODO: the case for super
			case TagConstants.TYPEOBJECTDESIGNATOR: {
				// cannot be null
				//System.out.println(field);
				return entry.post;
			}
			default: 
				throw new IllegalArgumentException("Unknown object designator type ! " + od);
			
		}
	}

	public Post newInstance(NewInstanceExpr ni, VCEntry entry) {
		QuantVariableRef newheap = Heap.newVar();
	
		
		Post normalPost = Lookup.normalPostcondition(ni.decl);
		Post excpPost = Lookup.exceptionalPostcondition(ni.decl);
		Term pre = Lookup.precondition(ni.decl);
		QuantVariableRef newThis = entry.post.var;
		
		// first: the exceptional post
		QuantVariableRef exc = Expression.rvar(Ref.sort);
		Term tExcp = Logic.forall(exc.qvar, Logic.implies(excpPost.substWith(exc).subst(Ref.varThis, newThis), 
				               		StmtVCGen.getExcpPost(Type.javaLangThrowable(), entry).substWith(exc)));
		// the normal post
		QuantVariableRef res = entry.post.var;		
		Term tNormal = normalPost.substWith(res);
		tNormal = Logic.forall(res, Logic.implies(tNormal, entry.post.substWith(res)).subst(Ref.varThis, newThis));

		entry.post = new Post(Logic.and(pre, Logic.implies(pre, Logic.and(tNormal, tExcp))));
		
		entry.post = new Post(Logic.forall(newThis, Logic.forall(newheap, Logic.implies(
								Heap.newObject(Heap.var, Type.translate(ni.type), newheap, newThis), entry.post.post.subst(Heap.var, newheap)))));
		
		Vector<QuantVariableRef> v = mkArguments(ni);
		ExprVec ev = ni.args;
		for (int i = ev.size() - 1; i >= 0; i--) {
			entry.post = new Post(v.elementAt(i), entry.post.post);
			entry.post = getPre(ev.elementAt(i), entry);
		}
		entry.post = new Post(newThis, entry.post.post);
		return entry.post;
	}

	public Post fieldAccess(FieldAccess field, VCEntry entry) {
	
		QuantVariable f = Expression.var(field.decl);
		Lookup.fieldsToDeclare.add(f);
		if(Modifiers.isStatic(field.decl.modifiers)) {
			return new Post(entry.post.substWith(Heap.select(Heap.var, f)));
		}
		else { // not static :)
			QuantVariableRef obj = Expression.rvar(Ref.sort);
			Term normal = entry.post.substWith(Heap.select(Heap.var, obj, f));
			entry.post = new Post(obj, normal);
			Post p = objectDesignator(field.od, entry);

			return p;			
		}
		
	}

	public Post newArray(NewArrayExpr narr, VCEntry entry) {
		QuantVariableRef newHeap = Heap.newVar();
		QuantVariableRef loc = entry.post.var;
		QuantVariableRef dim;
		//ArrayInit init= narr.init;
		Term arr;
		Post pre = entry.post;
		Term type =  Type.translateToType(narr.type);
		
		// init expressions.
		if (narr.init != null) {
			ArrayInit init = narr.init;
			VarInitVec vec = init.elems;
			for(int i = vec.size() - 1; i >= 0; i--) {
				VarInit vi = vec.elementAt(i);
				QuantVariableRef qvr = Expression.rvar(Type.getSort(vi));
				Term store = Heap.storeArray(Heap.var, loc, Num.value(i), qvr);
				entry.post = new Post(qvr, entry.post.post.subst(Heap.var, store));
				entry.post = getPre(vi, entry);
			}
			
		}
		
		
		Vector<QuantVariableRef> dimVec = new Vector<QuantVariableRef>();


		// multi array creation note: it is not working
		for(int i = narr.dims.size() -1;  i > 0; i --) {
			//Term res;
			dim = Expression.rvar(Num.sortInt);
			QuantVariableRef idx = Expression.rvar(Num.sortInt);
			
			 Logic.forall(dim, 
					Logic.implies(Logic.interval0To(dim, idx),
							Logic.implies(Heap.newArray(Heap.var, type, newHeap, dim,loc), pre.post)));
			//type = Type.arrayof(type);
		}
		dim = Expression.rvar(Num.sortInt);
		arr = Heap.newArray(Heap.var, type, newHeap, dim, loc);
		pre = new Post(dim, Logic.forall(loc, Logic.forall(newHeap, Logic.implies(arr, pre.post))));
		dimVec.add(dim);

		
		// dim handling
		for(int i = narr.dims.size() -1;  i >= 0; i --) {
			entry.post = new Post(dimVec.elementAt(i), pre.post);
			pre = getPre(narr.dims.elementAt(i), entry);
		}
		
		return pre;
	}

	public Post arrayRef(ArrayRefExpr arr, VCEntry entry) {
		QuantVariableRef var = Expression.rvar(Ref.sort);
		QuantVariableRef idx = Expression.rvar(Num.sortInt);
		Term pre = entry.post.post;
		Term length = Heap.select(Heap.var, var, Expression.length);
		
		pre = entry.post.substWith(Heap.selectArray(Heap.var, var, idx, Type.getSort(arr)));
		Term norm = Logic.implies(Logic.interval0To(length, idx), pre);
		
		QuantVariableRef exc = Expression.rvar(Ref.sort);
		Term tExcp = Logic.forall(exc.qvar, 
				Logic.implies(Logic.not(Logic.interval0To(length, idx)), 
				               		StmtVCGen.getExcpPost(Type.javaLangArrayOutOfBoundException(), entry).substWith(exc)));
		
		pre = Logic.and(norm, tExcp);
		entry.post = new Post(idx, pre);
		pre = getPre(arr.index, entry).post;
		
		norm = Logic.implies(Logic.not(Logic.equalsNull(var)), pre);
		tExcp = Logic.forall(exc.qvar, 
				Logic.implies(Logic.equalsNull(var), 
				               		StmtVCGen.getExcpPost(Type.javaLangNullPointerException(), entry).substWith(exc)));
		
		pre = Logic.and(norm, tExcp);
		entry.post = new Post(var, pre);
		pre = getPre(arr.array, entry).post;
		
		return new Post(pre);
	}


	
	
}
