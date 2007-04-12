package mobius.directVCGen.formula.annotation;

import java.util.Vector;

import javafe.ast.ASTDecoration;
import javafe.ast.ASTNode;

public class AnnotationDecoration extends ASTDecoration {

	public static final AnnotationDecoration inst = new AnnotationDecoration();
	public AnnotationDecoration() {
		super("annotationDecorations");
	}
	
	public static class Annotation {
		protected final Vector<AAnnotation> pre = new Vector<AAnnotation>();

		protected final Vector<AAnnotation> post = new Vector<AAnnotation>();

		protected AAnnotation inv = null;
	}

	public Vector<AAnnotation> getAnnotPre(ASTNode n) {
		Annotation v = getAnnot(n);
		if(v == null)
			return null;
		else 
			return v.pre;
	}
	
	public Vector<AAnnotation> getAnnotPost(ASTNode n) {
		Annotation v = getAnnot(n);
		if(v == null)
			return null;
		else 
			return v.post;
	}
	
	
	@SuppressWarnings("unchecked")
	public Annotation getAnnot(ASTNode n) {
		Annotation v = (Annotation) super.get(n);
		return v;
	}
	
	
	public void setAnnotPre(ASTNode n, Vector<AAnnotation> v) {
		Annotation res = getAnnot(n);
		if(res == null) {
			super.set(n, res = new Annotation());
		}
		res.pre.clear();
		res.pre.addAll(v);
	}
	public void setAnnotPost(ASTNode n, Vector<AAnnotation> v) {
		Annotation res = getAnnot(n);
		if(res == null) {
			super.set(n, res = new Annotation());
		}
		res.post.clear();
		res.post.addAll(v);
	}
	
	public void setInvariant(ASTNode n, AAnnotation inv) {
		Annotation res = getAnnot(n);
		if(res == null) {
			super.set(n, res = new Annotation());
		}
		res.inv = inv;
	}
	@SuppressWarnings("unchecked")
	public AAnnotation getInvariant(ASTNode n) {
		Annotation v =  getAnnot(n);
		if (v == null)
			return null;
		return v.inv;
	}
}
