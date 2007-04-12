package mobius.directVCGen.formula.annotation;

import java.util.Vector;

import javafe.ast.ASTDecoration;
import javafe.ast.ASTNode;

public class AnnotationDecoration extends ASTDecoration {

	public static final AnnotationDecoration inst = new AnnotationDecoration();
	public AnnotationDecoration() {
		super("annotationDecorations");
	}
	static final int pre = 0;
	static final int post = 1;

	@SuppressWarnings("unchecked")
	public Vector<AAnnotation> getAnnotPre(ASTNode n) {
		Vector<Vector<AAnnotation>> v = getAnnot(n);
		if(v == null)
			return null;
		else 
			return v.get(pre);
	}
	
	@SuppressWarnings("unchecked")
	public Vector<AAnnotation> getAnnotPost(ASTNode n) {
		Vector<Vector<AAnnotation>> v = getAnnot(n);
		if(v == null)
			return null;
		else 
			return v.get(post);
	}
	
	
	@SuppressWarnings("unchecked")
	public Vector<Vector<AAnnotation>> getAnnot(ASTNode n) {
		Vector<Vector<AAnnotation>> v = (Vector<Vector<AAnnotation>>)super.get(n);
		return v;
	}
	
	
	public void setAnnotPre(ASTNode n, Vector<AAnnotation> v) {
		Vector<Vector<AAnnotation>> res = getAnnot(n);
		if(res == null) {
			super.set(n, res = new Vector<Vector<AAnnotation>>(2));
		}
		res.set(pre, v);
	}
	public void setAnnotPost(ASTNode n, Vector<AAnnotation> v) {
		Vector<Vector<AAnnotation>> res = getAnnot(n);
		if(res == null) {
			super.set(n, res = new Vector<Vector<AAnnotation>>(2));
		}
		res.set(post, v);
	}
	
	@SuppressWarnings("unchecked")
	public AAnnotation getLastPre(ASTNode n) {
		Vector<AAnnotation> v =  (Vector<AAnnotation>)getAnnotPre(n);
		if (v == null || v.size() == 0)
			return null;
		return v.lastElement();
	}
}
