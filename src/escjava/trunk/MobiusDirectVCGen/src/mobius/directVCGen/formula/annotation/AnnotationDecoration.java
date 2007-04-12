package mobius.directVCGen.formula.annotation;

import java.util.Vector;

import javafe.ast.ASTDecoration;
import javafe.ast.ASTNode;

public class AnnotationDecoration extends ASTDecoration {

	public static final AnnotationDecoration inst = new AnnotationDecoration();
	public AnnotationDecoration() {
		super("annotationDecorations");
	}
	
	@SuppressWarnings("unchecked")
	public Vector<AAnnotation> get(ASTNode n) {
		return (Vector<AAnnotation>)super.get(n);
	}
	
	public void set(ASTNode n, Vector<AAnnotation> v) {
		super.set(n, v);
	}
	
	@SuppressWarnings("unchecked")
	public AAnnotation getLast(ASTNode n) {
		Vector<AAnnotation> v =  (Vector<AAnnotation>)super.get(n);
		if (v == null || v.size() == 0)
			return null;
		return v.lastElement();
	}
}
