// This class is generated as part os the 2003 Revision of the ESC Tools
// Author: David Cok


package escjava;

import javafe.ast.*;
import javafe.util.ErrorSet;
import javafe.util.Location;
import escjava.ast.*;
import escjava.ast.TagConstants;
import escjava.ast.Modifiers;

/** This class handles the desugaring of annotations.

*/
public class AnnotationHandler {

    public AnnotationHandler() {}

    protected TypeDecl td = null;

    public void handleModelMethods(CompilationUnit cu) {
	TypeDeclVec elems = cu.elems;
	for (int i=0; i<elems.size(); ++i) {
	    TypeDecl td = elems.elementAt(i);
	    handleModelMethods(td);
	}
    }

    /** After parsing, but before type checking, we need to convert model
	methods to regular methods (with the MODEL modifier bit set), so that
	names are resolved correctly.
    */ // FIXME - possibly should put these in GhostEnv??
    public void handleModelMethods(TypeDecl td) {
	for (int j=0; j<td.elems.size(); ++j) {
	    TypeDeclElem tde = td.elems.elementAt(j);
	    // Handle nested types
	    if (tde instanceof TypeDecl) handleModelMethods((TypeDecl)tde);
	    if (tde instanceof ModelMethodDeclPragma) {
		ModelMethodDeclPragma mmp = (ModelMethodDeclPragma)tde;
		td.elems.setElementAt(((ModelMethodDeclPragma)tde).decl,j);
	    }
	}
    }

    public void process(TypeDecl td) {

	this.td = td;

	for (int i=0; i<td.elems.size(); ++i) {
	    TypeDeclElem tde = td.elems.elementAt(i);
	    process(tde);
        }
    }

    protected void process(TypeDeclElem tde) {
	int tag = tde.getTag();
	switch (tag) {
	   case TagConstants.FIELDDECL:

		// skip
		break;

	    case TagConstants.CONSTRUCTORDECL:
		//System.out.println("CONSTRUCTOR");
		break;

	    case TagConstants.METHODDECL:
		process((MethodDecl)tde);
		break;

	    default:
		//System.out.println("TAG " + tag + " " + TagConstants.toString(tag));
	}

    }

    protected void process(MethodDecl tde) {
	//System.out.println("METHOD " + tde.id + " " + Modifiers.toString(tde.modifiers));
	ModifierPragmaVec pmodifiers = tde.pmodifiers;
	if (pmodifiers == null) return;
	for (int i = 0; i<pmodifiers.size(); ++i) {
	    ModifierPragma mp = pmodifiers.elementAt(i);
	    //System.out.println("   pmod " + escjava.ast.TagConstants.toString(mp.getTag()));
	    Object o;
	    if (mp instanceof ExprModifierPragma)
	      (new ReplaceModelVars()).visitNode(((ExprModifierPragma)mp).expr);
	}


    }

    public class ReplaceModelVars {

	public void visitNode(ASTNode x) {
	    if (x == null) return;
	    switch (x.getTag()) {
		case TagConstants.FIELDACCESS:
			//System.out.println("FA "  + ((FieldAccess)x).id);
			break;
		case TagConstants.METHODINVOCATION:
		    MethodInvocation m = (MethodInvocation)x;
		    if (!Modifiers.isPure(m.decl.modifiers)) {
			ErrorSet.error(m.locId,
			    "Method " + m.id + " is used in an annotation" +
			    " but is not pure (" + 
			    Location.toFileLineString(m.decl.loc) + ")");
		    }
		    break;
		default:
		    int n = x.childCount();
		    for (int i = 0; i < n; ++i) {
			if (x.childAt(i) instanceof ASTNode)
				visitNode((ASTNode)x.childAt(i));
		    }
	    }
	}

    }
}
		




