package escjava.vcGeneration;
import java.lang.StringBuffer;

class TDotVisitor extends TVisitor {

    StringBuffer out = null;

    TDotVisitor(){
	out = new StringBuffer();
    }

    /*
     * Generic functions used by different visit* functions
     */

    public void visitTFunction(/*@ non_null @*/ TFunction n){

	/* declaration of the node */
	out.append(n.dotId()); /* unique */

	out.append(" [label = \""+n.getShortName());

	// write the type (if exists)
	if(n.type!=null){
	    /* the old type is contained into the 'type' field which has
	       type 'typeInfo' ouf! */

	    out.append("\\n\\["+n.getType()+"\\]"); 
	}
    
	out.append("\"];\n");

	TNode nTemp = null;

	/* add all the sons */
	for(int i = 0; i <= n.sons.size() - 1; i++){

	    out.append(n.dotId()+" -> ");
	    
	    nTemp = n.getChildAt(i);
	    out.append(nTemp.dotId());

	    /* red arrow for variables, green one for value */
	    if(nTemp instanceof TName)
		out.append(" [color = red]");
	    else if(nTemp instanceof TLiteral)
		out.append(" [color = green]");

	    out.append(";\n");

	    /* recursive call on the sons */
	    nTemp.accept(this);
	}

    }

    public void visitTVariable(/*@ non_null @*/ TVariable n){

	out.append(n.dotId());

	/* add fancy stuff, like square box o_O */
	out.append(" [shape=box, label=\"");

	// write the type (if exists)
	if(n.type!=null){
	    /* the old type is contained into the 'type' field which has
	       type 'typeInfo' ouf! */

	    out.append("\\["+n.getType()+"\\]"); 
	}
	
	//out.append("\"];\n");
    }

    /* 
     * non automatic generated class
     */ 
    public void visitTName(/*@ non_null @*/ TName n){
	
	out.append(n.dotId());

	/* add fancy stuff, like square box o_O */
	out.append(" [shape=box, label=\"");
	
	out.append("\\["+n.getType()+"\\]");
	
	/* append the name of the variable */
	out.append("\\n"+n.name);

	out.append("\"];\n");
    }

    public void visitTRoot(/*@ non_null @*/ TRoot n){

	TNode nTemp = null;

	for(int i = 0; i <= n.sons.size() - 1; i++){

	    nTemp = n.getChildAt(i);

	    /* recursive call on the sons */
	    nTemp.accept(this);

	}
    }
    
    /*
     * class created using the perl script
     */
    public void visitTBoolImplies(/*@ non_null @*/ TBoolImplies n){
	visitTFunction(n);
    }

    public void visitTBoolAnd(/*@ non_null @*/ TBoolAnd n){
	visitTFunction(n);
    }

    public void visitTBoolOr(/*@ non_null @*/ TBoolOr n){
	visitTFunction(n);
    }

    public void visitTBoolNot(/*@ non_null @*/ TBoolNot n){
	visitTFunction(n);
    }

    public void visitTBoolEQ(/*@ non_null @*/ TBoolEQ n){
	visitTFunction(n);
    }

    public void visitTBoolNE(/*@ non_null @*/ TBoolNE n){
	visitTFunction(n);
    }

    public void visitTAllocLT(/*@ non_null @*/ TAllocLT n){
	visitTFunction(n);
    }

    public void visitTAllocLE(/*@ non_null @*/ TAllocLE n){
	visitTFunction(n);
    }

    public void visitTAnyEQ(/*@ non_null @*/ TAnyEQ n){
	visitTFunction(n);
    }

    public void visitTAnyNE(/*@ non_null @*/ TAnyNE n){
	visitTFunction(n);
    }

    public void visitTIntegralEQ(/*@ non_null @*/ TIntegralEQ n){
	visitTFunction(n);
    }

    public void visitTIntegralGE(/*@ non_null @*/ TIntegralGE n){
	visitTFunction(n);
    }

    public void visitTIntegralGT(/*@ non_null @*/ TIntegralGT n){
	visitTFunction(n);
    }

    public void visitTIntegralLE(/*@ non_null @*/ TIntegralLE n){
	visitTFunction(n);
    }

    public void visitTIntegralLT(/*@ non_null @*/ TIntegralLT n){
	visitTFunction(n);
    }

    public void visitTIntegralNE(/*@ non_null @*/ TIntegralNE n){
	visitTFunction(n);
    }

    public void visitTIntegralAdd(/*@ non_null @*/ TIntegralAdd n){
	visitTFunction(n);
    }

    public void visitTIntegralDiv(/*@ non_null @*/ TIntegralDiv n){
	visitTFunction(n);
    }

    public void visitTIntegralMod(/*@ non_null @*/ TIntegralMod n){
	visitTFunction(n);
    }

    public void visitTIntegralMul(/*@ non_null @*/ TIntegralMul n){
	visitTFunction(n);
    }

    public void visitTFloatEQ(/*@ non_null @*/ TFloatEQ n){
	visitTFunction(n);
    }

    public void visitTFloatGE(/*@ non_null @*/ TFloatGE n){
	visitTFunction(n);
    }

    public void visitTFloatGT(/*@ non_null @*/ TFloatGT n){
	visitTFunction(n);
    }

    public void visitTFloatLE(/*@ non_null @*/ TFloatLE n){
	visitTFunction(n);
    }

    public void visitTFloatLT(/*@ non_null @*/ TFloatLT n){
	visitTFunction(n);
    }

    public void visitTFloatNE(/*@ non_null @*/ TFloatNE n){
	visitTFunction(n);
    }

    public void visitTFloatAdd(/*@ non_null @*/ TFloatAdd n){
	visitTFunction(n);
    }

    public void visitTFloatDiv(/*@ non_null @*/ TFloatDiv n){
	visitTFunction(n);
    }

    public void visitTFloatMod(/*@ non_null @*/ TFloatMod n){
	visitTFunction(n);
    }

    public void visitTFloatMul(/*@ non_null @*/ TFloatMul n){
	visitTFunction(n);
    }

    public void visitTLockLE(/*@ non_null @*/ TLockLE n){
	visitTFunction(n);
    }

    public void visitTLockLT(/*@ non_null @*/ TLockLT n){
	visitTFunction(n);
    }

    public void visitTRefEQ(/*@ non_null @*/ TRefEQ n){
	visitTFunction(n);
    }

    public void visitTRefNE(/*@ non_null @*/ TRefNE n){
	visitTFunction(n);
    }

    public void visitTTypeEQ(/*@ non_null @*/ TTypeEQ n){
	visitTFunction(n);
    }

    public void visitTTypeNE(/*@ non_null @*/ TTypeNE n){
	visitTFunction(n);
    }

    public void visitTTypeLE(/*@ non_null @*/ TTypeLE n){
	visitTFunction(n);
    }

    public void visitTCast(/*@ non_null @*/ TCast n){
	visitTFunction(n);
    }

    public void visitTIs(/*@ non_null @*/ TIs n){
	visitTFunction(n);
    }

    public void visitTSelect(/*@ non_null @*/ TSelect n){
	visitTFunction(n);
    }

    public void visitTStore(/*@ non_null @*/ TStore n){
	visitTFunction(n);
    }

    public void visitTTypeOf(/*@ non_null @*/ TTypeOf n){
	visitTFunction(n);
    }

    public void visitTForAll(/*@ non_null @*/ TForAll n){
	visitTFunction(n);
    }

    public void visitTExist(/*@ non_null @*/ TExist n){
	visitTFunction(n);
    }

    public void visitTIsAllocated(/*@ non_null @*/ TIsAllocated n){
	visitTFunction(n);
    }

    public void visitTEClosedTime(/*@ non_null @*/ TEClosedTime n){
	visitTFunction(n);
    }

    public void visitTFClosedTime(/*@ non_null @*/ TFClosedTime n){
	visitTFunction(n);
    }

    public void visitTAsElems(/*@ non_null @*/ TAsElems n){
	visitTFunction(n);
    }

    public void visitTAsField(/*@ non_null @*/ TAsField n){
	visitTFunction(n);
    }

    public void visitTAsLockSet(/*@ non_null @*/ TAsLockSet n){
	visitTFunction(n);
    }

    public void visitTArrayLength(/*@ non_null @*/ TArrayLength n){
	visitTFunction(n);
    }

    public void visitTArrayFresh(/*@ non_null @*/ TArrayFresh n){
	visitTFunction(n);
    }

    public void visitTArrayShapeOne(/*@ non_null @*/ TArrayShapeOne n){
	visitTFunction(n);
    }

    public void visitTArrayShapeMore(/*@ non_null @*/ TArrayShapeMore n){
	visitTFunction(n);
    }

    public void visitTIsNewArray(/*@ non_null @*/ TIsNewArray n){
	visitTFunction(n);
    }

    public void visitTString(/*@ non_null @*/ TString n){
	visitTVariable(n);

	out.append("\\n"+n.value);
	out.append("\"];\n");
    }	

    public void visitTBoolean(/*@ non_null @*/ TBoolean n){
	visitTVariable(n);

	out.append("\\n"+Boolean.toString(n.value));
	out.append("\"];\n");
    }
    
    public void visitTChar(/*@ non_null @*/ TChar n){
	visitTVariable(n);

	out.append("\\n"+Character.toString(n.value));
	out.append("\"];\n");
    }

    public void visitTInt(/*@ non_null @*/ TInt n){
	visitTVariable(n);

	out.append("\\n"+Integer.toString(n.value));
	out.append("\"];\n");
    }
    
    public void visitTFloat(/*@ non_null @*/ TFloat n){
	visitTVariable(n);

	out.append("\\n"+Float.toString(n.value));
	out.append("\"];\n");
    }

    public void visitTDouble(/*@ non_null @*/ TDouble n){
	visitTVariable(n);
	
	out.append("\\n"+Double.toString(n.value));
	out.append("\"];\n");
    }
    
    public void visitTNull(/*@ non_null @*/ TNull n){
	visitTVariable(n);

	out.append("\\nnull\"];\n");
    }
}
