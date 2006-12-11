package escjava.vcGeneration;

import java.io.StringWriter;

class TDotVisitor extends TVisitor {

    TDotVisitor() {
        super(new StringWriter());
    }

    /*
     * Generic functions used by different visit* functions
     */

    public void visitTFunction(/*@ non_null @*/ TFunction n) throws java.io.IOException{

	/* declaration of the node */
	out.write(n.dotId()); /* unique */

	out.write(" [label = \""+n.getShortName());

	// write the type (if exists)
	if(n.type!=null){
	    /* the old type is contained into the 'type' field which has
	       type 'typeInfo' ouf! */

	    out.write("\\n\\["+n.getType()+"\\]"); 
	}
    
	out.write("\"];\n");

	TNode nTemp = null;

	/* add all the sons */
	for(int i = 0; i <= n.sons.size() - 1; i++){

	    out.write(n.dotId()+" -> ");
	    
	    nTemp = n.getChildAt(i);
	    out.write(nTemp.dotId());

	    /* red arrow for variables, green one for value */
	    if(nTemp instanceof TName)
		out.write(" [color = red]");
	    else if(nTemp instanceof TLiteral)
		out.write(" [color = green]");

	    out.write(";\n");

	    /* recursive call on the sons */
	    nTemp.accept(this);
	}

    }

    public void visitTVariable(/*@ non_null @*/ TVariable n) throws java.io.IOException{

	out.write(n.dotId());

	/* add fancy stuff, like square box o_O */
	out.write(" [shape=box, label=\"");

	// write the type (if exists)
	if(n.type!=null){
	    /* the old type is contained into the 'type' field which has
	       type 'typeInfo' ouf! */

	    out.write("\\["+n.getType()+"\\]"); 
	}
	
	//out.write("\"];\n");
    }

    /* 
     * non automatic generated class
     */ 
    public void visitTName(/*@ non_null @*/ TName n) throws java.io.IOException{
	
	out.write(n.dotId());

	/* add fancy stuff, like square box o_O */
	out.write(" [shape=box, label=\"");
	
	out.write("\\["+n.getType()+"\\]");
	
	/* append the name of the variable */
	out.write("\\n"+n.name);

	out.write("\"];\n");
    }

    public void visitTRoot(/*@ non_null @*/ TRoot n) throws java.io.IOException{

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
    public void visitTBoolImplies(/*@ non_null @*/ TBoolImplies n) throws java.io.IOException{
	visitTFunction(n);
    }

    public void visitTBoolAnd(/*@ non_null @*/ TBoolAnd n) throws java.io.IOException{
	visitTFunction(n);
    }

    public void visitTBoolOr(/*@ non_null @*/ TBoolOr n) throws java.io.IOException{
	visitTFunction(n);
    }

    public void visitTBoolNot(/*@ non_null @*/ TBoolNot n) throws java.io.IOException{
	visitTFunction(n);
    }

    public void visitTBoolEQ(/*@ non_null @*/ TBoolEQ n) throws java.io.IOException{
	visitTFunction(n);
    }

    public void visitTBoolNE(/*@ non_null @*/ TBoolNE n) throws java.io.IOException{
	visitTFunction(n);
    }

    public void visitTAllocLT(/*@ non_null @*/ TAllocLT n) throws java.io.IOException{
	visitTFunction(n);
    }

    public void visitTAllocLE(/*@ non_null @*/ TAllocLE n) throws java.io.IOException{
	visitTFunction(n);
    }

    public void visitTAnyEQ(/*@ non_null @*/ TAnyEQ n) throws java.io.IOException{
	visitTFunction(n);
    }

    public void visitTAnyNE(/*@ non_null @*/ TAnyNE n) throws java.io.IOException{
	visitTFunction(n);
    }

    public void visitTIntegralEQ(/*@ non_null @*/ TIntegralEQ n) throws java.io.IOException{
	visitTFunction(n);
    }

    public void visitTIntegralGE(/*@ non_null @*/ TIntegralGE n) throws java.io.IOException{
	visitTFunction(n);
    }

    public void visitTIntegralGT(/*@ non_null @*/ TIntegralGT n) throws java.io.IOException{
	visitTFunction(n);
    }

    public void visitTIntegralLE(/*@ non_null @*/ TIntegralLE n) throws java.io.IOException{
	visitTFunction(n);
    }

    public void visitTIntegralLT(/*@ non_null @*/ TIntegralLT n) throws java.io.IOException{
	visitTFunction(n);
    }

    public void visitTIntegralNE(/*@ non_null @*/ TIntegralNE n) throws java.io.IOException{
	visitTFunction(n);
    }

    public void visitTIntegralAdd(/*@ non_null @*/ TIntegralAdd n) throws java.io.IOException{
	visitTFunction(n);
    }

    public void visitTIntegralDiv(/*@ non_null @*/ TIntegralDiv n) throws java.io.IOException{
	visitTFunction(n);
    }

    public void visitTIntegralMod(/*@ non_null @*/ TIntegralMod n) throws java.io.IOException{
	visitTFunction(n);
    }

    public void visitTIntegralMul(/*@ non_null @*/ TIntegralMul n) throws java.io.IOException{
	visitTFunction(n);
    }

    public void visitTFloatEQ(/*@ non_null @*/ TFloatEQ n) throws java.io.IOException{
	visitTFunction(n);
    }

    public void visitTFloatGE(/*@ non_null @*/ TFloatGE n) throws java.io.IOException{
	visitTFunction(n);
    }

    public void visitTFloatGT(/*@ non_null @*/ TFloatGT n) throws java.io.IOException{
	visitTFunction(n);
    }

    public void visitTFloatLE(/*@ non_null @*/ TFloatLE n) throws java.io.IOException{
	visitTFunction(n);
    }

    public void visitTFloatLT(/*@ non_null @*/ TFloatLT n) throws java.io.IOException{
	visitTFunction(n);
    }

    public void visitTFloatNE(/*@ non_null @*/ TFloatNE n) throws java.io.IOException{
	visitTFunction(n);
    }

    public void visitTFloatAdd(/*@ non_null @*/ TFloatAdd n) throws java.io.IOException{
	visitTFunction(n);
    }

    public void visitTFloatDiv(/*@ non_null @*/ TFloatDiv n) throws java.io.IOException{
	visitTFunction(n);
    }

    public void visitTFloatMod(/*@ non_null @*/ TFloatMod n) throws java.io.IOException{
	visitTFunction(n);
    }

    public void visitTFloatMul(/*@ non_null @*/ TFloatMul n) throws java.io.IOException{
	visitTFunction(n);
    }

    public void visitTLockLE(/*@ non_null @*/ TLockLE n) throws java.io.IOException{
	visitTFunction(n);
    }

    public void visitTLockLT(/*@ non_null @*/ TLockLT n) throws java.io.IOException{
	visitTFunction(n);
    }

    public void visitTRefEQ(/*@ non_null @*/ TRefEQ n) throws java.io.IOException{
	visitTFunction(n);
    }

    public void visitTRefNE(/*@ non_null @*/ TRefNE n) throws java.io.IOException{
	visitTFunction(n);
    }

    public void visitTTypeEQ(/*@ non_null @*/ TTypeEQ n) throws java.io.IOException{
	visitTFunction(n);
    }

    public void visitTTypeNE(/*@ non_null @*/ TTypeNE n) throws java.io.IOException{
	visitTFunction(n);
    }

    public void visitTTypeLE(/*@ non_null @*/ TTypeLE n) throws java.io.IOException{
	visitTFunction(n);
    }

    public void visitTCast(/*@ non_null @*/ TCast n) throws java.io.IOException{
	visitTFunction(n);
    }

    public void visitTIs(/*@ non_null @*/ TIs n) throws java.io.IOException{
	visitTFunction(n);
    }

    public void visitTSelect(/*@ non_null @*/ TSelect n) throws java.io.IOException{
	visitTFunction(n);
    }

    public void visitTStore(/*@ non_null @*/ TStore n) throws java.io.IOException{
	visitTFunction(n);
    }

    public void visitTTypeOf(/*@ non_null @*/ TTypeOf n) throws java.io.IOException{
	visitTFunction(n);
    }

    public void visitTForAll(/*@ non_null @*/ TForAll n) throws java.io.IOException{
	visitTFunction(n);
    }

    public void visitTExist(/*@ non_null @*/ TExist n) throws java.io.IOException{
	visitTFunction(n);
    }

    public void visitTIsAllocated(/*@ non_null @*/ TIsAllocated n) throws java.io.IOException{
	visitTFunction(n);
    }

    public void visitTEClosedTime(/*@ non_null @*/ TEClosedTime n) throws java.io.IOException{
	visitTFunction(n);
    }

    public void visitTFClosedTime(/*@ non_null @*/ TFClosedTime n) throws java.io.IOException{
	visitTFunction(n);
    }

    public void visitTAsElems(/*@ non_null @*/ TAsElems n) throws java.io.IOException{
	visitTFunction(n);
    }

    public void visitTAsField(/*@ non_null @*/ TAsField n) throws java.io.IOException{
	visitTFunction(n);
    }

    public void visitTAsLockSet(/*@ non_null @*/ TAsLockSet n) throws java.io.IOException{
	visitTFunction(n);
    }

    public void visitTArrayLength(/*@ non_null @*/ TArrayLength n) throws java.io.IOException{
	visitTFunction(n);
    }

    public void visitTArrayFresh(/*@ non_null @*/ TArrayFresh n) throws java.io.IOException{
	visitTFunction(n);
    }

    public void visitTArrayShapeOne(/*@ non_null @*/ TArrayShapeOne n) throws java.io.IOException{
	visitTFunction(n);
    }

    public void visitTArrayShapeMore(/*@ non_null @*/ TArrayShapeMore n) throws java.io.IOException{
	visitTFunction(n);
    }

    public void visitTIsNewArray(/*@ non_null @*/ TIsNewArray n) throws java.io.IOException{
	visitTFunction(n);
    }

    public void visitTString(/*@ non_null @*/ TString n) throws java.io.IOException{
	visitTVariable(n);

	out.write("\\n"+n.value);
	out.write("\"];\n");
    }	

    public void visitTBoolean(/*@ non_null @*/ TBoolean n) throws java.io.IOException{
	visitTVariable(n);

	out.write("\\n"+Boolean.toString(n.value));
	out.write("\"];\n");
    }
    
    public void visitTChar(/*@ non_null @*/ TChar n) throws java.io.IOException{
	visitTVariable(n);

	out.write("\\n"+Character.toString(n.value));
	out.write("\"];\n");
    }

    public void visitTInt(/*@ non_null @*/ TInt n) throws java.io.IOException{
	visitTVariable(n);

	out.write("\\n"+Integer.toString(n.value));
	out.write("\"];\n");
    }
    
    public void visitTFloat(/*@ non_null @*/ TFloat n) throws java.io.IOException{
	visitTVariable(n);

	out.write("\\n"+Float.toString(n.value));
	out.write("\"];\n");
    }

    public void visitTDouble(/*@ non_null @*/ TDouble n) throws java.io.IOException{
	visitTVariable(n);
	
	out.write("\\n"+Double.toString(n.value));
	out.write("\"];\n");
    }
    
    public void visitTNull(/*@ non_null @*/ TNull n) throws java.io.IOException{
	visitTVariable(n);

	out.write("\\nnull\"];\n");
    }

	public void visitTMethodCall(/*@non_null*/TMethodCall call)  throws java.io.IOException{
		// TODO Auto-generated method stub
		
	}

	public void visitTUnset(/*@non_null*/TUnset n) throws java.io.IOException {
		// TODO Auto-generated method stub
		
	}

	public void visitTIntegralSub(/*@non_null*/TIntegralSub sub) throws java.io.IOException {
		// TODO Auto-generated method stub
		
	}

    public void visitTSum(/*@non_null*/TSum s) {
		// TODO Auto-generated method stub
		
	}
}
