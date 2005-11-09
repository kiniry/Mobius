package escjava.vcGeneration.coq;

import escjava.vcGeneration.TAllocLE;
import escjava.vcGeneration.TAllocLT;
import escjava.vcGeneration.TAnyEQ;
import escjava.vcGeneration.TAnyNE;
import escjava.vcGeneration.TArrayFresh;
import escjava.vcGeneration.TArrayLength;
import escjava.vcGeneration.TArrayShapeMore;
import escjava.vcGeneration.TArrayShapeOne;
import escjava.vcGeneration.TAsElems;
import escjava.vcGeneration.TAsField;
import escjava.vcGeneration.TAsLockSet;
import escjava.vcGeneration.TBoolAnd;
import escjava.vcGeneration.TBoolEQ;
import escjava.vcGeneration.TBoolImplies;
import escjava.vcGeneration.TBoolNE;
import escjava.vcGeneration.TBoolNot;
import escjava.vcGeneration.TBoolOr;
import escjava.vcGeneration.TBoolean;
import escjava.vcGeneration.TCast;
import escjava.vcGeneration.TChar;
import escjava.vcGeneration.TDouble;
import escjava.vcGeneration.TEClosedTime;
import escjava.vcGeneration.TExist;
import escjava.vcGeneration.TFClosedTime;
import escjava.vcGeneration.TFloat;
import escjava.vcGeneration.TFloatAdd;
import escjava.vcGeneration.TFloatDiv;
import escjava.vcGeneration.TFloatEQ;
import escjava.vcGeneration.TFloatGE;
import escjava.vcGeneration.TFloatGT;
import escjava.vcGeneration.TFloatLE;
import escjava.vcGeneration.TFloatLT;
import escjava.vcGeneration.TFloatMod;
import escjava.vcGeneration.TFloatMul;
import escjava.vcGeneration.TFloatNE;
import escjava.vcGeneration.TForAll;
import escjava.vcGeneration.TFunction;
import escjava.vcGeneration.TInt;
import escjava.vcGeneration.TIntegralAdd;
import escjava.vcGeneration.TIntegralDiv;
import escjava.vcGeneration.TIntegralEQ;
import escjava.vcGeneration.TIntegralGE;
import escjava.vcGeneration.TIntegralGT;
import escjava.vcGeneration.TIntegralLE;
import escjava.vcGeneration.TIntegralLT;
import escjava.vcGeneration.TIntegralMod;
import escjava.vcGeneration.TIntegralMul;
import escjava.vcGeneration.TIntegralNE;
import escjava.vcGeneration.TIntegralSub;
import escjava.vcGeneration.TIs;
import escjava.vcGeneration.TIsAllocated;
import escjava.vcGeneration.TIsNewArray;
import escjava.vcGeneration.TLiteral;
import escjava.vcGeneration.TLockLE;
import escjava.vcGeneration.TLockLT;
import escjava.vcGeneration.TMethodCall;
import escjava.vcGeneration.TName;
import escjava.vcGeneration.TNode;
import escjava.vcGeneration.TNull;
import escjava.vcGeneration.TRefEQ;
import escjava.vcGeneration.TRefNE;
import escjava.vcGeneration.TRoot;
import escjava.vcGeneration.TSelect;
import escjava.vcGeneration.TStore;
import escjava.vcGeneration.TString;
import escjava.vcGeneration.TTypeEQ;
import escjava.vcGeneration.TTypeLE;
import escjava.vcGeneration.TTypeNE;
import escjava.vcGeneration.TTypeOf;
import escjava.vcGeneration.TUnset;
import escjava.vcGeneration.TVisitor;
import escjava.vcGeneration.VariableInfo;


class TCoqVisitor extends TVisitor {

    protected CoqStringBuffer out = null;
    private TCoqVisitor tcbv; 
    private CoqProver p;
    TCoqVisitor(CoqProver prover){
    	out = new CoqStringBuffer(super.out);
    	p= prover;
    	tcbv = new TCoqBoolVisitor(out, p);
    }
    
    protected TCoqVisitor(CoqStringBuffer out, CoqProver p){
    	this.out = out;
    	tcbv = this;
    	this.p = p;
    }
    /*
     * General Function
     * You give the operator at the first argument and then it outputs
     * op (son1, son2 ...)
     * )
     */
    public void genericFun(/*@ non_null @*/ String s, TFunction n){

	out.appendI("("+ s+" ");
	
	int i =0;
	for(; i < n.sons.size(); i++) {
		
	    n.getChildAt(i).accept(this);

	    /*
	     * If not last, output a space
	     */
	    if(i != n.sons.size() - 1)
		out.appendN(" ");
	}
	out.appendN(")");

	if((n.getChildAt(--i)) instanceof TName || (n.getChildAt(--i)) instanceof TLiteral)
	    out.reduceIwNl();
	else
	    out.reduceI();
	    
    }
    public void propFun(/*@ non_null @*/ String s, TFunction n){

    	out.appendI("("+ s+" ");
    	
    	int i =0;
    	for(; i < n.sons.size(); i++) {
    		
    	    n.getChildAt(i).accept(tcbv);

    	    /*
    	     * If not last, output a space
    	     */
    	    if(i != n.sons.size() - 1)
    		out.appendN(" ");
    	}
    	out.appendN(")");

    	if((n.getChildAt(--i)) instanceof TName || (n.getChildAt(--i)) instanceof TLiteral)
    	    out.reduceIwNl();
    	else
    	    out.reduceI();
    	    
        }
    /*
     * Function/Operator with arity 1 :
     * (op X)
     */
    public void unaryGeneric(/*@ non_null @*/ String s, TFunction n){

	if(n.sons.size() != 1)
	    System.err.println("java.escjava.vcGeneration.TCoqVisitor.unFun : an unary operator named "+s+" has a number of sons equals to "+n.sons.size()+" which is different from 1");
	out.appendI("(");
	out.appendN(s);
	out.appendN(" (");
	n.getChildAt(0).accept(this);
	out.appendN("))");
	if((n.getChildAt(0)) instanceof TName || (n.getChildAt(0)) instanceof TLiteral)
	    out.reduceIwNl();
	else
	    out.reduceI();
	    
    }

    /*
     * You give the operator at the first argument and then it outputs
     *   (son1 
        op 
	  son2 ... 
	op 
	  sonN)
     */
    public void genericOp(/*@ non_null @*/ String s, TFunction n){

	out.appendI("(");

	int i =0;
//	for(int j = 0; j < n.sons.size(); j++)
//		out.appendN("(");
	for(; i < n.sons.size(); i++) {
		out.appendN("(");
	    n.getChildAt(i).accept(this);
	    //if(i != 0)
		out.appendN(")");
	    /*
	     * not the last
	     */
	    if(i != n.sons.size() - 1) {
	    	out.appendN("\n");
	    	out.append(s);
	    }
	    
	    out.appendN(" ");
	}
	//for(int j = 0; j <= i; j++)
		out.appendN(")");
	out.reduceI();
    }
    public void genericPropOp(/*@ non_null @*/ String s, TFunction n){

    	out.appendI("(");

    	int i =0;
//    	for(int j = 0; j < n.sons.size(); j++)
//    		out.appendN("(");
    	for(; i < n.sons.size(); i++) {
    		out.appendN("(");
    	    n.getChildAt(i).accept(this);
    	    if(n.getChildAt(i) instanceof TName)
    	    	out.appendN(" = true");
    	    //if(i != 0)
    		out.appendN(")");
    	    /*
    	     * not the last
    	     */
    	    if(i != n.sons.size() - 1) {
    	    	out.appendN("\n");
    	    	out.append(s);
    	    }
    	    
    	    out.appendN(" ");
    	}
    	//for(int j = 0; j <= i; j++)
    		out.appendN(")");
    	out.reduceI();
        }
    /*
     * Function/Operator with arity 1 :
     * (op X)
     */
    public void unaryProp(/*@ non_null @*/ String s, TFunction n){

	if(n.sons.size() != 1)
	    System.err.println("java.escjava.vcGeneration.TCoqVisitor.unFun : an unary operator named "+s+" has a number of sons equals to "+n.sons.size()+" which is different from 1");
	out.appendI("(");
	out.appendN(s);
	out.appendN(" (");
	n.getChildAt(0).accept(this);
	 if(n.getChildAt(0) instanceof TName)
	    	out.appendN(" = true");
	out.appendN("))");
	if((n.getChildAt(0)) instanceof TName || (n.getChildAt(0)) instanceof TLiteral)
	    out.reduceIwNl();
	else
	    out.reduceI();
	    
    }
    /*
     * Function for binary operator
     * You give the operator at the first argument and then it outputs
     * (son1 
     * op 
     * son2)
     * 
     * If son1 is a variable, op isn't on the next line
     * If son2 is a variable, it doesn't go to next line.
     */
    public void binOp(/*@ non_null @*/ String s, TFunction n){

	if(n.sons.size() != 2)
	    System.err.println("java.escjava.vcGeneration.TCoqVisitor : a binary operator named "+s+" has a number of sons equals to "+n.sons.size()+" which is different from 2");

	out.appendI("(");
	
	n.getChildAt(0).accept(this);

	if(! ((n.getChildAt(0)) instanceof TName || (n.getChildAt(0)) instanceof TLiteral)) {
	    out.appendN("\n");
	    out.append("");
	}
	
	out.appendN(" "+s+" ");
	n.getChildAt(1).accept(this);
	out.appendN(")");
	if((n.getChildAt(1)) instanceof TName || (n.getChildAt(1)) instanceof TLiteral)
	    out.reduceIwNl();
	else
	    out.reduceI();
	    
    }
    public void spacedBinOp(/*@ non_null @*/ String s, TFunction n){

    	if(n.sons.size() < 2 )
    	    System.err.println("java.escjava.vcGeneration.TCoqVisitor : the spaced out binary operator named "+s+" has a number of sons equals to "+n.sons.size()+" which is different from 2");

    	out.appendI("(");
    	for(int i =0; i < n.sons.size() - 1; i++) {
    		
    		if(i != 0) {
    			out.appendN(" /\\ (");
    		}
    		else
    			out.appendN("(");
    		// Frankie says... no equality on Prop
    		n.getChildAt(i).accept(tcbv);    	
    		out.appendN(" "+s+" ");
    		n.getChildAt(i+1).accept(tcbv);
    		out.appendN(")");
    	}
    	out.appendN(")");
    	if((n.getChildAt(1)) instanceof TName || (n.getChildAt(1)) instanceof TLiteral)
    	    out.reduceIwNl();
    	else
    	    out.reduceI();
    	    
        }
    /* 
     * non automatic generated class
     */ 
    public void visitTName(/*@ non_null @*/ TName n){

	/*
	 * This call handles everything, ie if n is a variable or a type name
	 */
    	VariableInfo vi = TNode.getVariableInfo(n.name);
    	String name = p.getVariableInfo(vi);
    	if(name.equals("Z"))
    		name = "T_Z";
		out.appendN(name);
    }

    public void visitTRoot(/*@ non_null @*/ TRoot n){
	
	for(int i = 0; i <= n.sons.size() - 1; i++)
	    n.getChildAt(i).accept(this);

    }

    /*
     * class created using the perl script
     */
    public void visitTBoolImplies(/*@ non_null @*/ TBoolImplies n){
    	genericPropOp("->", n);
    }

    public void visitTBoolAnd(/*@ non_null @*/ TBoolAnd n){
    	genericPropOp("/\\", n);
    }

    public void visitTBoolOr(/*@ non_null @*/ TBoolOr n){
    	genericPropOp("\\/", n);
//    	out.appendI("(");
//
//    	int i =0;
//    	System.out.print("hello > " + n.sons.size());
//    	for(; i < n.sons.size(); i++) {
//    		
//    		if(i != 0) {
//    			if(n.getChildAt(i - 1) instanceof TBoolNot) {
//    				out.appendN("\n");
//            		out.append("->");
//    			}
//    			else {
//    				out.appendN("\n");
//    				out.append("\\/");
//    			}
//        	}
//    		out.appendN("(");
//    		if((i !=  n.sons.size() - 1) && (n.getChildAt(i) instanceof TBoolNot)) {
//    			((TBoolNot)n.getChildAt(i)).getChildAt(0).accept(this);
//    		}
//    		else {
//    			n.getChildAt(i).accept(this);
//    		}
//
//    	    /*
//    	     * not the last
//    	     */
//    	    
//
//    	    out.appendN(" ");
//    	}
//    	System.out.println();
//    	for(int j = 0; j <= i; j++)
//    		out.appendN(")");
//    	out.reduceI();
    	
    }

    public void visitTBoolNot(/*@ non_null @*/ TBoolNot n){
    	unaryProp("not ", n);
    }
    
    public void visitTBoolEQ(/*@ non_null @*/ TBoolEQ n){
    	String s = "=";
    	if(n.sons.size() < 2 )
    	    System.err.println("java.escjava.vcGeneration.TCoqVisitor : the spaced out binary operator named "+s+" has a number of sons equals to "+n.sons.size()+" which is different from 2");

    	out.appendI("(");
    	for(int i =0; i < n.sons.size() - 1; i++) {
    		
    		if(i != 0) {
    			out.appendN(" /\\ (");
    		}
    		else
    			out.appendN("(");
    		n.getChildAt(i).accept(tcbv);
    		out.appendN(" "+s+" ");
    		n.getChildAt(i+1).accept(tcbv);
    		out.appendN(")");
    	}
    	out.appendN(")");
    	if((n.getChildAt(1)) instanceof TName || (n.getChildAt(1)) instanceof TLiteral)
    	    out.reduceIwNl();
    	else
    	    out.reduceI();
    	    
    
		
    	//spacedBinOp("(* Bool Eq *) =", n);
    }
    
    public void visitTBoolNE(/*@ non_null @*/ TBoolNE n){
    	binOp("<>", n);
    }

    public void visitTAllocLT(/*@ non_null @*/ TAllocLT n){
	binOp("<", n);
    }

    public void visitTAllocLE(/*@ non_null @*/ TAllocLE n){
	binOp("<=", n);
    }

    public void visitTAnyEQ(/*@ non_null @*/ TAnyEQ n){
    	if(n.sons.size() == 2) {
    		Object son = n.sons.get(1);
    		if((son instanceof TAsLockSet) || 
    				(son instanceof TAsElems) ||
    				(son instanceof TAsField)) {
    			out.appendN("True ");
    			return;
    		}
    		
    	}
    	
    	spacedBinOp("(* Any Eq *) =", n);
    	
    }

    public void visitTAnyNE(/*@ non_null @*/ TAnyNE n){
	binOp("<>", n);
    }
    
    public void visitTIntegralEQ(/*@ non_null @*/ TIntegralEQ n){
	binOp(" =", n);
    }
    
    public void visitTIntegralGE(/*@ non_null @*/ TIntegralGE n){
	binOp(">=", n);
    }
    
    public void visitTIntegralGT(/*@ non_null @*/ TIntegralGT n){
	binOp(">", n);
    }

    public void visitTIntegralLE(/*@ non_null @*/ TIntegralLE n){
	binOp("<=", n);
    }
    
    public void visitTIntegralLT(/*@ non_null @*/ TIntegralLT n){
	binOp("<", n);
    }
    
    public void visitTIntegralNE(/*@ non_null @*/ TIntegralNE n){
	binOp("<>", n);
    }
    
    public void visitTIntegralAdd(/*@ non_null @*/ TIntegralAdd n){
	binOp("+", n);
    }
    
    public void visitTIntegralDiv(/*@ non_null @*/ TIntegralDiv n){
	binOp("/", n); 
    }

    public void visitTIntegralMod(/*@ non_null @*/ TIntegralMod n) {
	binOp("mod", n); 
    }

    public void visitTIntegralMul(/*@ non_null @*/ TIntegralMul n){
	binOp("*", n);
    }
    
    public void visitTFloatEQ(/*@ non_null @*/ TFloatEQ n){
    	spacedBinOp("(* Float Eq *) =", n);
    }
				  
    public void visitTFloatGE(/*@ non_null @*/ TFloatGE n){
	binOp(">=", n); 
    }
				  
    public void visitTFloatGT(/*@ non_null @*/ TFloatGT n){
	binOp(">", n); 
    }
				  
    public void visitTFloatLE(/*@ non_null @*/ TFloatLE n){
	binOp("<=", n); 
    }
				  
    public void visitTFloatLT(/*@ non_null @*/ TFloatLT n){
	binOp("<", n); 
    }
				  
    public void visitTFloatNE(/*@ non_null @*/ TFloatNE n){
	binOp("<>", n); 
    }
				  
    public void visitTFloatAdd(/*@ non_null @*/ TFloatAdd n){
	binOp("+", n); 
    }

    public void visitTFloatDiv(/*@ non_null @*/ TFloatDiv n){
	binOp("/", n); 
    }

    public void visitTFloatMod(/*@ non_null @*/ TFloatMod n){
	binOp("mod", n);
    }

    public void visitTFloatMul(/*@ non_null @*/ TFloatMul n){
	binOp("*", n);
    }
			
    // FIXME: LockLE and LockLT have the same symbol
    public void visitTLockLE(/*@ non_null @*/ TLockLE n){
	binOp("lockLess", n);
    }

    public void visitTLockLT(/*@ non_null @*/ TLockLT n){
	binOp("lockLess", n);
    }
				  
    public void visitTRefEQ(/*@ non_null @*/ TRefEQ n){
    	spacedBinOp("(* Ref Eq *) =", n);
    }
				  
    public void visitTRefNE(/*@ non_null @*/ TRefNE n){
	binOp("<>", n);
    }
				  
    public void visitTTypeEQ(/*@ non_null @*/ TTypeEQ n){
    	spacedBinOp("(* Type Eq *) =", n);
    }
				  
    public void visitTTypeNE(/*@ non_null @*/ TTypeNE n){
	binOp("<>", n);
    }
				  
    public void visitTTypeLE(/*@ non_null @*/ TTypeLE n){
	genericFun("subtypes", n); //
    }
	
    public void visitTCast(/*@ non_null @*/ TCast n){
	genericFun("cast", n);
    }
			
    public void visitTIs(/*@ non_null @*/ TIs n){
    	//genericFun("subtypes", n); //
	out.appendN(" True");

	//genericFun("isa?", n);
    }
				  
    public void visitTSelect(/*@ non_null @*/ TSelect n){
    	String pre = "";
    	if(TNode.$integer.equals(((TNode)n.sons.get(1)).type))
    		pre = "arr";
    	if(TNode.$integer.equals(n.type))
    		genericFun(pre +"IntHeap.select ", n);
    	else if(TNode.$boolean.equals(n.type))
    		propFun(pre +"BoolHeap.select ", n);
    	else
    		genericFun(pre +"RefHeap.select ", n);
    }
    public void visitTStore(/*@ non_null @*/ TStore n){
    	String pre = "";
    	if(TNode.$integer.equals(((TNode)n.sons.get(1)).type))
    		pre = "arr";
    	if(TNode.$integer.equals(((TNode)n.sons.get(2)).type))
    		genericFun("IntHeap." + pre + "store ", n);
    	else if(TNode.$boolean.equals(((TNode)n.sons.get(2)).type))
    		propFun("BoolHeap." + pre +"store ", n);
    	else
    		genericFun("RefHeap." + pre + "store ", n);
    }

    public void visitTTypeOf(/*@ non_null @*/ TTypeOf n){
	genericFun("typeof",n);
    }

    // fixme not handled atm
    public void visitTForAll(/*@ non_null @*/ TForAll n){
    	out.appendI("(forall ");	
    	int i =0;
    	StringBuffer sb = new StringBuffer();
    	//n.generateDeclarations(sb);
    	out.appendN(sb.toString());
    	for(; i < n.sons.size(); i++) {
    	    TNode a = n.getChildAt(i);
    	    
    	    /*
    	     * If not last, output a space
    	     */
    	    if(!(a instanceof TName)) {
    	    	break;
    	    }
    	    
    	    out.appendN( "(");
    	    TName var = (TName) a;
    	    this.visitTName(var);
    	    
    	    out.appendN(  ": "+ p.getTypeInfo(TNode.getVariableInfo(var.name).type) + ")");
    	    
    	}
    	out.appendN(","); 
    	if( i <n.sons.size() - 1)
    		i++;
    	//for(; i < n.sons.size(); i++) {
    	    TNode a = n.getChildAt(i);
    	    out.appendN(" ");    
    	   	a.accept(this);
    	    	
    	//}
    	out.appendN(")");
    	 out.reduceI();
    }

    public void visitTExist(/*@ non_null @*/ TExist n){
	out.appendN("(* TExist *) True");
    }
    //
				  
    public void visitTIsAllocated(/*@ non_null @*/ TIsAllocated n){
	genericFun("isAllocated", n);
    }

    public void visitTEClosedTime(/*@ non_null @*/ TEClosedTime n){
	genericFun("eClosedTime", n);
    }
				  
    public void visitTFClosedTime(/*@ non_null @*/ TFClosedTime n){
	genericFun("fClosedTime", n);
    }
    public void visitTAsElems(/*@ non_null @*/ TAsElems n){
	genericFun("asElems", n);
    }
				  
    public void visitTAsField(/*@ non_null @*/ TAsField n){
	genericFun("asField", n);
    }
				  
    public void visitTAsLockSet(/*@ non_null @*/ TAsLockSet n){
    	genericFun("asLockSet", n);
    	
    }
				  
    public void visitTArrayLength(/*@ non_null @*/ TArrayLength n){
    	genericFun("arrayLength", n);
    }
    public void visitTArrayFresh(/*@ non_null @*/ TArrayFresh n){
    	if(TNode.$boolean.equals(n.getChildAt(6).type)) {
    		String s= "arrayFreshBool";
    	
	    	out.appendI("("+ s+" ");
	    	
	    	int i =0;
	    	for(; i < n.sons.size(); i++) {
	    		
	    	    n.getChildAt(i).accept(tcbv);
	
	    	    /*
	    	     * If not last, output a space
	    	     */
	    	    if(i != n.sons.size() - 1)
	    		out.appendN(" ");
	    	}
	    	out.appendN(")");
	
	    	if((n.getChildAt(--i)) instanceof TName || (n.getChildAt(--i)) instanceof TLiteral)
	    	    out.reduceIwNl();
	    	else
	    	    out.reduceI();
	    }
    	else
    		genericFun("arrayFresh", n);     	
    	
    }
    public void visitTArrayShapeOne(/*@ non_null @*/ TArrayShapeOne n){
    	genericFun("arrayShapeOne", n);
    }
    public void visitTArrayShapeMore(/*@ non_null @*/ TArrayShapeMore n){
    	genericFun("arrayShapeMore", n);
    }
    public void visitTIsNewArray(/*@ non_null @*/ TIsNewArray n){
    	genericFun("isNewArray", n);
    }
    public void visitTString(/*@ non_null @*/ TString n){
    	out.appendN(" (typeof " + n.value+ ")" );
    }

    public void visitTBoolean(/*@ non_null @*/ TBoolean n){
	if(n.value)
	    out.appendN(" (* bool*) True");
	else
	    out.appendN("False");
    }

    public void visitTChar(/*@ non_null @*/ TChar n){
	out.appendN(" (* a char value *)"+n.value);
    }

    // "" is added to be able to make this call
    // without redefining append for each type
    // It works because of the way the java compiler
    // handles the + operator
    public void visitTInt(/*@ non_null @*/ TInt n){
    	out.appendN(n.value + " "); //fixme not sure // seems to be ok
    }
				  
    public void visitTFloat(/*@ non_null @*/ TFloat n){
	out.appendN(" (* a float value *)"+n.value);
    }
				  
    public void visitTDouble(/*@ non_null @*/ TDouble n){
	out.appendN(" (* a double value *)"+n.value); // fixme
    }
    public void visitTNull(/*@ non_null @*/ TNull n){
	out.appendN(" null");
    }

	public void visitTMethodCall(TMethodCall call) {
		genericFun(p.getVariableInfo(call.getName()), call);
	}

	public void visitTUnset(TUnset n) {
		genericFun("unset", n);
	}

	public void visitTIntegralSub(TIntegralSub n) {
		binOp("-", n);
	}

}
