package escjava.vcGeneration.pvs;

import java.io.*;

import escjava.vcGeneration.*;

public class TPvsVisitor extends TVisitor {
    
    TPvsVisitor(Writer out) {
        super(out);
    }
    
    /**
     * General Function
     * You give the operator at the first argument and then it outputs
     * op (son1, son2 ...)
     * )
     */
    public void genericFun(/*@ non_null @*/String s, TFunction n) throws IOException{

        lib.appendI(s + " (");

        for (int i = 0; i < n.sons.size(); i++) {
            n.getChildAt(i).accept(this);

            /*
             * If not last, output a comma
             */
            if (i != n.sons.size() - 1)
                lib.appendN(", ");
        }

        lib.appendN(")");

        int lastChild = n.sons.size() - 1;
        if ((n.getChildAt(lastChild)) instanceof TName
                || (n.getChildAt(lastChild)) instanceof TLiteral)
            lib.reduceIwNl();
        else
            lib.reduceI();

    }

    /**
     * Function/Operator with arity 1 :
     * (op X)
     */
    public void unaryGeneric(/*@ non_null @*/String s, TFunction n) throws IOException {

        if (n.sons.size() != 1)
            TDisplay.err("An unary operator named " + s
                            + " has a number of sons equals to "
                            + n.sons.size() + " which is different from 1");

        lib.appendI(s);

        n.getChildAt(0).accept(this);

        if ((n.getChildAt(0)) instanceof TName
                || (n.getChildAt(0)) instanceof TLiteral)
            lib.reduceIwNl();
        else
            lib.reduceI();

    }

    /**
     * You give the operator at the first argument and then it outputs
     *   (son1 
     op 
     son2 ... 
     op 
     sonN)
     */
    public void genericOp(/*@ non_null @*/String s, TFunction n) throws IOException {

        lib.appendI("");

        int i = 0;
        for (; i < n.sons.size(); i++) {
            n.getChildAt(i).accept(this);

            /*
             * not the last
             */
            if (i != n.sons.size() - 1) {
                lib.appendN("\n");
                lib.append(s);
            }

            lib.appendN(" ");
        }

        lib.reduceI();
    }

    /**
     * Function for binary operator
     * You give the operator at the first argument and then it outputs
     * (son1 
     * op 
     * son2)
     * 
     * If son1 is a variable, op isn't on the next line
     * If son2 is a variable, it doesn't go to next line.
     */
    public void binOp(/*@ non_null @*/String s, TFunction n) throws IOException {

        if (n.sons.size() != 2)
            TDisplay.err("Binary operator named " + s
                            + " has a number of sons equals to "
                            + n.sons.size() + " which is different from 2");

        lib.appendI("");

        n.getChildAt(0).accept(this);

        if (!((n.getChildAt(0)) instanceof TName || (n.getChildAt(0)) instanceof TLiteral)) {
            lib.appendN("\n");
            lib.append("");
        }

        lib.appendN(" " + s + " ");
        n.getChildAt(1).accept(this);

        if ((n.getChildAt(1)) instanceof TName
                || (n.getChildAt(1)) instanceof TLiteral)
            lib.reduceIwNl();
        else
            lib.reduceI();

    }

    public void visitTName(/*@ non_null @*/TName n) throws IOException {
        /*
         * This call handles everything, ie if n is a variable or a type name
         */
        VariableInfo vi = TNode.getVariableInfo(n.name);
        lib.appendN(vi.getVariableInfo());
    }
    
    public void visitTRoot(/*@ non_null @*/TRoot n) throws IOException {
        for (int i = 0; i <= n.sons.size() - 1; i++)
            n.getChildAt(i).accept(this);
    }

    /*
     * class created using the perl script
     */
    public void visitTBoolImplies(/*@ non_null @*/TBoolImplies n) throws IOException {
        binOp("IMPLIES", n);
    }

    public void visitTBoolAnd(/*@ non_null @*/TBoolAnd n) throws IOException {
        genericOp("AND", n);
    }

    public void visitTBoolOr(/*@ non_null @*/TBoolOr n) throws IOException {
        genericOp("OR", n);
    }

    public void visitTBoolNot(/*@ non_null @*/TBoolNot n) throws IOException {
        unaryGeneric("NOT", n);
    }

    public void visitTBoolEQ(/*@ non_null @*/TBoolEQ n) throws IOException {
        genericOp("=", n);
    }

    public void visitTBoolNE(/*@ non_null @*/TBoolNE n) throws IOException {
        binOp("/=", n);
    }

    public void visitTAllocLT(/*@ non_null @*/TAllocLT n) throws IOException {
        binOp("<", n);
    }

    public void visitTAllocLE(/*@ non_null @*/TAllocLE n) throws IOException {
        binOp("<=", n);
    }

    public void visitTAnyEQ(/*@ non_null @*/TAnyEQ n) throws IOException {
        genericOp("=", n);
    }

    public void visitTAnyNE(/*@ non_null @*/TAnyNE n) throws IOException {
        binOp("/=", n);
    }

    public void visitTIntegralEQ(/*@ non_null @*/TIntegralEQ n) throws IOException {
        binOp("=", n);
    }

    public void visitTIntegralGE(/*@ non_null @*/TIntegralGE n) throws IOException {
        binOp(">=", n);
    }

    public void visitTIntegralGT(/*@ non_null @*/TIntegralGT n) throws IOException {
        binOp(">", n);
    }

    public void visitTIntegralLE(/*@ non_null @*/TIntegralLE n) throws IOException {
        binOp("<=", n);
    }

    public void visitTIntegralLT(/*@ non_null @*/TIntegralLT n) throws IOException {
        binOp("<", n);
    }

    public void visitTIntegralNE(/*@ non_null @*/TIntegralNE n) throws IOException {
        binOp("/=", n);
    }

    public void visitTIntegralAdd(/*@ non_null @*/TIntegralAdd n) throws IOException {
        binOp("+", n);
    }

    public void visitTIntegralDiv(/*@ non_null @*/TIntegralDiv n) throws IOException {
        binOp("/", n);
    }

    public void visitTIntegralMod(/*@ non_null @*/TIntegralMod n) throws IOException {
        binOp("mod", n);
    }

    public void visitTIntegralMul(/*@ non_null @*/TIntegralMul n) throws IOException {
        binOp("*", n);
    }

    public void visitTFloatEQ(/*@ non_null @*/TFloatEQ n) throws IOException {
        binOp("=", n);
    }

    public void visitTFloatGE(/*@ non_null @*/TFloatGE n) throws IOException {
        binOp(">=", n);
    }

    public void visitTFloatGT(/*@ non_null @*/TFloatGT n) throws IOException {
        binOp(">", n);
    }

    public void visitTFloatLE(/*@ non_null @*/TFloatLE n) throws IOException {
        binOp("<=", n);
    }

    public void visitTFloatLT(/*@ non_null @*/TFloatLT n) throws IOException {
        binOp("<", n);
    }

    public void visitTFloatNE(/*@ non_null @*/TFloatNE n) throws IOException {
        binOp("/=", n);
    }

    public void visitTFloatAdd(/*@ non_null @*/TFloatAdd n) throws IOException {
        binOp("+", n);
    }

    public void visitTFloatDiv(/*@ non_null @*/TFloatDiv n) throws IOException {
        binOp("/", n);
    }

    public void visitTFloatMod(/*@ non_null @*/TFloatMod n) throws IOException {
        binOp("mod", n);
    }

    public void visitTFloatMul(/*@ non_null @*/TFloatMul n) throws IOException {
        binOp("*", n);
    }

    // FIXME LockLE and LockLT have the same symbol
    public void visitTLockLE(/*@ non_null @*/TLockLE n) throws IOException {
        binOp("lockLess", n);
    }

    public void visitTLockLT(/*@ non_null @*/TLockLT n) throws IOException {
        binOp("lockLess", n);
    }

    public void visitTRefEQ(/*@ non_null @*/TRefEQ n) throws IOException {
        binOp("=", n);
    }

    public void visitTRefNE(/*@ non_null @*/TRefNE n) throws IOException {
        binOp("/=", n);
    }

    public void visitTTypeEQ(/*@ non_null @*/TTypeEQ n) throws IOException {
        binOp("=", n);
    }

    public void visitTTypeNE(/*@ non_null @*/TTypeNE n) throws IOException {
        binOp("/=", n);
    }

    public void visitTTypeLE(/*@ non_null @*/TTypeLE n) throws IOException {
        genericFun("subtype?", n); //FIXME, maybe it's extends ? // have to check logics semantics..
    }

    public void visitTCast(/*@ non_null @*/TCast n) throws IOException {
        genericFun("cast", n);
    }

    public void visitTIs(/*@ non_null @*/TIs n) throws IOException {

        /*
         * As this node should be simplified in TProofSimplifier, we should not be here.
         */
        TDisplay.err("This node should have been simplified in TProofSimplifier");

        /*
         * As the proof is typed, no need for this operator anymore.
         * FIXME, handle it in a nicer way.
         */
        lib.appendN("TAMERE");

    }

    public void visitTSelect(/*@ non_null @*/TSelect n) throws IOException {
        genericFun("get", n);
    }

    public void visitTStore(/*@ non_null @*/TStore n) throws IOException {
        genericFun("set", n);
    }

    public void visitTTypeOf(/*@ non_null @*/TTypeOf n) throws IOException {
        genericFun("typeOf", n);
    }

    // FIXME not handled atm
    public void visitTForAll(/*@ non_null @*/TForAll n) throws IOException {
        lib.appendN("TRUE");
    }

    public void visitTExist(/*@ non_null @*/TExist n) throws IOException {
        lib.appendN("TRUE");
    }

    //

    public void visitTIsAllocated(/*@ non_null @*/TIsAllocated n) throws IOException {
        genericFun("isAllocated", n);
    }

    public void visitTEClosedTime(/*@ non_null @*/TEClosedTime n) throws IOException {
        genericFun("eClosedTime", n);
    }

    public void visitTFClosedTime(/*@ non_null @*/TFClosedTime n) throws IOException {
        genericFun("fClosedTime", n);
    }

    public void visitTAsElems(/*@ non_null @*/TAsElems n) throws IOException {
        genericFun("asElems", n);
    }

    public void visitTAsField(/*@ non_null @*/TAsField n) throws IOException {
        genericFun("asField", n);
    }

    public void visitTAsLockSet(/*@ non_null @*/TAsLockSet n) throws IOException {
        genericFun("asLockSet", n);
    }

    public void visitTArrayLength(/*@ non_null @*/TArrayLength n) throws IOException {
    }

    public void visitTArrayFresh(/*@ non_null @*/TArrayFresh n) throws IOException {
    }

    public void visitTArrayShapeOne(/*@ non_null @*/TArrayShapeOne n) throws IOException {
    }

    public void visitTArrayShapeMore(/*@ non_null @*/TArrayShapeMore n) throws IOException {
    }

    public void visitTIsNewArray(/*@ non_null @*/TIsNewArray n) throws IOException {
    }

    public void visitTString(/*@ non_null @*/TString n) throws IOException {
    }

    public void visitTBoolean(/*@ non_null @*/TBoolean n) throws IOException {
        if (n.value)
            lib.appendN("TRUE");
        else
            lib.appendN("FALSE");
    }

    public void visitTChar(/*@ non_null @*/TChar n) throws IOException {
        lib.appendN(" |C_" + n.value + "|");
    }

    // "" is added to be able to make this call
    // without redefining append for each type
    // It works because of the way the java compiler
    // handles the + operator
    public void visitTInt(/*@ non_null @*/TInt n) throws IOException {
        lib.appendN("" + n.value); //FIXME not sure // seems to be ok
    }

    public void visitTFloat(/*@ non_null @*/TFloat n) throws IOException {
        lib.appendN(" |F_" + n.value + "|");
    }

    public void visitTDouble(/*@ non_null @*/TDouble n) throws IOException {
        lib.appendN(" |F_" + n.value + "|"); // FIXME
    }

    public void visitTNull(/*@ non_null @*/TNull n) throws IOException {
        lib.appendN(" null");
    }

	public void visitTUnset(/*@non_null*/TUnset n) throws IOException {
		// TODO Auto-generated method stub
		
	}

	public void visitTMethodCall(/*@non_null*/TMethodCall call) throws IOException {
		// TODO Auto-generated method stub
		
	}

	public void visitTIntegralSub(/*@non_null*/TIntegralSub sub) throws IOException {
		// TODO Auto-generated method stub
		
	}

	public void visitTSum(TSum s) {
		// TODO Auto-generated method stub
		
	}

}
