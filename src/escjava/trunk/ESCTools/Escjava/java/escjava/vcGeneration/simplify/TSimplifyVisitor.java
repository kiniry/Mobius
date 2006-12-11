package escjava.vcGeneration.simplify;

import java.io.*;

import escjava.vcGeneration.*;

class TSimplifyVisitor extends TVisitor {

    TSimplifyVisitor(Writer out) {
        super(out);
    }
    
    /*
     * General Function
     * You give the operator at the first argument and then it outputs
     * (op
     *   (son1 son2 ...)
     * )
     */

    public void genericOp(/*@ non_null @*/String s, TFunction n) throws IOException {

        lib.appendI(s);

        int i = 0;
        for (; i <= n.sons.size() - 1; i++)
            n.getChildAt(i).accept(this);

        /*
         * Stick to the old representation :
         * if last child was a variable don't go to next line
         */
        if ((n.getChildAt(--i)) instanceof TName)
            lib.reduceIwNl();
        else
            lib.reduceI();
    }
    
    
    public void visitTName(/*@ non_null @*/TName n) throws IOException {
        /*
         * This call handles everything, ie if n is a variable or a type name
         */
        VariableInfo vi = TNode.getVariableInfo(n.name);
        lib.appendN(" " + vi.getVariableInfo());
    }

    public void visitTRoot(/*@ non_null @*/TRoot n) throws IOException {
        for (int i = 0; i <= n.sons.size() - 1; i++)
            n.getChildAt(i).accept(this);
    }

    /*
     * class created using the perl script
     */
    public void visitTBoolImplies(/*@ non_null @*/TBoolImplies n) throws IOException {
        genericOp("IMPLIES", n);
    }

    // take care special behaviour here, fixme explains why
    public void visitTBoolAnd(/*@ non_null @*/TBoolAnd n) throws IOException {

        lib.appendI("AND");

        int i = 0;
        TNode m = null;
        TNode o = null;

        for (; i <= n.sons.size() - 2; i++) {
            m = n.getChildAt(i);
            o = n.getChildAt(i + 1);

            if (o instanceof TBoolean) {
                TBoolean p = (TBoolean) o;
                if (p.value) // we have a true value just at the bottom
                // of boolean and, it's means that the previous node 
                // need to be outputted as (EQ |@true|
                //                             blabla)
                {
                    lib.appendI("EQ");
                    lib.appendN(" |@true|");
                    m.accept(this);
                    i++;
                }
            } else {
                m.accept(this);
                o.accept(this);

                /* not at the end */
                if (i <= n.sons.size() - 3)
                    i++;
            }
        }

        /*
         * Stick to the old representation :
         * if last child was a variable don't go to next line
         */
        if ((n.getChildAt(i)) instanceof TName)
            lib.reduceIwNl();
        else
            lib.reduceI();

    }

    public void visitTBoolOr(/*@ non_null @*/TBoolOr n) throws IOException {
        genericOp("OR", n);
    }

    public void visitTBoolNot(/*@ non_null @*/TBoolNot n) throws IOException {
        genericOp("NOT", n);
    }

    public void visitTBoolEQ(/*@ non_null @*/TBoolEQ n) throws IOException {
        genericOp("EQ", n);
    }

    public void visitTBoolNE(/*@ non_null @*/TBoolNE n) throws IOException {
        genericOp("NEQ", n);
    }

    public void visitTAllocLT(/*@ non_null @*/TAllocLT n) throws IOException {
        genericOp("<", n);
    }

    public void visitTAllocLE(/*@ non_null @*/TAllocLE n) throws IOException {
        genericOp("<=", n);
    }

    public void visitTAnyEQ(/*@ non_null @*/TAnyEQ n) throws IOException {
        genericOp("EQ", n);
    }

    public void visitTAnyNE(/*@ non_null @*/TAnyNE n) throws IOException {
        genericOp("NEQ", n);
    }

    public void visitTIntegralEQ(/*@ non_null @*/TIntegralEQ n) throws IOException {
        genericOp("EQ", n);
    }

    public void visitTIntegralGE(/*@ non_null @*/TIntegralGE n) throws IOException {
        genericOp(">=", n);
    }

    public void visitTIntegralGT(/*@ non_null @*/TIntegralGT n) throws IOException {
        genericOp(">", n);
    }

    public void visitTIntegralLE(/*@ non_null @*/TIntegralLE n) throws IOException {
        genericOp("<=", n);
    }

    public void visitTIntegralLT(/*@ non_null @*/TIntegralLT n) throws IOException {
        genericOp("<", n);
    }

    public void visitTIntegralNE(/*@ non_null @*/TIntegralNE n) throws IOException {
        genericOp("NEQ", n);
    }

    public void visitTIntegralAdd(/*@ non_null @*/TIntegralAdd n) throws IOException {
        genericOp("+", n);
    }

    public void visitTIntegralDiv(/*@ non_null @*/TIntegralDiv n) throws IOException {
        genericOp("integralDiv", n);
    }

    public void visitTIntegralMod(/*@ non_null @*/TIntegralMod n) throws IOException {
        genericOp("integralMod", n);
    }

    public void visitTIntegralMul(/*@ non_null @*/TIntegralMul n) throws IOException {
        genericOp("*", n);
    }

    public void visitTFloatEQ(/*@ non_null @*/TFloatEQ n) throws IOException {
        genericOp("floatingEQ", n);
    }

    public void visitTFloatGE(/*@ non_null @*/TFloatGE n) throws IOException {
        genericOp("floatingGE", n);
    }

    public void visitTFloatGT(/*@ non_null @*/TFloatGT n) throws IOException {
        genericOp("floatingGT", n);
    }

    public void visitTFloatLE(/*@ non_null @*/TFloatLE n) throws IOException {
        genericOp("floatingLE", n);
    }

    public void visitTFloatLT(/*@ non_null @*/TFloatLT n) throws IOException {
        genericOp("floatingGE", n);
    }

    public void visitTFloatNE(/*@ non_null @*/TFloatNE n) throws IOException {
        genericOp("floatingNE", n);
    }

    public void visitTFloatAdd(/*@ non_null @*/TFloatAdd n) throws IOException {
        genericOp("floatingAdd", n);
    }

    public void visitTFloatDiv(/*@ non_null @*/TFloatDiv n) throws IOException {
        genericOp("floatingDiv", n);
    }

    public void visitTFloatMod(/*@ non_null @*/TFloatMod n) throws IOException {
        genericOp("floatingMod", n);
    }

    public void visitTFloatMul(/*@ non_null @*/TFloatMul n) throws IOException {
        genericOp("floatingMul", n);
    }

    public void visitTLockLE(/*@ non_null @*/TLockLE n) throws IOException {
        genericOp("lockLE", n);
    }

    public void visitTLockLT(/*@ non_null @*/TLockLT n) throws IOException {
        genericOp("lockLT", n);
    }

    public void visitTRefEQ(/*@ non_null @*/TRefEQ n) throws IOException {
        genericOp("EQ", n);
    }

    public void visitTRefNE(/*@ non_null @*/TRefNE n) throws IOException {
        genericOp("NEQ", n);
    }

    public void visitTTypeEQ(/*@ non_null @*/TTypeEQ n) throws IOException {
        genericOp("EQ", n);
    }

    public void visitTTypeNE(/*@ non_null @*/TTypeNE n) throws IOException {
        genericOp("NEQ", n);
    }

    public void visitTTypeLE(/*@ non_null @*/TTypeLE n) throws IOException {
        genericOp("<:", n);
    }

    public void visitTCast(/*@ non_null @*/TCast n) throws IOException {
        genericOp("cast", n);
    }

    public void visitTIs(/*@ non_null @*/TIs n) throws IOException {

        //add (EQ |@true| blabla )
        lib.appendI("EQ");
        lib.appendN(" |@true|");

        genericOp("is", n);

        lib.reduceI();
    }

    public void visitTSelect(/*@ non_null @*/TSelect n) throws IOException {
        genericOp("select", n);
    }

    public void visitTStore(/*@ non_null @*/TStore n) throws IOException {
        genericOp("store", n);
    }

    public void visitTTypeOf(/*@ non_null @*/TTypeOf n) throws IOException {
        genericOp("typeof", n);
    }

    public void visitTForAll(/*@ non_null @*/TForAll n) throws IOException {
    }

    public void visitTExist(/*@ non_null @*/TExist n) throws IOException {
    }

    public void visitTIsAllocated(/*@ non_null @*/TIsAllocated n) throws IOException {

        //add (EQ |@true| blabla )
        lib.appendI("EQ");
        lib.appendN(" |@true|");

        genericOp("isAllocated", n);

        lib.reduceI();

    }

    public void visitTEClosedTime(/*@ non_null @*/TEClosedTime n) throws IOException {
        genericOp("eClosedTime", n);
    }

    public void visitTFClosedTime(/*@ non_null @*/TFClosedTime n) throws IOException {
        genericOp("fClosedTime", n);
    }

    public void visitTAsElems(/*@ non_null @*/TAsElems n) throws IOException {
        genericOp("asElems", n);
    }

    public void visitTAsField(/*@ non_null @*/TAsField n) throws IOException {
        genericOp("asField", n);
    }

    public void visitTAsLockSet(/*@ non_null @*/TAsLockSet n) throws IOException {
        genericOp("asLockSet", n);
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
            lib.append(" |@true|");
        else
            lib.append(" |bool$false|");
    }

    public void visitTChar(/*@ non_null @*/TChar n) throws IOException {
        lib.appendN(" |C_" + n.value + "|");
    }

    public void visitTInt(/*@ non_null @*/TInt n) throws IOException {
        lib.appendN(" " + n.value); //fixme not sure
    }

    public void visitTFloat(/*@ non_null @*/TFloat n) throws IOException {
        lib.appendN(" |F_" + n.value + "|");
    }

    public void visitTDouble(/*@ non_null @*/TDouble n) throws IOException {
        lib.appendN(" |F_" + n.value + "|"); // fixme
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

	public void visitTSum(/*@non_null@*/ TSum s) {
		// TODO Auto-generated method stub
		
	}

}
