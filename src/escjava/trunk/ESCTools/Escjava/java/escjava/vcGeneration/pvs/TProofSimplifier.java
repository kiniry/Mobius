package escjava.vcGeneration.pvs;

import java.io.*;

import escjava.vcGeneration.*;

class TProofSimplifier extends TVisitor {

    TProofSimplifier() {
        // The term itself is modified, so no need for an output stream here
        super(null);
    }
    
    /*
     * Generic functions used by different visit* functions
     */
    public void visitTFunction(/*@ non_null @*/TFunction n) throws IOException {

        int i = 0;
        int sizeTemp = n.sons.size();

        /* recursive call on the sons */
        for (; i <= n.sons.size() - 1;) {

            sizeTemp = n.sons.size();
            n.getChildAt(i).accept(this);

            /*
             * If a son has been deleted, do not increase index
             */
            if (!(sizeTemp > n.sons.size()))
                ++i;

        }

    }

    /*
     * Methods used to simplify the proof
     */
    /*@
     @ requires indexOfSons >= 0 & indexOfSons <= n.sons.size() - 1;
     @ requires n.sons.contains(m);
     @*/
    public void simplify(/*@ non_null @*/TBoolRes n, TNode m) {

        int i = 0;

        //++
        if ((i = n.sons.indexOf(m)) == -1)
            TDisplay.err(this, "simplify(TBoolAnd n, TNode m)",
                    "!n.sons.contains(m)");
        //++
        else
            n.sons.remove(i);

        /*
         * Behavior of simplification process done here.
         */
        i = n.sons.size();

        if (i >= 2)
            ; // this node still makes sense, do nothing
        else {

            if (i == 1) {
                // check that the remaining node returns a boolean

                //++
                if (!(n.getChildAt(0) instanceof TBoolRes))
                    TDisplay
                            .err(this, "simplify(TBoolRes n, TNode m)",
                                    "Remaining child does not return a boolean, continuing anyway...");
                //++

                /*
                 this piece of code delete the BoolAnd node and add the sons
                 to its parent. 
                 ie changing x -> n -> m to x -> m
                 */
                simplify(n.parent, n, m);
            }

        }

    }

    /*
     * Node m is replaced by o in the list of sons of n.
     * Note that after the operation, \old(n.indexOf(m)) == n.indexOf(o);
     */
    /*@
     @ requires n.sons.contains(m);
     @ requires m.sons.contains(o);
     @ ensures n.sons.contains(o);
     @ ensures !n.sons.contains(m);
     @ ensures \old(n.indexOf(m)) == n.indexOf(o);
     @*/
    public void simplify(TFunction n, TNode m, TNode o) {

        int i = n.sons.indexOf(m);

        //++
        if (i == -1)
            TDisplay.err(this, "simplify(TFunction n, TNode m, TNode o)",
                    "!n.contiains(m)");
        //++

        n.sons.setElementAt(o, i);
    }

    /* 
     * non automatic generated class
     */
    public void visitTName(/*@ non_null @*/TName n) throws IOException {
    }
    
    public void visitTRoot(/*@ non_null @*/TRoot n) throws IOException {
        for (int i = 0; i <= n.sons.size() - 1; i++)
            n.getChildAt(i).accept(this);
    }

    /*
     * class created using the perl script
     */
    public void visitTBoolImplies(/*@ non_null @*/TBoolImplies n) throws IOException {
        visitTFunction(n);
    }

    public void visitTBoolAnd(/*@ non_null @*/TBoolAnd n) throws IOException {
        visitTFunction(n);
    }

    public void visitTBoolOr(/*@ non_null @*/TBoolOr n) throws IOException {
        visitTFunction(n);
    }

    public void visitTBoolNot(/*@ non_null @*/TBoolNot n) throws IOException {
        visitTFunction(n);
    }

    public void visitTBoolEQ(/*@ non_null @*/TBoolEQ n) throws IOException {
        visitTFunction(n);
    }

    public void visitTBoolNE(/*@ non_null @*/TBoolNE n) throws IOException {
        visitTFunction(n);
    }

    public void visitTAllocLT(/*@ non_null @*/TAllocLT n) throws IOException {
        visitTFunction(n);
    }

    public void visitTAllocLE(/*@ non_null @*/TAllocLE n) throws IOException {
        visitTFunction(n);
    }

    public void visitTAnyEQ(/*@ non_null @*/TAnyEQ n) throws IOException {
        visitTFunction(n);
    }

    public void visitTAnyNE(/*@ non_null @*/TAnyNE n) throws IOException {
        visitTFunction(n);
    }

    public void visitTIntegralEQ(/*@ non_null @*/TIntegralEQ n) throws IOException {
        visitTFunction(n);
    }

    public void visitTIntegralGE(/*@ non_null @*/TIntegralGE n) throws IOException {
        visitTFunction(n);
    }

    public void visitTIntegralGT(/*@ non_null @*/TIntegralGT n) throws IOException {
        visitTFunction(n);
    }

    public void visitTIntegralLE(/*@ non_null @*/TIntegralLE n) throws IOException {
        visitTFunction(n);
    }

    public void visitTIntegralLT(/*@ non_null @*/TIntegralLT n) throws IOException {
        visitTFunction(n);
    }

    public void visitTIntegralNE(/*@ non_null @*/TIntegralNE n) throws IOException {
        visitTFunction(n);
    }

    public void visitTIntegralAdd(/*@ non_null @*/TIntegralAdd n) throws IOException {
        visitTFunction(n);
    }

    public void visitTIntegralDiv(/*@ non_null @*/TIntegralDiv n) throws IOException {
        visitTFunction(n);
    }

    public void visitTIntegralMod(/*@ non_null @*/TIntegralMod n) throws IOException {
        visitTFunction(n);
    }

    public void visitTIntegralMul(/*@ non_null @*/TIntegralMul n) throws IOException {
        visitTFunction(n);
    }

    public void visitTFloatEQ(/*@ non_null @*/TFloatEQ n) throws IOException {
        visitTFunction(n);
    }

    public void visitTFloatGE(/*@ non_null @*/TFloatGE n) throws IOException {
        visitTFunction(n);
    }

    public void visitTFloatGT(/*@ non_null @*/TFloatGT n) throws IOException {
        visitTFunction(n);
    }

    public void visitTFloatLE(/*@ non_null @*/TFloatLE n) throws IOException {
        visitTFunction(n);
    }

    public void visitTFloatLT(/*@ non_null @*/TFloatLT n) throws IOException {
        visitTFunction(n);
    }

    public void visitTFloatNE(/*@ non_null @*/TFloatNE n) throws IOException {
        visitTFunction(n);
    }

    public void visitTFloatAdd(/*@ non_null @*/TFloatAdd n) throws IOException {
        visitTFunction(n);
    }

    public void visitTFloatDiv(/*@ non_null @*/TFloatDiv n) throws IOException {
        visitTFunction(n);
    }

    public void visitTFloatMod(/*@ non_null @*/TFloatMod n) throws IOException {
        visitTFunction(n);
    }

    public void visitTFloatMul(/*@ non_null @*/TFloatMul n) throws IOException {
        visitTFunction(n);
    }

    public void visitTLockLE(/*@ non_null @*/TLockLE n) throws IOException {
        visitTFunction(n);
    }

    public void visitTLockLT(/*@ non_null @*/TLockLT n) throws IOException {
        visitTFunction(n);
    }

    public void visitTRefEQ(/*@ non_null @*/TRefEQ n) throws IOException {
        visitTFunction(n);
    }

    public void visitTRefNE(/*@ non_null @*/TRefNE n) throws IOException {
        visitTFunction(n);
    }

    public void visitTTypeEQ(/*@ non_null @*/TTypeEQ n) throws IOException {
        visitTFunction(n);
    }

    public void visitTTypeNE(/*@ non_null @*/TTypeNE n) throws IOException {
        visitTFunction(n);
    }

    public void visitTTypeLE(/*@ non_null @*/TTypeLE n) throws IOException {
        visitTFunction(n);
    }

    public void visitTCast(/*@ non_null @*/TCast n) throws IOException {
        visitTFunction(n);
    }

    public void visitTIs(/*@ non_null @*/TIs n) throws IOException {

        if (n.parent instanceof TBoolRes) {
            TBoolRes nTemp = (TBoolRes) n.parent;
            simplify(nTemp, n);
        } else
            TDisplay.err(this, "visitTIs",
                    "TIs node has a parent which type is != from TBoolRes");

    }

    public void visitTSelect(/*@ non_null @*/TSelect n) throws IOException {
        visitTFunction(n);
    }

    public void visitTStore(/*@ non_null @*/TStore n) throws IOException {
        visitTFunction(n);
    }

    public void visitTTypeOf(/*@ non_null @*/TTypeOf n) throws IOException {
        visitTFunction(n);
    }

    public void visitTForAll(/*@ non_null @*/TForAll n) throws IOException {

        if (n.parent instanceof TBoolRes) {
            TBoolRes nTemp = (TBoolRes) n.parent;
            simplify(nTemp, n);
        } else
            TDisplay.err(this, "visitTForAll",
                    "TIs node has a parent which type is != from TBoolRes");

    }

    public void visitTExist(/*@ non_null @*/TExist n) throws IOException {

        if (n.parent instanceof TBoolRes) {
            TBoolRes nTemp = (TBoolRes) n.parent;
            simplify(nTemp, n);
        } else
            TDisplay.err(this, "visitTExist",
                    "TIs node has a parent which type is != from TBoolRes");

    }

    public void visitTIsAllocated(/*@ non_null @*/TIsAllocated n) throws IOException {
        visitTFunction(n);
    }

    public void visitTEClosedTime(/*@ non_null @*/TEClosedTime n) throws IOException {
        visitTFunction(n);
    }

    public void visitTFClosedTime(/*@ non_null @*/TFClosedTime n) throws IOException {
        visitTFunction(n);
    }

    public void visitTAsElems(/*@ non_null @*/TAsElems n) throws IOException {
        visitTFunction(n);
    }

    public void visitTAsField(/*@ non_null @*/TAsField n) throws IOException {
        visitTFunction(n);
    }

    public void visitTAsLockSet(/*@ non_null @*/TAsLockSet n) throws IOException {
        visitTFunction(n);
    }

    public void visitTArrayLength(/*@ non_null @*/TArrayLength n) throws IOException {
        visitTFunction(n);
    }

    public void visitTArrayFresh(/*@ non_null @*/TArrayFresh n) throws IOException {
        visitTFunction(n);
    }

    public void visitTArrayShapeOne(/*@ non_null @*/TArrayShapeOne n) throws IOException {
        visitTFunction(n);
    }

    public void visitTArrayShapeMore(/*@ non_null @*/TArrayShapeMore n) throws IOException {
        visitTFunction(n);
    }

    public void visitTIsNewArray(/*@ non_null @*/TIsNewArray n) throws IOException {
        visitTFunction(n);
    }

    public void visitTString(/*@ non_null @*/TString n) throws IOException {
    }

    public void visitTBoolean(/*@ non_null @*/TBoolean n) throws IOException {

        if (n.parent instanceof TBoolRes) {
            TBoolRes nTemp = (TBoolRes) n.parent;
            simplify(nTemp, n);
        } else
            TDisplay.err(this, "visitTBoolean",
                    "TIs node has a parent which type is != from TBoolRes");

    }

    public void visitTChar(/*@ non_null @*/TChar n) throws IOException {
    }

    public void visitTInt(/*@ non_null @*/TInt n) throws IOException {
    }

    public void visitTFloat(/*@ non_null @*/TFloat n) throws IOException {
    }

    public void visitTDouble(/*@ non_null @*/TDouble n) throws IOException {
    }

    public void visitTNull(/*@ non_null @*/TNull n) throws IOException {
    }

	public void visitTUnset(TUnset n) throws IOException {
		// TODO Auto-generated method stub
		
	}

	public void visitTMethodCall(TMethodCall call) throws IOException {
		// TODO Auto-generated method stub
		
	}

	public void visitTIntegralSub(TIntegralSub sub) throws IOException {
		// TODO Auto-generated method stub
		
	}

}
