package escjava.vcGeneration;

import java.io.*;

abstract public class TVisitor {

    /**
     * Default pretty printer that may be used by implementing vistor patterns.
     */
    protected PrettyPrinter lib = null;

    protected/*@ non_null @*/Writer out = null;

    protected/*@ non_null @*/StringBuffer indentation = null;

    public TVisitor(Writer out) {
        this(out, "  ", "(", ")", "\n");
    }

    public TVisitor(Writer out, String tab, String lbr, String rbr, String nl) {
        this.out = out;
        lib = new PrettyPrinter(out, tab, lbr, rbr, nl);
        indentation = new StringBuffer();
    }

    //non automatic division
    abstract public void visitTName(/*@ non_null @*/TName n) throws IOException;
    
    abstract public void visitTRoot(/*@ non_null @*/TRoot n) throws IOException;

    // class created using the perl script
    abstract public void visitTBoolImplies(/*@ non_null @*/TBoolImplies n) throws IOException;

    abstract public void visitTBoolAnd(/*@ non_null @*/TBoolAnd n) throws IOException;

    abstract public void visitTBoolOr(/*@ non_null @*/TBoolOr n) throws IOException;

    abstract public void visitTBoolNot(/*@ non_null @*/TBoolNot n) throws IOException;

    abstract public void visitTBoolEQ(/*@ non_null @*/TBoolEQ n) throws IOException;

    abstract public void visitTBoolNE(/*@ non_null @*/TBoolNE n) throws IOException;

    abstract public void visitTAllocLT(/*@ non_null @*/TAllocLT n) throws IOException;

    abstract public void visitTAllocLE(/*@ non_null @*/TAllocLE n) throws IOException;

    abstract public void visitTAnyEQ(/*@ non_null @*/TAnyEQ n) throws IOException;

    abstract public void visitTAnyNE(/*@ non_null @*/TAnyNE n) throws IOException;

    abstract public void visitTIntegralEQ(/*@ non_null @*/TIntegralEQ n) throws IOException;

    abstract public void visitTIntegralGE(/*@ non_null @*/TIntegralGE n) throws IOException;

    abstract public void visitTIntegralGT(/*@ non_null @*/TIntegralGT n) throws IOException;

    abstract public void visitTIntegralLE(/*@ non_null @*/TIntegralLE n) throws IOException;

    abstract public void visitTIntegralLT(/*@ non_null @*/TIntegralLT n) throws IOException;

    abstract public void visitTIntegralNE(/*@ non_null @*/TIntegralNE n) throws IOException;

    abstract public void visitTIntegralAdd(/*@ non_null @*/TIntegralAdd n) throws IOException;

    abstract public void visitTIntegralDiv(/*@ non_null @*/TIntegralDiv n) throws IOException;

    abstract public void visitTIntegralMod(/*@ non_null @*/TIntegralMod n) throws IOException;

    abstract public void visitTIntegralMul(/*@ non_null @*/TIntegralMul n) throws IOException;

    abstract public void visitTFloatEQ(/*@ non_null @*/TFloatEQ n) throws IOException;

    abstract public void visitTFloatGE(/*@ non_null @*/TFloatGE n) throws IOException;

    abstract public void visitTFloatGT(/*@ non_null @*/TFloatGT n) throws IOException;

    abstract public void visitTFloatLE(/*@ non_null @*/TFloatLE n) throws IOException;

    abstract public void visitTFloatLT(/*@ non_null @*/TFloatLT n) throws IOException;

    abstract public void visitTFloatNE(/*@ non_null @*/TFloatNE n) throws IOException;

    abstract public void visitTFloatAdd(/*@ non_null @*/TFloatAdd n) throws IOException;

    abstract public void visitTFloatDiv(/*@ non_null @*/TFloatDiv n) throws IOException;

    abstract public void visitTFloatMod(/*@ non_null @*/TFloatMod n) throws IOException;

    abstract public void visitTFloatMul(/*@ non_null @*/TFloatMul n) throws IOException;

    abstract public void visitTLockLE(/*@ non_null @*/TLockLE n) throws IOException;

    abstract public void visitTLockLT(/*@ non_null @*/TLockLT n) throws IOException;

    abstract public void visitTRefEQ(/*@ non_null @*/TRefEQ n) throws IOException;

    abstract public void visitTRefNE(/*@ non_null @*/TRefNE n) throws IOException;

    abstract public void visitTTypeEQ(/*@ non_null @*/TTypeEQ n) throws IOException;

    abstract public void visitTTypeNE(/*@ non_null @*/TTypeNE n) throws IOException;

    abstract public void visitTTypeLE(/*@ non_null @*/TTypeLE n) throws IOException;

    abstract public void visitTCast(/*@ non_null @*/TCast n) throws IOException;

    abstract public void visitTIs(/*@ non_null @*/TIs n) throws IOException;

    abstract public void visitTSelect(/*@ non_null @*/TSelect n) throws IOException;

    abstract public void visitTStore(/*@ non_null @*/TStore n) throws IOException;

    abstract public void visitTTypeOf(/*@ non_null @*/TTypeOf n) throws IOException;

    abstract public void visitTForAll(/*@ non_null @*/TForAll n) throws IOException;

    abstract public void visitTExist(/*@ non_null @*/TExist n) throws IOException;

    abstract public void visitTIsAllocated(/*@ non_null @*/TIsAllocated n) throws IOException;

    abstract public void visitTEClosedTime(/*@ non_null @*/TEClosedTime n) throws IOException;

    abstract public void visitTFClosedTime(/*@ non_null @*/TFClosedTime n) throws IOException;

    abstract public void visitTAsElems(/*@ non_null @*/TAsElems n) throws IOException;

    abstract public void visitTAsField(/*@ non_null @*/TAsField n) throws IOException;

    abstract public void visitTAsLockSet(/*@ non_null @*/TAsLockSet n) throws IOException;

    abstract public void visitTArrayLength(/*@ non_null @*/TArrayLength n) throws IOException;

    abstract public void visitTArrayFresh(/*@ non_null @*/TArrayFresh n) throws IOException;

    abstract public void visitTArrayShapeOne(/*@ non_null @*/TArrayShapeOne n) throws IOException;

    abstract public void visitTArrayShapeMore(/*@ non_null @*/TArrayShapeMore n) throws IOException;

    abstract public void visitTIsNewArray(/*@ non_null @*/TIsNewArray n) throws IOException;

    abstract public void visitTString(/*@ non_null @*/TString n) throws IOException;

    abstract public void visitTBoolean(/*@ non_null @*/TBoolean n) throws IOException;

    abstract public void visitTChar(/*@ non_null @*/TChar n) throws IOException;

    abstract public void visitTInt(/*@ non_null @*/TInt n) throws IOException;

    abstract public void visitTFloat(/*@ non_null @*/TFloat n) throws IOException;

    abstract public void visitTDouble(/*@ non_null @*/TDouble n) throws IOException;

    abstract public void visitTNull(/*@ non_null @*/TNull n) throws IOException;

    // added by me
    abstract public void visitTUnset(/*@ non_null @*/ TUnset n) throws IOException;

    abstract public void visitTMethodCall(/*@ non_null @*/ TMethodCall call) throws IOException;

    abstract public void visitTIntegralSub(/*@ non_null @*/ TIntegralSub sub) throws IOException;
    
    abstract public void visitTSum (/*@ non_null @*/  TSum s) throws IOException;
}
