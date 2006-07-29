package escjava.vcGeneration.cvc3;

import java.io.*;

import escjava.vcGeneration.*;

class TCvc3Visitor extends TVisitor {

    TCvc3Visitor(Writer out) {
        super(out);
    }
    
    /*
     * General Function (infix functions, most of the built-ins)
     * You give the operator at the first argument and then it outputs
     * (son1 op son2 op ...)
     * 
     */

    public void genericOp(/*@ non_null @*/String s, TFunction n) throws IOException {
                                                                                
//        lib.appendI("(");
                                                                                
        int i = 0;
        for (; i < n.sons.size(); i++) {
            n.getChildAt(i).accept(this);
                                                                                
            /*
             * not the last
             */
            if (i != n.sons.size() - 1) {
                lib.appendN(" ");
                lib.append(s);
            }
                                                                                
            lib.appendN(" ");
        }
//        lib.appendI(")");
                                                                                
        lib.reduceI();

    }

    /*
     * Pretty printing function for prefix operators (uninterpreted functions)
     * op (son1, son2, ...)
     */
    public void prefixOp(/*@ non_null @*/String s, TFunction n) throws IOException {
        lib.appendI(s);

        int i = 0;
        for (; i <= n.sons.size() - 1; i++) {
            n.getChildAt(i).accept(this);
                                                                                
            /*
             * not the last
             */
            if (i != n.sons.size() - 1) {
                lib.appendN(",");
                lib.append(s);
            }
                                                                                
            lib.appendN(" ");
        }
                                                                                
        lib.reduceI();

    }

    /*
     * Pretty print for unsupported operators (comments)
     */
    public void noOp(/*@ non_null @*/String s, TNode n) {
     try {
       lib.append("% "+s +"\n");
     } catch (Exception e) {
       System.out.println(e.getMessage());
     }
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
//        prefixOp("boolImplies", n);
          genericOp("=>",n);
    }

    public void visitTBoolAnd(/*@ non_null @*/TBoolAnd n) throws IOException {
//        prefixOp("boolAnd",n);
          genericOp("AND",n);
    }

    public void visitTBoolOr(/*@ non_null @*/TBoolOr n) throws IOException {
//        prefixOp("boolOr", n);
          genericOp("OR",n);
    }

    public void visitTBoolNot(/*@ non_null @*/TBoolNot n) throws IOException {
//        prefixOp("boolNot", n);
          prefixOp("NOT",n);
    }

    public void visitTBoolEQ(/*@ non_null @*/TBoolEQ n) throws IOException {
//        prefixOp("boolEq", n);
          genericOp("<=>",n);
    }

    public void visitTBoolNE(/*@ non_null @*/TBoolNE n) throws IOException {
//        prefixOp("boolNE", n);
          genericOp("XOR",n);
    }

    public void visitTAllocLT(/*@ non_null @*/TAllocLT n) throws IOException {
        noOp("AllocLT", n);
// ??
    }

    public void visitTAllocLE(/*@ non_null @*/TAllocLE n) throws IOException {
        noOp("AllocLE", n);
// ??
    }

    public void visitTAnyEQ(/*@ non_null @*/TAnyEQ n) throws IOException {
        // won't work for BOOLEAN
        genericOp("=", n);
    }

    public void visitTAnyNE(/*@ non_null @*/TAnyNE n) throws IOException {
        // won't work for BOOLEAN
        genericOp("/=", n);
    }

    public void visitTIntegralEQ(/*@ non_null @*/TIntegralEQ n) throws IOException {
        genericOp("=", n);
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
        genericOp("/=", n);
    }

    public void visitTIntegralAdd(/*@ non_null @*/TIntegralAdd n) throws IOException {
        genericOp("+", n);
    }

    public void visitTIntegralDiv(/*@ non_null @*/TIntegralDiv n) throws IOException {
noOp("IntegralDiv",n);
		// TODO Auto-generated method stub
// cvc currently does not support non-linear functions
    }

    public void visitTIntegralMod(/*@ non_null @*/TIntegralMod n) throws IOException {
noOp("IntegralMod",n);
		// TODO Auto-generated method stub
// cvc currently does not support non-linear functions
    }

    public void visitTIntegralMul(/*@ non_null @*/TIntegralMul n) throws IOException {
        genericOp("*", n);
    }

    public void visitTFloatEQ(/*@ non_null @*/TFloatEQ n) throws IOException {
        genericOp("=", n);
    }

    public void visitTFloatGE(/*@ non_null @*/TFloatGE n) throws IOException {
        genericOp(">=", n);
    }

    public void visitTFloatGT(/*@ non_null @*/TFloatGT n) throws IOException {
        genericOp(">", n);
    }

    public void visitTFloatLE(/*@ non_null @*/TFloatLE n) throws IOException {
        genericOp("<=", n);
    }

    public void visitTFloatLT(/*@ non_null @*/TFloatLT n) throws IOException {
        genericOp("<", n);
    }

    public void visitTFloatNE(/*@ non_null @*/TFloatNE n) throws IOException {
        genericOp("/=", n);
    }

    public void visitTFloatAdd(/*@ non_null @*/TFloatAdd n) throws IOException {
        genericOp("+", n);
    }

    public void visitTFloatDiv(/*@ non_null @*/TFloatDiv n) throws IOException {
        genericOp("/", n);
    }

    public void visitTFloatMod(/*@ non_null @*/TFloatMod n) throws IOException {
noOp("FloatMod",n);
		// TODO Auto-generated method stub
// cvc currently does not support non-linear functions
    }

    public void visitTFloatMul(/*@ non_null @*/TFloatMul n) throws IOException {
        genericOp("*", n);
    }

    public void visitTLockLE(/*@ non_null @*/TLockLE n) throws IOException {
        prefixOp("lockLE",n);
		// TODO Auto-generated method stub
    }

    public void visitTLockLT(/*@ non_null @*/TLockLT n) throws IOException {
        prefixOp("lockLT",n);
		// TODO Auto-generated method stub
    }

    public void visitTRefEQ(/*@ non_null @*/TRefEQ n) throws IOException {
        genericOp("=", n);
    }

    public void visitTRefNE(/*@ non_null @*/TRefNE n) throws IOException {
        genericOp("/=", n);
    }

    public void visitTTypeEQ(/*@ non_null @*/TTypeEQ n) throws IOException {
        // uninterpreted equality OK.
        genericOp("=",n);
    }

    public void visitTTypeNE(/*@ non_null @*/TTypeNE n) throws IOException {
        genericOp("/=",n);
    }

    public void visitTTypeLE(/*@ non_null @*/TTypeLE n) throws IOException {
        prefixOp("typeLE",n);
    }

    public void visitTCast(/*@ non_null @*/TCast n) throws IOException {
        prefixOp("tCast",n);
    }

    public void visitTIs(/*@ non_null @*/TIs n) throws IOException {
       // break up based on type
       String t = n.getChildAt(0).getType();
       if (t.equals("Boolean")) {
         prefixOp("is_Boolean",n);
       } 
       else if (t.equals("Reference")) {
         prefixOp("is_Reference",n);
       }
       else {
         prefixOp("is_Number",n);
       }
    }

    public void visitTSelect(/*@ non_null @*/TSelect n) throws IOException {
noOp("Select",n);
		// TODO Auto-generated method stub
    }

    public void visitTStore(/*@ non_null @*/TStore n) throws IOException {
noOp("Store",n);
		// TODO Auto-generated method stub
    }

    public void visitTTypeOf(/*@ non_null @*/TTypeOf n) throws IOException {
noOp("TypeOf",n);
		// TODO Auto-generated method stub
    }

    public void visitTForAll(/*@ non_null @*/TForAll n) throws IOException {
noOp("ForAll",n);
      // out format is FORALL (x:t1,y:t2): formula
      // TODO Not sure how quantifier nodes are put together
    }

    public void visitTExist(/*@ non_null @*/TExist n) throws IOException {
noOp("Exist",n);
      // out format is EXISTS (x:t1,y:t2): formula
      // TODO Not sure how quantifier nodes are put together
    }

    public void visitTIsAllocated(/*@ non_null @*/TIsAllocated n) throws IOException {
noOp("IsAllocated",n);
		// TODO Auto-generated method stub
    }

    public void visitTEClosedTime(/*@ non_null @*/TEClosedTime n) throws IOException {
noOp("EClosedTime",n);
		// TODO Auto-generated method stub
    }

    public void visitTFClosedTime(/*@ non_null @*/TFClosedTime n) throws IOException {
noOp("FClosedTime",n);
		// TODO Auto-generated method stub
    }

    public void visitTAsElems(/*@ non_null @*/TAsElems n) throws IOException {
noOp("AsElems",n);
		// TODO Auto-generated method stub
    }

    public void visitTAsField(/*@ non_null @*/TAsField n) throws IOException {
noOp("AsField",n);
		// TODO Auto-generated method stub
    }

    public void visitTAsLockSet(/*@ non_null @*/TAsLockSet n) throws IOException {
noOp("AsLockSet",n);
		// TODO Auto-generated method stub
    }

    public void visitTArrayLength(/*@ non_null @*/TArrayLength n) throws IOException {
noOp("ArrayLength",n);
		// TODO Auto-generated method stub
    }

    public void visitTArrayFresh(/*@ non_null @*/TArrayFresh n) throws IOException {
noOp("ArrayFresh",n);
		// TODO Auto-generated method stub
    }

    public void visitTArrayShapeOne(/*@ non_null @*/TArrayShapeOne n) throws IOException {
noOp("ArrayShapeOne",n);
		// TODO Auto-generated method stub
    }

    public void visitTArrayShapeMore(/*@ non_null @*/TArrayShapeMore n) throws IOException {
noOp("ArrayShapeMore",n);
		// TODO Auto-generated method stub
    }

    public void visitTIsNewArray(/*@ non_null @*/TIsNewArray n) throws IOException {
noOp("IsNewArray",n);
		// TODO Auto-generated method stub
    }

    public void visitTString(/*@ non_null @*/TString n) throws IOException {
noOp("String",n);
		// TODO Auto-generated method stub
    }

    public void visitTBoolean(/*@ non_null @*/TBoolean n) throws IOException {
        if (n.value)
            lib.append(" TRUE ");
        else
            lib.append(" FALSE ");
    }

    public void visitTChar(/*@ non_null @*/TChar n) throws IOException {
noOp("Char",n);
	// CVC does not support string manipulation
    }

    public void visitTInt(/*@ non_null @*/TInt n) throws IOException {
        lib.appendN(" " + n.value);
    }

    public void visitTFloat(/*@ non_null @*/TFloat n) throws IOException {
// is this a variable or a literal?
        // cvc only supports rationals!
        // so we need to figure out what the denominator should be...
        long d = 1;
        float f = n.value;
	while (f*d > (float)Math.floor(f*d)) {
          d = d*10;
        }
        long num = (long)f*d;
        if (d > 1) {
          lib.appendN(""+num+"/"+d);
        } else {
          lib.appendN(""+num);
        }
    }

    public void visitTDouble(/*@ non_null @*/TDouble n) throws IOException {
// is this a variable or a literal?
    // as visitTFloat, above
        long d = 1;
        double f = n.value;
	while (f*d > Math.floor(f*d)) {
          d = d*10;
        }
        long num = (long)f*d;
        if (d > 1) {
          lib.appendN(""+num+"/"+d);
        } else {
          lib.appendN(""+num);
        }
    }

    public void visitTNull(/*@ non_null @*/TNull n) throws IOException {
       lib.append("Null");
    }


	public void visitTUnset(/*@non_null*/TUnset n) throws IOException {
noOp("Unset",n);
		// TODO Auto-generated method stub
		
	}


	public void visitTMethodCall(/*@non_null*/TMethodCall call) throws IOException {
noOp("MethodCall",call);
		// TODO Auto-generated method stub
		
	}


	public void visitTIntegralSub(/*@non_null*/TIntegralSub sub) throws IOException {
noOp("IntegralSub",sub);
		// TODO Auto-generated method stub
		
	}

	public void visitTSum(TSum s) { 
noOp("Sum",s);
		// TODO Auto-generated method stub
		
	}

}
