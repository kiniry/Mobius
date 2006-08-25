package escjava.vcGeneration.cvc3;

import java.io.*;

import escjava.vcGeneration.*;

class TCvc3Visitor extends TVisitor {
    static boolean debug; // set to true to help map out nodes.

    Cvc3Prover prover; 

    TCvc3Visitor(Writer out, Cvc3Prover p) {
        super(out);
        prover = p;
    }

    /*
     * General Function (infix functions, most of the built-ins)
     * You give the operator at the first argument and then it outputs
     * (son1 op son2 op ...)
     * 
     */

// add in typeinfo?
// need to determine if we need to "reduce" a leaf to cvc-ntive type like INT
    public void genericOp(/*@ non_null @*/String s, TFunction n) throws IOException {
                                                                                
        lib.appendI("");
                                                                                
        int i = 0;
        for (; i < n.sons.size(); i++) {
            n.getChildAt(i).accept(this);
                                                                                
            /*
             * not the last
             */
            if (i != n.sons.size() - 1) {
                lib.appendN(" ");
                lib.appendN(s);
            }
                                                                                
            lib.appendN(" ");
        }
                                                                                
        lib.reduceI();

    }

    // for INT numeric operators, wrap subexpressions in to_INT
    public void intOp(/*@ non_null @*/String s, TFunction n) throws IOException {
        lib.appendI("");
        TNode child;
        int i = 0;
        for (; i < n.sons.size(); i++) {
            child = n.getChildAt(i);
            if (!(child instanceof TLiteral)) {
              lib.appendN("to_INT(");
              child.accept(this);
              lib.appendN(")");
            }
            else
              child.accept(this);

            if (i != n.sons.size() - 1) {
                lib.appendN(" ");
                lib.appendN(s);
            }
        }
        lib.reduceI();
    }
    // for REAL numeric operators, wrap subexpressions in to_INT
    public void realOp(/*@ non_null @*/String s, TFunction n) throws IOException {
        lib.appendI("");
        TNode child;
        int i = 0;
        for (; i < n.sons.size(); i++) {
            child = n.getChildAt(i);
            if (!(child instanceof TLiteral)) {
              lib.appendN("to_REAL(");
              child.accept(this);
              lib.appendN(")");
            }
            else
              child.accept(this);

            if (i != n.sons.size() - 1) {
                lib.appendN(" ");
                lib.appendN(s);
            }
        }
        lib.reduceI();
    }


    // simplification to remove TRUE/FALSE from boolean formulas
    public void booleanOp(/*@ non_null @*/String s, TFunction n, 
      boolean removing) throws IOException {                                                                                
        TNode child;
        lib.appendI("");
                                                                                
        int i = 0;
        for (; i < n.sons.size(); i++) {
            child = n.getChildAt(i);
            if (child instanceof TBoolean && ((TBoolean)child).value == removing)
              continue;

            child.accept(this);
                                                                                
            /*
             * not the last
             */
            if (i != n.sons.size() - 1) {
                lib.appendN(" ");
                lib.appendN(s);
            }
                                                                                
            lib.appendN(" ");
        }
                                                                                
        lib.reduceI();

    }


    /*
     * Pretty printing function for prefix operators (uninterpreted functions)
     * op (son1, son2, ...)
     */
    public void prefixOp(/*@ non_null @*/String s, TFunction n) throws IOException {
        lib.appendI("");
        lib.appendN(s+"(");

        int i = 0;
        for (; i <= n.sons.size() - 1; i++) {
            n.getChildAt(i).accept(this);
                                                                                
            /*
             * not the last
             */
            if (i != n.sons.size() - 1) {
                lib.appendN(",");
            }
                                                                                
        }
                                                                                
        lib.appendN(")");
        lib.reduceI();

    }


    // for debugging -- adds extra info to output
    public void exploreOp(/*@ non_null @*/String s, TFunction n) throws IOException {
        lib.append(s+"(");

        int i = 0;
        for (; i <= n.sons.size() - 1; i++) {
            lib.appendN("["+s+" #"+i+"] ");
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
        lib.append(s+")");

    }


    /*
     * Pretty print for unsupported operators (comments)
     */
    public void noOp(/*@ non_null @*/String s, TNode n) {
     try {
       lib.appendN("% "+s +"\n");
     } catch (Exception e) {
       System.out.println(e.getMessage());
     }
   }

    // variable or type name    
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
          booleanOp("AND",n,true);
    }

    public void visitTBoolOr(/*@ non_null @*/TBoolOr n) throws IOException {
//        prefixOp("boolOr", n);
          booleanOp("OR",n,false);
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

    // this compares numeric Times
    public void visitTAllocLT(/*@ non_null @*/TAllocLT n) throws IOException {
      genericOp("<", n);
// ?? Times should already be reals
    }

    // this compares numeric Times
    public void visitTAllocLE(/*@ non_null @*/TAllocLE n) throws IOException {
      genericOp("<=", n);
// ?? Times should alread be reals
    }

    public void visitTAnyEQ(/*@ non_null @*/TAnyEQ n) throws IOException {
        // won't work for BOOLEAN
        
        genericOp("=", n);
    }

    public void visitTAnyNE(/*@ non_null @*/TAnyNE n) throws IOException {
        genericOp("/=", n);
    }

    public void visitTIntegralEQ(/*@ non_null @*/TIntegralEQ n) throws IOException {
        intOp("=", n);
    }

    public void visitTIntegralGE(/*@ non_null @*/TIntegralGE n) throws IOException {
        intOp(">=", n);
    }

    public void visitTIntegralGT(/*@ non_null @*/TIntegralGT n) throws IOException {
        intOp(">", n);
    }

    public void visitTIntegralLE(/*@ non_null @*/TIntegralLE n) throws IOException {
        intOp("<=", n);
    }

    public void visitTIntegralLT(/*@ non_null @*/TIntegralLT n) throws IOException {
        intOp("<", n);
    }

    public void visitTIntegralNE(/*@ non_null @*/TIntegralNE n) throws IOException {
        intOp("/=", n);
    }

    public void visitTIntegralAdd(/*@ non_null @*/TIntegralAdd n) throws IOException {
        intOp("+", n);
    }

    public void visitTIntegralDiv(/*@ non_null @*/TIntegralDiv n) throws IOException {
       prefixOp("intdiv_not_supported",n);
		// TODO Auto-generated method stub
// cvc currently does not support non-linear functions
    }

    public void visitTIntegralMod(/*@ non_null @*/TIntegralMod n) throws IOException {
        prefixOp("imod_not_supported",n);
		// TODO Auto-generated method stub
// cvc currently does not support non-linear functions
    }

    public void visitTIntegralMul(/*@ non_null @*/TIntegralMul n) throws IOException {
        intOp("*", n);
    }

    public void visitTFloatEQ(/*@ non_null @*/TFloatEQ n) throws IOException {
        realOp("=", n);
    }

    public void visitTFloatGE(/*@ non_null @*/TFloatGE n) throws IOException {
        realOp(">=", n);
    }

    public void visitTFloatGT(/*@ non_null @*/TFloatGT n) throws IOException {
        realOp(">", n);
    }

    public void visitTFloatLE(/*@ non_null @*/TFloatLE n) throws IOException {
        realOp("<=", n);
    }

    public void visitTFloatLT(/*@ non_null @*/TFloatLT n) throws IOException {
        realOp("<", n);
    }

    public void visitTFloatNE(/*@ non_null @*/TFloatNE n) throws IOException {
        realOp("/=", n);
    }

    public void visitTFloatAdd(/*@ non_null @*/TFloatAdd n) throws IOException {
        realOp("+", n);
    }

    public void visitTFloatDiv(/*@ non_null @*/TFloatDiv n) throws IOException {
        realOp("/", n);
    }

    public void visitTFloatMod(/*@ non_null @*/TFloatMod n) throws IOException {
        prefixOp("fmod_not_supported",n);
		// TODO Auto-generated method stub
// cvc currently does not support non-linear functions
    }

    public void visitTFloatMul(/*@ non_null @*/TFloatMul n) throws IOException {
        realOp("*", n);
    }

    public void visitTLockLE(/*@ non_null @*/TLockLE n) throws IOException {
prefixOp("#lockLE",n);
		// TODO Auto-generated method stub
    }

    public void visitTLockLT(/*@ non_null @*/TLockLT n) throws IOException {
prefixOp("#lockLT",n);
		// TODO Auto-generated method stub
    }

    public void visitTRefEQ(/*@ non_null @*/TRefEQ n) throws IOException {
        // if either child x is Null, change to is_null(y)
        TNode a = n.getChildAt(0);
        TNode b = n.getChildAt(1);
        if (a instanceof TNull) {
          lib.append("is_null(");
          b.accept(this);
          lib.appendN(")");
        } else if (b instanceof TNull) {
          lib.append("is_null(");
          a.accept(this);
          lib.appendN(")");
        } else
          genericOp("=", n);
    }

    public void visitTRefNE(/*@ non_null @*/TRefNE n) throws IOException {
        // if either child x is Null, change to NOT is_null(y)
        TNode a = n.getChildAt(0);
        TNode b = n.getChildAt(1);
        if (a instanceof TNull) {
          lib.append("NOT is_null(");
          b.accept(this);
          lib.appendN(")");
        } else if (b instanceof TNull) {
          lib.append("NOT is_null(");
          a.accept(this);
          lib.appendN(")");
        } else
          genericOp("/=", n);
    }

    public void visitTTypeEQ(/*@ non_null @*/TTypeEQ n) throws IOException {
        // uninterpreted between equality OK.
        genericOp("=",n);
    }

    public void visitTTypeNE(/*@ non_null @*/TTypeNE n) throws IOException {
        genericOp("/=",n);
    }

    public void visitTTypeLE(/*@ non_null @*/TTypeLE n) throws IOException {
        prefixOp("is_subtype",n);
    }

    public void visitTCast(/*@ non_null @*/TCast n) throws IOException {
        prefixOp("cast",n);
    }

    public void visitTIs(/*@ non_null @*/TIs n) throws IOException {
       prefixOp("is",n);
    }

    public void visitTSelect(/*@ non_null @*/TSelect n) throws IOException {
//        lib.appendI("");
        TNode a = n.getChildAt(0);
        TNode b = n.getChildAt(1);
        a.accept(this);
        lib.appendN("[");
        b.accept(this);
        lib.appendN("]");
        
//        lib.reduceI();
		// TODO Auto-generated method stub
    }

    public void visitTStore(/*@ non_null @*/TStore n) throws IOException {
        TNode a = n.getChildAt(0);
        TNode b = n.getChildAt(1);
        TNode c = n.getChildAt(2);
        a.accept(this);
        lib.appendN(" WITH [");
        b.accept(this);
        lib.appendN("] := ");
        c.accept(this);
		// TODO Auto-generated method stub
    }

    public void visitTTypeOf(/*@ non_null @*/TTypeOf n) throws IOException {
      prefixOp("d_type",n);
    }

    public void visitTForAll(/*@ non_null @*/TForAll n) throws IOException {
//prefixOp("#ForAll",n);
      // out format is FORALL (x:t1,y:t2): formula
      // TODO Not sure how quantifier nodes are put together
      // for one variable it appears to be (var,T/F,formula)
      int i=0;
      lib.appendI("FORALL(");
      TNode child;
      String buf = "";
      for (;i<n.sons.size();i++) {
        child = n.getChildAt(i);
        // so it appears that it's names, then possibly junk, then the formula
        // stop when the names stop
        if (!(child instanceof TName)) {
          break;
        }
        // declare the variables
        if (i>0) {
          lib.appendN(",");
        }
        TName var = (TName)child;
        visitTName(var);
        String typename = prover.getTypeInfo(TNode.getVariableInfo(var.name).type);
        lib.appendN(":"+typename);
        VariableInfo vi = TNode.getVariableInfo(var.name);
//        buf = buf + "d_type("+vi.getVariableInfo()+") = "+typename+" AND ";
      }
      lib.appendN("):");
      // now output the formula
      // also set the types for the local vars!
      lib.appendN(buf);
      child = n.getChildAt(n.sons.size() - 1);
      child.accept(this);
      lib.reduceI();
    }

    public void visitTExist(/*@ non_null @*/TExist n) throws IOException {
//prefixOp("#Exist",n);
      // out format is EXISTS (x:t1,y:t2): formula
      // TODO Not sure how quantifier nodes are put together
      int i=0;
      lib.appendI("EXISTS(");
      TNode child;
      String buf = "";
      for (;i<n.sons.size();i++) {
        child = n.getChildAt(i);
        // so it appears that it's names, then possibly junk, then the formula
        // stop when the names stop
        if (!(child instanceof TName)) {
          break;
        }
        // declare the variables
        if (i>0) {
          lib.appendN(",");
        }
        TName var = (TName)child;
        visitTName(var);
        String typename = prover.getTypeInfo(TNode.getVariableInfo(var.name).type);
        lib.appendN(":"+typename);
        VariableInfo vi = TNode.getVariableInfo(var.name);
//        buf = buf + "d_type("+vi.getVariableInfo()+") = "+typename+" AND ";
      }
      lib.appendN("):");
      // now output the formula
      lib.appendN(buf);
      child = n.getChildAt(n.sons.size() - 1);
      child.accept(this);
      lib.reduceI();
    }

    public void visitTIsAllocated(/*@ non_null @*/TIsAllocated n) throws IOException {
      prefixOp("IsAllocated",n);
		// TODO Auto-generated method stub
    }

    public void visitTEClosedTime(/*@ non_null @*/TEClosedTime n) throws IOException {
      prefixOp("EClosedTime",n);
		// TODO Auto-generated method stub
    }

    public void visitTFClosedTime(/*@ non_null @*/TFClosedTime n) throws IOException {
      prefixOp("FClosedTime",n);
		// TODO Auto-generated method stub
    }

    public void visitTAsElems(/*@ non_null @*/TAsElems n) throws IOException {
      // not needed!
    }

    public void visitTAsField(/*@ non_null @*/TAsField n) throws IOException {
      prefixOp("AsField",n);
		// TODO Auto-generated method stub
    }

    public void visitTAsLockSet(/*@ non_null @*/TAsLockSet n) throws IOException {
    // should not be needed!
    }

    public void visitTArrayLength(/*@ non_null @*/TArrayLength n) throws IOException {
      prefixOp("ArrayLength",n);
		// TODO Auto-generated method stub
    }

    public void visitTArrayFresh(/*@ non_null @*/TArrayFresh n) throws IOException {
prefixOp("ArrayFresh",n);
		// TODO Auto-generated method stub
    }

    public void visitTArrayShapeOne(/*@ non_null @*/TArrayShapeOne n) throws IOException {
prefixOp("ArrayShapeOne",n);
		// TODO Auto-generated method stub
    }

    public void visitTArrayShapeMore(/*@ non_null @*/TArrayShapeMore n) throws IOException {
prefixOp("ArrayShapeMore",n);
		// TODO Auto-generated method stub
    }

    public void visitTIsNewArray(/*@ non_null @*/TIsNewArray n) throws IOException {
prefixOp("IsNewArray",n);
		// TODO Auto-generated method stub
    }

    public void visitTString(/*@ non_null @*/TString n) throws IOException {
      lib.appendN("[String]"+n.value);
		// TODO Auto-generated method stub
    }

    // this appears to be a literal
    public void visitTBoolean(/*@ non_null @*/TBoolean n) throws IOException {
        if (n.value)
            lib.appendN("TRUE");
        else
            lib.appendN("FALSE");
    }

    // this appears to be a literal
    public void visitTChar(/*@ non_null @*/TChar n) throws IOException {
        lib.appendN("" + n.value);
    }

    // this appears to be a literal
    public void visitTInt(/*@ non_null @*/TInt n) throws IOException {
        lib.appendN("" + n.value);
    }

    // this appears to be a literal
    public void visitTFloat(/*@ non_null @*/TFloat n) throws IOException {
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

    // this appears to be a literal
    public void visitTDouble(/*@ non_null @*/TDouble n) throws IOException {
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
       // this is not translated directly, rather we assert is_null(x),
       // where x is the (other) sibling node
    }


    public void visitTUnset(/*@non_null*/TUnset n) throws IOException {
prefixOp("Unset",n);
		// TODO Auto-generated method stub
		
    }


    public void visitTMethodCall(/*@non_null*/TMethodCall call) throws IOException {
     prefixOp(prover.getVariableInfo(call.getName()),call);
		// TODO Auto-generated method stub
		
    }


    public void visitTIntegralSub(/*@non_null*/TIntegralSub sub) throws IOException {
      intOp("-",sub);
                // not sure why this is here...
		// TODO Auto-generated method stub
		
    }

	public void visitTSum(TSum s) { 
		// TODO Auto-generated method stub
		
	}

}
