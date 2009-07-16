
/** 
   \defgroup mapi_ex Managed (.NET) API examples
*/
/*@{*/

using Microsoft.Z3;
using System;
///
/// \brief Class encapsulating Z3 tests.
///

class TestManaged {
    ///
    /// \brief local reference to the Z3 Api.
    ///
    Context z3;

    
    /*! \brief Create a logical context with model construction enabled.
    */
    public void mk_context() {
	if (this.z3 != null) {
	    this.z3.Dispose();
	}
	Config p = new Config();
        p.SetParamValue("MODEL","true");
        this.z3 = new Context(p);
	p.Dispose();
    }


    /*! \brief Create an integer type.
    */
    public Sort mk_int_type() {
        return z3.MkIntSort();
    }

    /*! \brief Create a bit-vector type.
    */
    public Sort mk_bv_type(uint num_bytes) {
        return z3.MkBvSort(num_bytes);
    }

    /*! \brief Create a variable using the given name and type.
    */
    public Term mk_var(string name, Sort ty) {
        return z3.MkConst(name,ty);
    }

    /*! \brief Create a boolean variable using the given name.
    */
    public Term mk_bool_var(string name) {
        return mk_var(name, z3.MkBoolSort());
    }

    /*! \brief Create an integer variable using the given name.
    */
    public Term mk_int_var(string name) {
        return mk_var(name, mk_int_type());
    }

    /*! \brief Create a bit-vector variable using the given name.
    */
    public Term mk_bv_var(string name, uint num_bytes) {
        return mk_var(name, mk_bv_type(num_bytes));
    }

    /*! \brief Create a Z3 integer node using an int. 
    */
    Term mk_int(int v) 
    {
        return z3.MkNumeral(v,mk_int_type());
    }

    /*! \brief Create a Z3 32-bit integer.
    */
    Term mk_bv32(UInt32 b)
    {
        return z3.MkNumeral(String.Format("{0}",b), mk_bv_type(32));
    }



    /*! \brief Create the unary function application: <tt>(f x)</tt>.
    */
    Term mk_unary_app(FuncDecl f, Term x) 
    {
        return z3.MkApp(f, x);
    }

    /*! \brief Create the binary function application: <tt>(f x y)</tt>.
    */
    Term mk_binary_app(FuncDecl f, Term x, Term y) 
    {
        return z3.MkApp(f, x, y);
    }

    void exitf(string message) {
	Console.WriteLine("{0}", message);
	throw new Exception("Fatal Error");
    }

    /*!
       \brief Check whether the logical context is satisfiable, 
       and compare the result with the expected result.
       If the context is satisfiable, then display the model.
    */
    public void check(LBool expected_result, out Model model)
    {
        LBool result = z3.CheckAndGetModel(out model);
        switch (result) {
        case LBool.False:
            Console.WriteLine("unsat");
            break;
        case LBool.Undef:
            Console.WriteLine("unknown");            
            break;
        case LBool.True:
            Console.WriteLine("sat");
	    model.Display(Console.Out);
            break;
        }
        if (result != expected_result) {
            Console.WriteLine("BUG: unexpected result");
        }
    }

    /**
       \brief Similar to #check, but uses #display_model instead of Z3's native display method.
    */
    public void check2(LBool expected_result)
    {
	Model model = null;
        LBool result = z3.CheckAndGetModel(out model);
        switch (result) {
        case LBool.False:
            Console.WriteLine("unsat");
            break;
        case LBool.Undef:
            Console.WriteLine("unknown");            
            break;
        case LBool.True:
            Console.WriteLine("sat");
	    display_model(Console.Out, model);
            break;
        }
        if (result != expected_result) {
            Console.WriteLine("BUG: unexpected result");
        }
	if (model != null) {
	    model.Dispose();
	}
    }



    /*!
       \brief Prove that the constraints already asserted into the logical
       context implies the given formula.  The result of the proof is
       displayed.
   
       Z3 is a satisfiability checker. So, one can prove \c f by showing
       that <tt>(not f)</tt> is unsatisfiable.

    */
    public void prove(Term f) 
    {        
        /* save the current state of the context */
        z3.Push();
        
        Term not_f = z3.MkNot(f);
        z3.AssertCnstr(not_f);
        
	Model model = null;
        switch (z3.CheckAndGetModel(out model)) {
        case LBool.False:
            /* proved */
            Console.WriteLine("valid");
            break;
        case LBool.Undef:
            /* Z3 failed to prove/disprove f. */
            Console.WriteLine("unknown");
            break;
        case LBool.True:
            /* disproved */
            Console.WriteLine("invalid");
	    model.Display(Console.Out);
            break;
        }
	if (model != null) {
	    model.Dispose();
	}
                
        /* restore context */
        z3.Pop(1);
    }

    /*!
       \brief Prove that the constraints already asserted into the logical
       context implies the given formula.  The result of the proof is
       displayed.
   
       Z3 is a satisfiability checker. So, one can prove \c f by showing
       that <tt>(not f)</tt> is unsatisfiable.

    */
    public void prove2(Term f, bool is_valid) 
    {        
        /* save the current state of the context */
        z3.Push();
        
        Term not_f = z3.MkNot(f);
        z3.AssertCnstr(not_f);
        
	Model model = null;
	LBool result = z3.CheckAndGetModel(out model);
        switch (result) {
        case LBool.False:
            /* proved */
            Console.WriteLine("valid");
	    if (!is_valid) {
		exitf("Did not expecte valid");
	    }
            break;
        case LBool.Undef:
            /* Z3 failed to prove/disprove f. */
            Console.WriteLine("unknown");
	    if (is_valid) {
		exitf("Expected valid");
	    }
            break;
        case LBool.True:
            /* disproved */
            Console.WriteLine("invalid");
	    model.Display(Console.Out);
	    if (is_valid) {
		exitf("Expected valid");
	    }
            break;
        }
	if (model != null) {
	    model.Dispose();
	}
                
        /* restore context */
        z3.Pop(1);

    }

    /**
       \brief Custom model pretty printer.
    */	
    void display_model(System.IO.TextWriter w, Model model)
    {
        w.WriteLine("Custom model display:");
        FuncDecl[] consts = model.GetModelConstants();        
        for (int i = 0; i < consts.Length; i++) {
            w.WriteLine("{0} |-> {1}", z3.ToString(consts[i]), z3.ToString(model.Eval(z3.MkConst(consts[i]))));
        }
	w.WriteLine("num consts: {0}", consts.Length);
	System.Collections.Generic.Dictionary<FuncDecl, FunctionGraph> graphs = model.GetFunctionGraphs();
	foreach (System.Collections.Generic.KeyValuePair<FuncDecl, FunctionGraph> declg in graphs) {
	    FunctionGraph g = declg.Value;
            w.WriteLine("function {0}:", z3.ToString(g.Declaration));
            for (int j = 0; j < g.Entries.Length; ++j) {
                for (int k = 0; k < g.Entries[j].Arguments.Length; ++k) {
                    w.Write("  {0} ", z3.ToString(g.Entries[j].Arguments[k]));
                }
                w.WriteLine(" |-> {0}", z3.ToString(g.Entries[j].Result));                
            }
            w.WriteLine("  else |-> {0}",z3.ToString(g.Else));
        }	
    }

    /*!
       \brief Assert the axiom: function f is injective in the i-th argument.
       
       The following axiom is asserted into the logical context:
       \code
       forall (x_0, ..., x_n) finv(f(x_0, ..., x_i, ..., x_{n-1})) = x_i
       \endcode
       
       Where, \c finv is a fresh function declaration.
    */
    public void assert_inj_axiom(FuncDecl f, int i)
    {        
	Sort[] domain = z3.GetDomain(f);
        uint sz = (uint)domain.Length;
        
        if (i >= sz) {
            Console.WriteLine("failed to create inj axiom");
            return;
        }
        
        /* declare the i-th inverse of f: finv */
        Sort finv_domain = z3.GetRange(f);
        Sort finv_range  = domain[i];
        FuncDecl finv       = z3.MkFuncDecl("f_fresh", finv_domain, finv_range);
        
        /* allocate temporary arrays */
        Term[] xs = new Term[sz];
        Symbol[] names = new Symbol[sz];
        Sort[] types = new Sort[sz];
        
        /* fill types, names and xs */

        for (uint j = 0; j < sz; j++) {
            types[j] = domain[j];
            names[j] = z3.MkSymbol(String.Format("x_{0}",j));
            xs[j]    = z3.MkBound(j, types[j]);
        }
        Term x_i = xs[i];
        
        /* create f(x_0, ..., x_i, ..., x_{n-1}) */ 
        Term fxs         = z3.MkApp(f, xs);
        
        /* create f_inv(f(x_0, ..., x_i, ..., x_{n-1})) */
        Term finv_fxs    = mk_unary_app(finv, fxs);
        
        /* create finv(f(x_0, ..., x_i, ..., x_{n-1})) = x_i */
        Term eq          = z3.MkEq(finv_fxs, x_i);
        
        /* use f(x_0, ..., x_i, ..., x_{n-1}) as the pattern for the quantifier */
        Pattern p  = z3.MkPattern(new Term[]{ fxs });
        Console.WriteLine("pattern {0}", z3.ToString(p));
        
        /* create & assert quantifier */
        Term q = z3.MkForall(
            0, /* using default weight */
            new Pattern[]{p}, /* patterns */
            types, /* types of quantified variables */
            names, /* names of quantified variables */
            eq);

        Console.WriteLine("assert axiom {0}", z3.ToString(q));
        z3.AssertCnstr(q);
        
    }

    /*!
       \brief Assert the axiom: function f is injective in the i-th argument.
       
       The following axiom is asserted into the logical context:
       \code
       forall (x_0, ..., x_n) finv(f(x_0, ..., x_i, ..., x_{n-1})) = x_i
       \endcode
       
       Where, \c finv is a fresh function declaration.
    */
    public void assert_inj_axiom_abs(FuncDecl f, int i)
    {        
	Sort[] domain = z3.GetDomain(f);
        uint sz = (uint)domain.Length;
        
        if (i >= sz) {
            Console.WriteLine("failed to create inj axiom");
            return;
        }
        
        /* declare the i-th inverse of f: finv */
        Sort finv_domain = z3.GetRange(f);
        Sort finv_range  = domain[i];
        FuncDecl finv       = z3.MkFuncDecl("f_fresh", finv_domain, finv_range);
        
        /* allocate temporary arrays */
        Term[] xs = new Term[sz];
        
        /* fill types, names and xs */

        for (uint j = 0; j < sz; j++) {
            xs[j]    = z3.MkConst(String.Format("x_{0}",j), domain[j]);
        }
        Term x_i = xs[i];
        
        /* create f(x_0, ..., x_i, ..., x_{n-1}) */ 
        Term fxs         = z3.MkApp(f, xs);
        
        /* create f_inv(f(x_0, ..., x_i, ..., x_{n-1})) */
        Term finv_fxs    = mk_unary_app(finv, fxs);
        
        /* create finv(f(x_0, ..., x_i, ..., x_{n-1})) = x_i */
        Term eq          = z3.MkEq(finv_fxs, x_i);
        
        /* use f(x_0, ..., x_i, ..., x_{n-1}) as the pattern for the quantifier */
        Pattern p  = z3.MkPattern(new Term[]{ fxs });
        Console.WriteLine("pattern {0}", z3.ToString(p));
        
        /* create & assert quantifier */
        Term q = z3.MkForall(
            0, /* using default weight */
            xs,    /* the list of bound variables */
            new Pattern[]{p}, /* patterns */
            eq);

        Console.WriteLine("assert axiom {0}", z3.ToString(q));
        z3.AssertCnstr(q);
        
    }

    /**
       \brief Assert the axiom: function f is commutative. 
   
       This example uses the SMT-LIB parser to simplify the axiom construction.
    */
    private void assert_comm_axiom(FuncDecl f)
    {
	Sort t = z3.GetRange(f);
	Sort[] dom = z3.GetDomain(f);

	if (dom.Length != 2 ||
	    !t.Equals(dom[0]) ||
	    !t.Equals(dom[1])) {
	    Console.WriteLine("{0} {1} {2} {3}", dom.Length, dom[0],dom[1],t);
	    exitf("function must be binary, and argument types must be equal to return type");
	} 
	string bench = string.Format("(benchmark comm :formula (forall (x {0}) (y {1}) (= ({2} x y) ({3} y x))))", 
				     t.GetName(), t.GetName(), f.GetDeclName(), f.GetDeclName());
	Term[] formulas, assumptions;
	FuncDecl[] decls;
	z3.ParseSmtlibString(bench, new Sort[]{t}, new FuncDecl[]{f}, out assumptions, out formulas, out decls);
	Term q = formulas[0];
	Console.WriteLine("assert axiom:\n{0}", q);
	z3.AssertCnstr(q);
    }



    /* @name Examples
    */

    /*!
       \brief "Hello world" example: create a Z3 logical context, and delete it.
    */
    public void simple_example() 
    {        
        Console.WriteLine("simple_example");
        Config p = new Config();
        Context z3 = new Context(p);
               
        /* do something with the context */

	/* be kind to dispose manually and not wait for the GC. */
	z3.Dispose();
	p.Dispose();
    }

    /*!
       \brief Find a model for <tt>x xor y</tt>.
    */
    public void find_model_example1() 
    {        
        Console.WriteLine("find_model_example1");
        
        mk_context();
                
        Term x       = mk_bool_var("x");
        Term y       = mk_bool_var("y");
        Term x_xor_y = z3.MkXor(x,y);
        
        z3.AssertCnstr(x_xor_y);
        
        Console.WriteLine("model for: x xor y");
	Model model = null;
        check(LBool.True, out model);
        Console.WriteLine("x = {0}, y = {1}", 
                          z3.ToString(model.Eval(x)),
	                  z3.ToString(model.Eval(y)));
	model.Dispose();
    }

    /*!
       \brief Find a model for <tt>x < y + 1, x > 2</tt>.
       Then, assert <tt>not(x = y)</tt>, and find another model.
    */
    public void find_model_example2() 
    {
        Console.WriteLine("find_model_example2");

        mk_context();
        Term x          = mk_int_var("x");
        Term y          = mk_int_var("y");
        Term one        = mk_int(1);
        Term two        = mk_int(2);

        Term y_plus_one = z3.MkAdd(y, one);
        
        Term c1         = z3.MkLt(x, y_plus_one);
        Term c2         = z3.MkGt(x, two);
    
        z3.AssertCnstr(c1);
        z3.AssertCnstr(c2);

        Console.WriteLine("model for: x < y + 1, x > 2");
	Model model = null;
        check(LBool.True, out model);
        Console.WriteLine("x = {0}, y = {1}", 
                          z3.ToString(model.Eval(x)),
                          z3.ToString(model.Eval(y)));
	model.Dispose();
	model = null;

        /* assert not(x = y) */
        Term x_eq_y     = z3.MkEq(x, y);
        Term c3         = z3.MkNot(x_eq_y);
        z3.AssertCnstr(c3);
        
        Console.WriteLine("model for: x < y + 1, x > 2, not(x = y)");
        check(LBool.True, out model);
        Console.WriteLine("x = {0}, y = {1}", 
                          z3.ToString(model.Eval(x)),
                          z3.ToString(model.Eval(y)));
	model.Dispose();
    }

    /*!
       \brief Prove <tt>x = y implies g(x) = g(y)</tt>, and
       disprove <tt>x = y implies g(g(x)) = g(y)</tt>.
       
       This function demonstrates how to create uninterpreted types and
       functions.
    */
    public void prove_example1() 
    {
        Console.WriteLine("prove_example1");
        
        mk_context();
        
        /* create uninterpreted type. */
        Sort U          = z3.MkSort("U");
        
        /* declare function g */
        FuncDecl g = z3.MkFuncDecl("g", U, U);
        
        /* create x and y */
        Term x      = z3.MkConst("x", U);
        Term y      = z3.MkConst("y", U);
        /* create g(x), g(y) */
        Term gx          = mk_unary_app(g, x);
        Term gy          = mk_unary_app(g, y);
        
        /* assert x = y */
        Term eq          = z3.MkEq(x, y);
        z3.AssertCnstr(eq);
        
        /* prove g(x) = g(y) */
        Term f           = z3.MkEq(gx, gy);
        Console.WriteLine("prove: x = y implies g(x) = g(y)");
        prove(f);
        
        /* create g(g(x)) */
        Term ggx         = mk_unary_app(g, gx);
        
        /* disprove g(g(x)) = g(y) */
        f           = z3.MkEq(ggx, gy);
        Console.WriteLine("disprove: x = y implies g(g(x)) = g(y)");
        prove(f);


        /* Print the model using the custom model printer */
        z3.AssertCnstr(z3.MkNot(f));
        check2(LBool.True);
    }


    /*! \brief Prove <tt>not(g(g(x) - g(y)) = g(z)), x + z <= y <= x implies z < 0 </tt>.
        Then, show that <tt>z < -1</tt> is not implied.
       
        This example demonstrates how to combine uninterpreted functions and arithmetic.
    */
    public void prove_example2() 
    {        
        Console.WriteLine("prove_example2");
        
        mk_context();
                
        /* declare function g */
        Sort int_type = mk_int_type();

        FuncDecl g = z3.MkFuncDecl("g", int_type, int_type);
                
        /* create x, y, and z */
        Term x           = mk_int_var("x");
        Term y           = mk_int_var("y");
        Term z           = mk_int_var("z");
        
        /* create gx, gy, gz */
        Term gx          = mk_unary_app(g, x);
        Term gy          = mk_unary_app(g, y);
        Term gz          = mk_unary_app(g, z);
        
        /* create zero */
        Term zero        = mk_int(0);
        
        /* assert not(g(g(x) - g(y)) = g(z)) */
        Term gx_gy       = z3.MkSub(gx, gy);
        Term ggx_gy      = mk_unary_app(g, gx_gy);
        Term eq          = z3.MkEq(ggx_gy, gz);
        Term c1          = z3.MkNot(eq);
        z3.AssertCnstr(c1);
        
        /* assert x + z <= y */
        Term x_plus_z    = z3.MkAdd(x,y);
        Term c2          = z3.MkLe(x_plus_z, y);
        z3.AssertCnstr(c2);
        
        /* assert y <= x */
        Term c3          = z3.MkLe(y, x);
        z3.AssertCnstr(c3);
        
        /* prove z < 0 */
        Term f           = z3.MkLt(z, zero);
        Console.WriteLine("prove: not(g(g(x) - g(y)) = g(z)), x + z <= y <= x implies z < 0");
        prove(f);
        
        /* disprove z < -1 */
        Term minus_one   = mk_int(-1);
        f           = z3.MkLt(z, minus_one);
        Console.WriteLine("disprove: not(g(g(x) - g(y)) = g(z)), x + z <= y <= x implies z < -1");
        prove(f);
    }

    /*! \brief Show how push & pop can be used to create "backtracking"
         points.
       
         This example also demonstrates how big numbers can be created in Z3.
    */
    public void push_pop_example1() 
    {
        Console.WriteLine("push_pop_example1");

        mk_context();

        /* create a big number */
        Sort int_type = mk_int_type();
        Term big_number = z3.MkNumeral("1000000000000000000000000000000000000000000000000000000", int_type);
    
        /* create number 3 */
        Term three      = z3.MkNumeral("3", int_type);

        /* create x */
        Term x          = z3.MkConst("x", int_type);


        /* assert x >= "big number" */
        Term c1         = z3.MkGe(x, big_number);
        Console.WriteLine("assert: x >= 'big number'");
        z3.AssertCnstr(c1);

        /* create a backtracking point */
        Console.WriteLine("push");
        z3.Push();

        /* assert x <= 3 */
        Term c2         = z3.MkLe(x, three);
        Console.WriteLine("assert: x <= 3");
        z3.AssertCnstr(c2);

        /* context is inconsistent at this point */
	Model model = null;
        check(LBool.False, out model);

        /* backtrack: the constraint x <= 3 will be removed, since it was
           asserted after the last z3.Push. */
        Console.WriteLine("pop");
        z3.Pop(1);

        /* the context is consistent again. */
        check2(LBool.True);

        /* new constraints can be asserted... */
    
        /* create y */
        Term y          = z3.MkConst("y", int_type);
    
        /* assert y > x */
        Term c3         = z3.MkGt(y, x);
        Console.WriteLine("assert: y > x");
        z3.AssertCnstr(c3);

        /* the context is still consistent. */
        check(LBool.True, out model);
	model.Dispose();
    }


    /*! \brief Prove that <tt>f(x, y) = f(w, v) implies y = v</tt> when 
        \c f is injective in the second argument.
       
        \sa assert_inj_axiom.
    */
    public void quantifier_example1() 
    {        
        Console.WriteLine("quantifier_example1");

        Config p = new Config();
        // p.SetParamValue("MODEL", "true");
        /* If quantified formulas are asserted in a logical context, then
           the model produced by Z3 should be viewed as a potential model.
           
        */
	if (this.z3 != null) {
	    this.z3.Dispose();
	}
        this.z3 = new Context(p);
        p.Dispose();

        /* declare function f */
        Sort int_type = mk_int_type();
        FuncDecl f       = z3.MkFuncDecl("f", new Sort[]{ int_type, int_type }, int_type);
        
        /* assert that f is injective in the second argument. */
        assert_inj_axiom(f, 1);
        
        /* create x, y, v, w, fxy, fwv */
        Term x           = mk_int_var("x");
        Term y           = mk_int_var("y");
        Term v           = mk_int_var("v");
        Term w           = mk_int_var("w");
        Term fxy         = mk_binary_app(f, x, y);
        Term fwv         = mk_binary_app(f, w, v);
        
        /* assert f(x, y) = f(w, v) */
        Term p1          = z3.MkEq(fxy, fwv);
        z3.AssertCnstr(p1);
        
        /* prove f(x, y) = f(w, v) implies y = v */
        Term p2          = z3.MkEq(y, v);
        Console.WriteLine("prove: f(x, y) = f(w, v) implies y = v");
        prove(p2);
        
        /* disprove f(x, y) = f(w, v) implies x = w */
        Term p3          = z3.MkEq(x, w);
        Console.WriteLine("disprove: f(x, y) = f(w, v) implies x = w");
        prove(p3);
    }

    /*! \brief Prove that <tt>f(x, y) = f(w, v) implies y = v</tt> when 
        \c f is injective in the second argument.
       
        \sa assert_inj_axiom.
    */
    public void quantifier_example1_abs() 
    {        
        Console.WriteLine("quantifier_example1_abs");

        Config p = new Config();
        // p.SetParamValue("MODEL", "true");
        /* If quantified formulas are asserted in a logical context, then
           the model produced by Z3 should be viewed as a potential model.
           
        */
	if (this.z3 != null) {
	    this.z3.Dispose();
	}
        this.z3 = new Context(p);
        p.Dispose();

        /* declare function f */
        Sort int_type = mk_int_type();
        FuncDecl f       = z3.MkFuncDecl("f", new Sort[]{ int_type, int_type }, int_type);
        
        /* assert that f is injective in the second argument. */
        assert_inj_axiom_abs(f, 1);
        
        /* create x, y, v, w, fxy, fwv */
        Term x           = mk_int_var("x");
        Term y           = mk_int_var("y");
        Term v           = mk_int_var("v");
        Term w           = mk_int_var("w");
        Term fxy         = mk_binary_app(f, x, y);
        Term fwv         = mk_binary_app(f, w, v);
        
        /* assert f(x, y) = f(w, v) */
        Term p1          = z3.MkEq(fxy, fwv);
        z3.AssertCnstr(p1);
        
        /* prove f(x, y) = f(w, v) implies y = v */
        Term p2          = z3.MkEq(y, v);
        Console.WriteLine("prove: f(x, y) = f(w, v) implies y = v");
        prove(p2);
        
        /* disprove f(x, y) = f(w, v) implies x = w */
        Term p3          = z3.MkEq(x, w);
        Console.WriteLine("disprove: f(x, y) = f(w, v) implies x = w");
        prove(p3);
    }


    /*! \brief Prove <tt>store(a1, i1, v1) = store(a2, i2, v2) implies (i1 = i3 or i2 = i3 or select(a1, i3) = select(a2, i3))</tt>.
       
       This example demonstrates how to use the array theory.
    */
    public void array_example1() 
    {

        Console.WriteLine("array_example1");

        mk_context();

        Sort int_type    = mk_int_type();
        Sort array_type  = z3.MkArraySort(int_type, int_type);

        Term a1          = mk_var("a1", array_type);
        Term a2          = mk_var("a2", array_type);
        Term i1          = mk_var("i1", int_type);
        Term i2          = mk_var("i2", int_type);
        Term i3          = mk_var("i3", int_type);
        Term v1          = mk_var("v1", int_type);
        Term v2          = mk_var("v2", int_type);
    
        Term st1         = z3.MkArrayStore(a1, i1, v1);
        Term st2         = z3.MkArrayStore(a2, i2, v2);
    
        Term sel1        = z3.MkArraySelect(a1, i3);
        Term sel2        = z3.MkArraySelect(a2, i3);

        /* create antecedent */
        Term antecedent  = z3.MkEq(st1, st2);

        /* create consequent: i1 = i3 or  i2 = i3 or select(a1, i3) = select(a2, i3) */
        Term consequent  = z3.MkOr(new Term[] { z3.MkEq(i1,i3), z3.MkEq(i2,i3), z3.MkEq(sel1,sel2) });
        
        /* prove store(a1, i1, v1) = store(a2, i2, v2) implies (i1 = i3 or i2 = i3 or select(a1, i3) = select(a2, i3)) */
        Term thm         = z3.MkImplies(antecedent, consequent);
        Console.WriteLine("prove: store(a1, i1, v1) = store(a2, i2, v2) implies (i1 = i3 or i2 = i3 or select(a1, i3) = select(a2, i3))");
        Console.WriteLine("{0}", z3.ToString(thm));
        prove(thm);
    }

    /*! \brief Show that <tt>distinct(a_0, ... , a_n)</tt> is
       unsatisfiable when \c a_i's are arrays from boolean to
       boolean and n > 4.
       
       This example also shows how to use the \c distinct construct.
    */
    public void array_example2() 
    {        
        Console.WriteLine("array_example2");
        
        for (int n = 2; n <= 5; n++) {
            Console.WriteLine("n = {0}", n);
            mk_context();
            
	    if (n == 3) {
		z3.OpenLog("array3.z3");
	    }
            Sort bool_type   = z3.MkBoolSort();
            Sort array_type  = z3.MkArraySort(bool_type, bool_type);
            Term[] a = new Term[n];
            
            /* create arrays */
            for (int i = 0; i < n; i++) {
                a[i] = z3.MkConst(String.Format("array_{0}",i), array_type);
            }
            
            /* assert distinct(a[0], ..., a[n]) */
            Term d = z3.MkDistinct( a);
            Console.WriteLine("{0}", z3.ToString(d));
            z3.AssertCnstr(d);
            
            /* context is satisfiable if n < 5 */
	    Model model = null;
            check(n < 5 ? LBool.True : LBool.False, out model);
            if (n < 5) {
                for (int i = 0; i < n; i++) {
                    Console.WriteLine("{0} = {1}", 
                                      z3.ToString(a[i]), 
                                      z3.ToString(model.Eval(a[i])));
                }
            }
	    if (model != null) {
		model.Dispose();
	    }
        }
    }

    /*! \brief Tuples.

        Check that the projection of a tuple returns the corresponding element.
    */
    public void tuple_example() {
        mk_context();
        Sort int_type = mk_int_type();
        FuncDecl[] decls = new FuncDecl[2];
	FuncDecl mk_tuple = null;
        Sort tuple = z3.MkTupleSort
	    (
	     z3.MkSymbol("mk_tuple"),                        // name of tuple constructor
	     new Symbol[]{z3.MkSymbol("first"),z3.MkSymbol("second")},    // names of projection operators
	     new Sort[]{int_type,int_type}, // types of projection operators
	     out mk_tuple,
	     decls                              // return declarations.
            );
        FuncDecl first = decls[0];         // declarations are for projections
        FuncDecl second = decls[1];
        Term x = z3.MkConst("x",int_type);
        Term y = z3.MkConst("y",int_type);
        Term n1 = z3.MkApp(mk_tuple, x,y);
        Term n2 = z3.MkApp(first, n1);
        Term n3 = z3.MkEq(x, n2);
        Console.WriteLine("Tuple example: {0}",z3.ToString(n3));
        prove(n3);        
    }

    /**
       \brief Simple bit-vector example. This example disproves that x - 10 <= 0 IFF x <= 10 for (32-bit) machine integers
    */
    public void bitvector_example1() 
    {
	Console.WriteLine("\nbitvector_example1");
    
	mk_context();
    
	Sort bv_type   = z3.MkBvSort(32);
	Term x           = mk_var("x", bv_type);
	Term zero        = z3.MkNumeral("0", bv_type);
	Term ten         = z3.MkNumeral("10", bv_type);
	Term x_minus_ten = z3.MkBvSub(x, ten);
	/* bvsle is signed less than or equal to */
	Term c1          = z3.MkBvSle(x, ten);
	Term c2          = z3.MkBvSle(x_minus_ten, zero);
	Term thm         = z3.MkIff(c1,c2);
	Console.WriteLine("disprove: x - 10 <= 0 IFF x <= 10 for (32-bit) machine integers");
	prove(thm);
    }

    /**
       \brief Find x and y such that: x ^ y - 103 == x * y
    */
    public void bitvector_example2()
    {
	mk_context();
 
	/* construct x ^ y - 103 == x * y */
	Sort bv_type = z3.MkBvSort(32);
	Term x = mk_var("x", bv_type);
	Term y = mk_var("y", bv_type);
	Term x_xor_y = z3.MkBvXor(x,y);
	Term c103 = z3.MkNumeral("103", bv_type);
	Term lhs = z3.MkBvSub(x_xor_y, c103);
	Term rhs = z3.MkBvMul(x,y);
	Term ctr = z3.MkEq(lhs, rhs);
	
	Console.WriteLine("\nbitvector_example2");
	Console.WriteLine("find values of x and y, such that x ^ y - 103 == x * y");
	
	/* add the constraint <tt>x ^ y - 103 == x * y<\tt> to the logical context */
	z3.AssertCnstr(ctr);
	
	/* find a model (i.e., values for x an y that satisfy the constraint */
	check2(LBool.True);
    }


    /*! \brief Injective functions.

        Check that the projection of a tuple returns the corresponding element.
    */
    public void injective_example() {
        mk_context();
        Sort int_type = mk_int_type();
        FuncDecl f = z3.MkInjectiveFunction("f_inj", new Sort[]{int_type}, int_type);
        Term x = z3.MkConst("x",int_type);
        Term y = z3.MkConst("y",int_type);
        Term fx = z3.MkApp(f,x);
        Term f_y = z3.MkApp(f,y);
        Term c = z3.MkImplies(z3.MkEq(fx,f_y), z3.MkEq(x,y));
        Console.WriteLine("Injective example: {0}",z3.ToString(c));
        prove(c);        
    }

    /**
       \brief Demonstrates how to use the SMTLIB parser.
    */
    public void parser_example1() 
    {
	mk_context();
	
	Console.WriteLine("\nparser_example1");
		
	Term[] formulas, assumptions;
	FuncDecl[] decls;
	z3.ParseSmtlibString("(benchmark tst :extrafuns ((x Int) (y Int)) :formula (> x y) :formula (> x 0))",
			     null, null, out assumptions, out formulas, out decls);
	foreach (var f in formulas) {
	    Console.WriteLine("formula {0}", f);
	    z3.AssertCnstr(f);
	}	
	check2(LBool.True);
    }

   /**
      \brief Demonstrates how to initialize the parser symbol table.
   */
    public void parser_example2() 
    {
	mk_context();
	Console.WriteLine("\nparser_example2");
    
	/* 
	   Z3_enable_arithmetic doesn't need to be invoked in this example
	   because it will be implicitly invoked by mk_int_var.
	*/
    
	FuncDecl a = z3.MkConstDecl("a", z3.MkIntSort());
	FuncDecl b = z3.MkConstDecl("b", z3.MkIntSort());
	FuncDecl[] decls   = new FuncDecl[]{a,b};
	Term[] formulas, assumptions;
	FuncDecl[] new_decls;

	z3.ParseSmtlibString(
                           "(benchmark tst :formula (> a b))",
			   null, 
			   decls, 
	                   out assumptions, out formulas, out new_decls);
	Term f = formulas[0];
	Console.WriteLine("formula: {0}", f);
	z3.AssertCnstr(f);
	check2(LBool.True);
    }

    /**
       \brief Demonstrates how to initialize the parser symbol table.
    */
    public void parser_example3() 
    {	
	Console.WriteLine("\nparser_example3");
	
	mk_context();
	
	/* declare function g */
	Sort int_type    = z3.MkIntSort();
	FuncDecl g = z3.MkFuncDecl("g", new Sort[]{int_type, int_type}, int_type);
	Term[] formulas, assumptions;
	FuncDecl[] new_decls;
	
	assert_comm_axiom(g);
	
	z3.ParseSmtlibString("(benchmark tst :formula (forall (x Int) (y Int) (implies (= x y) (= (g x 0) (g 0 y)))))",
			     null, 
			     new FuncDecl[]{g},
	                     out assumptions, out formulas, out new_decls);
	Term thm = formulas[0];
	Console.WriteLine("formula: {0}", thm);
	prove(thm);
    }

    /**
       \brief Display the declarations, assumptions and formulas in a SMT-LIB string.
    */
    public void parser_example4() 
    {
	mk_context();
	
	Console.WriteLine("\nparser_example4");
    
	Term[] formulas, assumptions;
	FuncDecl[] decls;    
	z3.ParseSmtlibString(  "(benchmark tst :extrafuns ((x Int) (y Int)) :assumption (= x 20) :formula (> x y) :formula (> x 0))",
			       null, null, 
	                     out assumptions, out formulas, out decls);
	foreach (var decl in decls) {
	    Console.WriteLine("Declaration: {0}", decl);
	}
	foreach (var f in assumptions) {
	    Console.WriteLine("Assumption: {0}", f);
	}
	foreach (var f in formulas) {
	    Console.WriteLine("Formula: {0}", f);
	}
    }

    /**
       \brief Demonstrates how to handle parser errors using Z3 error handling support.
    */
    public void parser_example5() 
    {
	Console.WriteLine("\nparser_example5");

	Term[] formulas, assumptions;
	FuncDecl[] decls;    

	try {
	    z3.ParseSmtlibString(
				 /* the following string has a parsing error: missing parenthesis */
				 "(benchmark tst :extrafuns ((x Int (y Int)) :formula (> x y) :formula (> x 0))",
				 null, null, out assumptions, out formulas, out decls);
	}
	catch (Z3Error e) {
	    Console.WriteLine("Z3 error: {0}", e);
	}
    }
 
    /**
       \brief Create an ite-term (if-then-else terms).
    */
    public void ite_example() 
    {
	Console.WriteLine("\nite_example");
	mk_context();
		
	Term f    = z3.MkFalse();
	Term one  = mk_int(1);
	Term zero = mk_int(0);
	Term ite  = z3.MkIte(f, one, zero);
	
	Console.WriteLine("term: {0}", ite);
    }

    /**
       \brief Create an enumeration data type.
    */
    void enum_example() {
	mk_context();
	Symbol name = z3.MkSymbol("fruit");

	FuncDecl[] enum_consts = new FuncDecl[3];
	FuncDecl[] enum_testers = new FuncDecl[3];

	Console.WriteLine("\nenum_example");
	
	
	Sort fruit = z3.MkEnumerationSort("fruit", new string[] {"apple", "banana", "orange" }, enum_consts, enum_testers);
	
	Console.WriteLine("{0}", (enum_consts[0]));
	Console.WriteLine("{0}", (enum_consts[1]));
	Console.WriteLine("{0}", (enum_consts[2]));
	
	Console.WriteLine("{0}", (enum_testers[0]));
	Console.WriteLine("{0}", (enum_testers[1]));
	Console.WriteLine("{0}", (enum_testers[2]));
	
	Term apple  = z3.MkConst(enum_consts[0]);
	Term banana = z3.MkConst(enum_consts[1]);
	Term orange = z3.MkConst(enum_consts[2]);
	
	/* Apples are different from oranges */
	prove2(z3.MkNot(z3.MkEq(apple, orange)), true);
	
	/* Apples pass the apple test */
	prove2(z3.MkApp(enum_testers[0], apple), true);
	
	/* Oranges fail the apple test */
	prove2(z3.MkApp(enum_testers[0], orange), false);
	prove2(z3.MkNot(z3.MkApp(enum_testers[0], orange)), true);
	
	Term fruity = mk_var("fruity", fruit);
	
	/* If something is fruity, then it is an apple, banana, or orange */
	
	prove2(z3.MkOr(new Term[]{ z3.MkEq(fruity,apple), z3.MkEq(fruity,banana), z3.MkEq(fruity,orange)}), true);	
    }


    /**
       \brief Create a list datatype.
    */
    public void list_example() {
	mk_context();

	Sort int_ty, int_list;
	FuncDecl nil_decl, is_nil_decl, cons_decl, is_cons_decl, head_decl, tail_decl;
	Term nil, l1, l2, x, y, u, v, fml, fml1;
		
	Console.WriteLine("\nlist_example");
	
	int_ty = z3.MkIntSort();
	
	int_list = z3.MkListSort("int_list", int_ty,
				 out nil_decl, out is_nil_decl, out cons_decl, out is_cons_decl, out head_decl, out tail_decl);
	
	nil = z3.MkConst(nil_decl);
	l1 = mk_binary_app(cons_decl, mk_int(1), nil);
	l2 = mk_binary_app(cons_decl, mk_int(2), nil);
	
	/* nil != cons(1, nil) */
	prove2(z3.MkNot(z3.MkEq(nil, l1)), true);
	
	/* cons(2,nil) != cons(1, nil) */
	prove2(z3.MkNot(z3.MkEq(l1, l2)), true);
	
	/* cons(x,nil) = cons(y, nil) => x = y */
	x = mk_var("x", int_ty);
	y = mk_var("y", int_ty);    
	l1 = mk_binary_app(cons_decl, x, nil);
	l2 = mk_binary_app(cons_decl, y, nil);
	prove2(z3.MkImplies(z3.MkEq(l1,l2), z3.MkEq(x, y)), true);
	
	/* cons(x,u) = cons(x, v) => u = v */
	u = mk_var("u", int_list);
	v = mk_var("v", int_list);    
	l1 = mk_binary_app(cons_decl, x, u);
	l2 = mk_binary_app(cons_decl, y, v);
	prove2(z3.MkImplies(z3.MkEq(l1,l2), z3.MkEq(u, v)), true);
	prove2(z3.MkImplies(z3.MkEq(l1,l2), z3.MkEq(x, y)), true);
	
	/* is_nil(u) or is_cons(u) */
	prove2(z3.MkOr(z3.MkApp(is_nil_decl, u), z3.MkApp(is_cons_decl, u)), true);
	
	/* occurs check u != cons(x,u) */    
	prove2(z3.MkNot(z3.MkEq(u, l1)), true);
	
	/* destructors: is_cons(u) => u = cons(head(u),tail(u)) */
	fml1 = z3.MkEq(u, mk_binary_app(cons_decl, mk_unary_app(head_decl, u), mk_unary_app(tail_decl, u)));
	fml = z3.MkImplies(z3.MkApp(is_cons_decl, u), fml1);
	Console.WriteLine("Formula {0}", fml);

	prove2(fml, true);
	
	prove2(fml1, false);
    }



    /**
       \brief Create a binary tree datatype.
    */ 
    public void tree_example() {
	mk_context();
	Sort cell;
	FuncDecl nil_decl, is_nil_decl, cons_decl, is_cons_decl, car_decl, cdr_decl;
	Term nil, l1, l2, x, y, u, v, fml, fml1;
	string[] head_tail = new string[]{ "car", "cdr" };
	Sort[] sorts = new Sort[]{ null, null};
	uint[] sort_refs = new uint[]{ 0, 0 };
	Constructor nil_con, cons_con;
	
	Console.WriteLine("\ntree_example");
	
	nil_con  = z3.MkConstructor("nil", "is_nil", null, null, null);
	cons_con = z3.MkConstructor("cons", "is_cons", head_tail,  sorts, sort_refs);
	Constructor[] constructors = new Constructor[] { nil_con, cons_con };
    
	cell = z3.MkDataType("cell", constructors);

	nil_decl = z3.GetConstructor(nil_con);
	is_nil_decl = z3.GetTester(nil_con);
	cons_decl = z3.GetConstructor(cons_con);
	is_cons_decl = z3.GetTester(cons_con);
	FuncDecl[] cons_accessors = z3.GetAccessors(cons_con);
	car_decl = cons_accessors[0];
	cdr_decl = cons_accessors[1];

	nil_con.Dispose();
	cons_con.Dispose();
		
	
	nil = z3.MkConst(nil_decl);
	l1 = mk_binary_app(cons_decl, nil, nil);
	l2 = mk_binary_app(cons_decl, l1, nil);
	
	/* nil != cons(nil, nil) */
	prove2(z3.MkNot(z3.MkEq(nil, l1)), true);
	
	/* cons(x,u) = cons(x, v) => u = v */
	u = mk_var("u", cell);
	v = mk_var("v", cell);    
	x = mk_var("x", cell);
	y = mk_var("y", cell);    
	l1 = mk_binary_app(cons_decl, x, u);
	l2 = mk_binary_app(cons_decl, y, v);
	prove2(z3.MkImplies(z3.MkEq(l1,l2), z3.MkEq(u, v)), true);
	prove2(z3.MkImplies(z3.MkEq(l1,l2), z3.MkEq(x, y)), true);
	
	/* is_nil(u) or is_cons(u) */
	prove2(z3.MkOr(z3.MkApp(is_nil_decl, u),z3.MkApp(is_cons_decl, u)) , true);
	
	/* occurs check u != cons(x,u) */    
	prove2(z3.MkNot(z3.MkEq(u, l1)), true);
	
	/* destructors: is_cons(u) => u = cons(car(u),cdr(u)) */
	fml1 = z3.MkEq(u, mk_binary_app(cons_decl, mk_unary_app(car_decl, u), mk_unary_app(cdr_decl, u)));
	fml = z3.MkImplies(z3.MkApp(is_cons_decl, u), fml1);
	Console.WriteLine("Formula {0}", fml);
	prove2(fml, true);
	
	prove2(fml1, false);
	
    }


    /**
       \brief Create a forest of trees.
       
       forest ::= nil | cons(tree, forest)
       tree   ::= nil | cons(forest, forest)
    */ 

    public void forest_example() {
	mk_context();
	Sort tree, forest;
	FuncDecl nil1_decl, is_nil1_decl, cons1_decl, is_cons1_decl, car1_decl, cdr1_decl;
	FuncDecl nil2_decl, is_nil2_decl, cons2_decl, is_cons2_decl, car2_decl, cdr2_decl;
	Term nil1, nil2, t1, t2, t3, t4, f1, f2, f3, l1, l2, x, y, u, v;

        //
        // Declare the names of the accessors for cons.
	// Then declare the sorts of the accessors. 
	// For this example, all sorts refer to the new types 'forest' and 'tree'
	// being declared, so we pass in null for both sorts1 and sorts2.
	// On the other hand, the sort_refs arrays contain the indices of the
	// two new sorts being declared. The first element in sort1_refs
	// points to 'tree', which has index 1, the second element in sort1_refs array
	// points to 'forest', which has index 0.
	// 
	string[] head_tail1 = new string[] { "head", "tail" };
	Sort[] sorts1       = new Sort[]   {  null, null };
	uint[] sort1_refs   = new uint[]   {  1,    0}; // the first item points to a tree, the second to a forest
        
	string[] head_tail2 = new string[] { "car", "cdr" };
	Sort[] sorts2       = new Sort[]   { null,  null };
	uint[] sort2_refs   = new uint[]   { 0,     0}; // both items point to the forest datatype.
	Constructor nil1_con, cons1_con, nil2_con, cons2_con;
	Constructor[] constructors1 = new Constructor[2], constructors2 = new Constructor[2];
	string[] sort_names = { "forest", "tree" };

	Console.WriteLine("\nforest_example");
	
	/* build a forest */
	nil1_con  = z3.MkConstructor("nil", "is_nil", null, null, null);
	cons1_con = z3.MkConstructor("cons1", "is_cons1", head_tail1, sorts1, sort1_refs);
	constructors1[0] = nil1_con;
	constructors1[1] = cons1_con;
	
	/* build a tree */
	nil2_con  = z3.MkConstructor("nil2", "is_nil2", null, null, null);
	cons2_con = z3.MkConstructor("cons2", "is_cons2", head_tail2, sorts2, sort2_refs);
	constructors2[0] = nil2_con;
	constructors2[1] = cons2_con;

	
	Constructor[][] clists = new Constructor[][] { constructors1, constructors2 };
	
	Sort[] sorts = z3.MkDataTypes(sort_names, clists);
	forest = sorts[0];
	tree = sorts[1];
	
	//
	// Now that the datatype has been created.
	// Query the constructors for the constructor
	// functions, testers, and field accessors.
	//
	nil1_decl = z3.GetConstructor(nil1_con);
	is_nil1_decl = z3.GetTester(nil1_con);
	cons1_decl = z3.GetConstructor(cons1_con);
	is_cons1_decl = z3.GetTester(cons1_con);
	FuncDecl[] cons1_accessors = z3.GetAccessors(cons1_con);
	car1_decl = cons1_accessors[0];
	cdr1_decl = cons1_accessors[1];

	nil2_decl = z3.GetConstructor(nil2_con);
	is_nil2_decl = z3.GetTester(nil2_con);
	cons2_decl = z3.GetConstructor(cons2_con);
	is_cons2_decl = z3.GetTester(cons2_con);
	FuncDecl[] cons2_accessors = z3.GetAccessors(cons2_con);
	car2_decl = cons2_accessors[0];
	cdr2_decl = cons2_accessors[1];

	
	nil1_con.Dispose();
	nil2_con.Dispose();
	cons1_con.Dispose();
	cons2_con.Dispose();

	nil1 = z3.MkConst(nil1_decl);
	nil2 = z3.MkConst(nil2_decl);
	f1 = mk_binary_app(cons1_decl, nil2, nil1);
	t1 = mk_binary_app(cons2_decl, nil1, nil1);
	t2 = mk_binary_app(cons2_decl, f1, nil1);
	t3 = mk_binary_app(cons2_decl, f1, f1);
	t4 = mk_binary_app(cons2_decl, nil1, f1);
	f2 = mk_binary_app(cons1_decl, t1, nil1);
	f3 = mk_binary_app(cons1_decl, t1, f1);
	
	
	/* nil != cons(nil,nil) */
	prove2(z3.MkNot(z3.MkEq(nil1, f1)), true);
	prove2(z3.MkNot(z3.MkEq(nil2, t1)), true);


	/* cons(x,u) = cons(x, v) => u = v */
	u = mk_var("u", forest);
	v = mk_var("v", forest);    
	x = mk_var("x", tree);
	y = mk_var("y", tree);
	l1 = mk_binary_app(cons1_decl, x, u);
	l2 = mk_binary_app(cons1_decl, y, v);
	prove2(z3.MkImplies(z3.MkEq(l1,l2), z3.MkEq(u, v)), true);
	prove2(z3.MkImplies(z3.MkEq(l1,l2), z3.MkEq(x, y)), true);
	
	/* is_nil(u) or is_cons(u) */
	prove2(z3.MkOr(z3.MkApp(is_nil1_decl, u), z3.MkApp(is_cons1_decl, u)), true);
	
	/* occurs check u != cons(x,u) */    
	prove2(z3.MkNot(z3.MkEq(u, l1)), true);
    }


    /**
       \brief Demonstrate how to use #Eval.
    */
    public void eval_example1() 
    {
	Console.WriteLine("\neval_example1");
	mk_context();
	Term x = mk_int_var("x");
	Term y = mk_int_var("y");
	Term two = mk_int(2);
    
	/* assert x < y */
	z3.AssertCnstr(z3.MkLt(x,y));

	/* assert x > 2 */
	z3.AssertCnstr(z3.MkGt(x, two));

	/* find model for the constraints above */
	Model model = null;
	if (LBool.True == z3.CheckAndGetModel(out model)) {
	    model.Display(Console.Out);
	    Console.WriteLine("\nevaluating x+y");
	    Term v = model.Eval(z3.MkAdd(x, y));
	    if (v != null) {
		Console.WriteLine("result = {0}", z3.ToString(v));
	    }
	    else {
		Console.WriteLine("Failed to evaluate: x+y");
	    }
	    model.Dispose();
	}
	else {
	    Console.WriteLine("BUG, the constraints are satisfiable.");
	}
    }

    /**
       \brief Demonstrate how to use #Eval on tuples.
    */
    public void eval_example2() 
    {
	Console.WriteLine("\neval_example2");
        mk_context();
        Sort int_type = mk_int_type();
        FuncDecl[] decls = new FuncDecl[2];
	FuncDecl mk_tuple = null;
        Sort tuple = z3.MkTupleSort
	    (
	     z3.MkSymbol("mk_tuple"),                        // name of tuple constructor
	     new Symbol[]{z3.MkSymbol("first"),z3.MkSymbol("second")},    // names of projection operators
	     new Sort[]{int_type,int_type}, // types of projection operators
	     out mk_tuple,
	     decls                              // return declarations.
            );
        FuncDecl first = decls[0];     // declarations are for projections
        FuncDecl second = decls[1];
	Term tup1 = z3.MkConst("t1",tuple);
	Term tup2 = z3.MkConst("t2", tuple);
	/* assert tup1 != tup2 */
	z3.AssertCnstr(z3.MkNot(z3.MkEq(tup1, tup2)));
	/* assert first tup1 = first tup2 */
	z3.AssertCnstr(z3.MkEq(z3.MkApp(first,tup1), z3.MkApp(first, tup2)));

	/* find model for the constraints above */
	Model model = null;
	if (LBool.True == z3.CheckAndGetModel(out model)) {
	    model.Display(Console.Out);	
	    Console.WriteLine("evaluating tup1 {0}", z3.ToString(model.Eval(tup1)));
	    Console.WriteLine("evaluating tup2 {0}", z3.ToString(model.Eval(tup2)));
	    Console.WriteLine("evaluating second(tup2) {0}", 
			      z3.ToString(model.Eval(z3.MkApp(second,tup2))));
	    model.Dispose();
	}
	else {
	    Console.WriteLine("BUG, the constraints are satisfiable.");
	}
    }

    /**
       \brief Demonstrate how to use #Push and #Pop to control 
       the size of models.

       Note: this test is specialized to 32-bit bitvectors.
    */
    public void check_small(Term[] to_minimize) {
	
	Sort bv32 = mk_bv_type(32);

	int num_terms = to_minimize.Length;
	UInt32[] upper = new UInt32[num_terms];
	UInt32[] lower = new UInt32[num_terms];
	Term[] values = new Term[num_terms];
	for (int i = 0; i < upper.Length; ++i) {
	    upper[i] = UInt32.MaxValue;
	    lower[i] = 0;
	}
	bool some_work = true;
	int last_index = -1;
	UInt32 last_upper = 0;
	while (some_work) {
	    z3.Push();
	    
	    bool check_is_sat = true;
	    while(check_is_sat && some_work) {
		// Assert all feasible bounds.
		for (int i = 0; i < num_terms; ++i) {
		    z3.AssertCnstr(z3.MkBvUle(to_minimize[i], mk_bv32(upper[i])));
		}
		Model model = null;
		check_is_sat = LBool.True == z3.CheckAndGetModel(out model);
		if (!check_is_sat) {
		    if (last_index != -1) {
			lower[last_index] = last_upper+1;
		    }
		    if (model != null) {
			model.Dispose();
		    }
		    break;
		}
		model.Display(Console.Out);

		// narrow the bounds based on the current model.
		for (int i = 0; i < num_terms; ++i) {
		    Term v = model.Eval(to_minimize[i]);
		    UInt64 ui = z3.GetNumeralUInt64(v);
		    if (ui < upper[i]) {
			upper[i] = (UInt32)ui;
		    }
		    Console.WriteLine("{0} {1} {2}",i,lower[i],upper[i]);
		}
		model.Dispose();
		// find a new bound to add
		some_work = false;
		last_index = 0;
		for (int i = 0; i < num_terms; ++i) {
		    if (lower[i] < upper[i]) {			
			last_upper = (upper[i] + lower[i])/2;
			last_index = i;
			z3.AssertCnstr(z3.MkBvUle(to_minimize[i], mk_bv32(last_upper)));
			some_work = true;
			break;
		    }
		}
	    }
	    z3.Pop();
	}
    }

    /**
       \brief Reduced-size model generation example.
    */
    public void find_small_model_example() {
	mk_context();
	Term x = mk_bv_var("x",32);
	Term y = mk_bv_var("y",32);
	Term z = mk_bv_var("z",32);
	Sort bv32 = mk_bv_type(32);
	z3.AssertCnstr(z3.MkBvUle(x, z3.MkBvAdd(y, z)));
	check_small(new Term[]{x,y,z});
    }

    /**
       \brief Simplifier example.
    */
    public void simplifier_example() {
	mk_context();
	Term x = mk_int_var("x");
	Term y = mk_int_var("y");
	Term z = mk_int_var("z");
	Term u = mk_int_var("u");

	Term t1 = z3.MkAdd(x, z3.MkSub(y,z3.MkAdd(x,z)));
	Term t2 = z3.Simplify(t1);
	Console.WriteLine("{0} -> {1}", z3.ToString(t1), z3.ToString(t2));
    }

    public void unsat_core_and_proof_example() {
	if (this.z3 != null) {
	    this.z3.Dispose();
	}
	Config p = new Config();
        // p.SetParamValue("MODEL","true");
        p.SetParamValue("PROOF_MODE","2");
        this.z3 = new Context(p);
	p.Dispose();

	Term pa = mk_bool_var("PredA");
	Term pb = mk_bool_var("PredB");
	Term pc = mk_bool_var("PredC");
	Term pd = mk_bool_var("PredD");
	Term p1 = mk_bool_var("P1");
	Term p2 = mk_bool_var("P2");
	Term p3 = mk_bool_var("P3");
	Term p4 = mk_bool_var("P4");
	Term[] assumptions = new Term[] {z3.MkNot(p1), z3.MkNot(p2), z3.MkNot(p3), z3.MkNot(p4) };
	Term f1 = z3.MkAnd( new Term[] { pa, pb, pc });
	Term f2 = z3.MkAnd( new Term[] { pa, z3.MkNot(pb), pc });
	Term f3 = z3.MkOr(z3.MkNot(pa), z3.MkNot(pc));
	Term f4 = pd;
	
	z3.AssertCnstr(z3.MkOr(f1,p1));
	z3.AssertCnstr(z3.MkOr(f2,p2));
	z3.AssertCnstr(z3.MkOr(f3,p3));
	z3.AssertCnstr(z3.MkOr(f4,p4));
	Term[] core = null;
	Term proof;
	Model m = null;
	LBool result;
   	
	result = z3.CheckAssumptions(out m, assumptions, out proof, out core);
	
	if (result == LBool.False) {
	    Console.WriteLine("unsat");
	    Console.WriteLine("proof: {0}", proof);
	    foreach (Term c in core) {
		Console.WriteLine("{0}", c);
	    }
	}
	if (m != null) {
	    m.Dispose();
	}
    }

    static void Main() {
        TestManaged test = new TestManaged();
        test.simple_example();
        test.find_model_example1();
        test.find_model_example2();
        test.prove_example1();
        test.prove_example2();
        test.push_pop_example1();
        test.quantifier_example1();
        test.quantifier_example1_abs();
        test.array_example1();
        test.array_example2();
        test.tuple_example();
	test.bitvector_example1();
	test.bitvector_example2();
    	test.parser_example1();
    	test.parser_example2();
   	test.parser_example3();
    	test.parser_example4();
    	test.parser_example5();
    	test.ite_example();
    	test.enum_example();
    	test.list_example();
    	test.tree_example();
    	test.forest_example();
        test.injective_example();
	test.eval_example1();
	test.eval_example2();
	test.find_small_model_example();
	test.simplifier_example();
	test.unsat_core_and_proof_example();
	test.z3.Dispose();
       
    }
}

/*@}*/






