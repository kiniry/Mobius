//
//  Copyright (c) Microsoft Corporation.  All rights reserved.
//
//  THIS CODE AND INFORMATION IS PROVIDED "AS IS" WITHOUT WARRANTY OF ANY
//  KIND, EITHER EXPRESSED OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE
//  IMPLIED WARRANTIES OF MERCHANTABILITY AND/OR FITNESS FOR A PARTICULAR
//  PURPOSE.
//
//  Author:
//
//  Byron Cook (Nov. 16, 2007)
//



#light

#I "c:/Program Files/Microsoft Research/Z3-1.1/bin"
#r @"Microsoft.Z3.dll"


open Microsoft.Z3
open Microsoft.FSharp.Math
open Matrix.Generic


//---------------------------------------------------------------
//  Ignore this.  F#'s Generic Matrix map is not general enough in type 
// Additions to library -- lifted out of example
module Matrix =
  module Generic =
    let map f (m:Matrix<'a>) = Matrix.Generic.init m.NumRows m.NumCols (fun r c -> f m.[r,c])

module RowVector =
  module Generic =
    let map f (rv:RowVector<'a>) = RowVector.Generic.init rv.Length (fun i -> f rv.[i])



// Load up Z3.  Note: we need to dispose of z3 at the end.
let p = new Config()
p.SetParamValue("MODEL","true")
let z3 = new Context(p) 
p.Dispose()
    

//---------------------------------------------------------------
// We make a type z3e

type z3e = Z of nativeint
let z3ePtr (Z p) = p

let integer (i:int) = Z (z3.MkNumeral(i,z3.MkRealType()))
let zero  = integer 0                                  
let one   = integer 1
let add (Z a) (Z b) = Z(z3.MkAdd(a,b))                  
let sub (Z a) (Z b) = Z(z3.MkSub(a,b))
let mul (Z a) (Z b) = Z(z3.MkMul(a,b))
let neg z = mul (integer (-1)) z

//---------------------------------------------------------------
// Register arithmetic on z3e, allowing me to use overloaded +, *, etc                               

let FormNumerics =                                          
    { new INumeric<_> with 
      member ops.Zero          = zero
      member ops.One           = one
      member ops.Add(a,b)      = add a b
      member ops.Subtract(a,b) = sub a b
      member ops.Multiply(a,b) = mul a b
      member ops.Negate(a)     = neg a
      
      // The remainder of these ops are left unfinished for now.                                             
      member ops.Abs(a)  = failwith "no abs" 
      member ops.Sign(a) = failwith "no sign"
      member ops.ToString((x:z3e),fmt,fmtprovider) = "formula" 
      member ops.Parse(s,numstyle,fmtprovider) = failwith "no parsing" 
     }

Math.GlobalAssociations.RegisterNumericAssociation (FormNumerics)


//---------------------------------------------------------------
// Wrapper to Z3 procedure

let solve (Z q) =
    z3.Push();
    z3.AssertCnstr(q) ;
    let model = ref null in                                 
    let ans = z3.CheckAndGetModel(model) in
    z3.Pop();
    match ans with
    | LBool.True      -> Some (!model)                      
    | LBool.False     -> None
    | _ -> failwith "Error!\n"
                                  

// ---------------------------------------------------------------
// Some z3e helper functions 

let make_var (name:string) =  Z (z3.MkConst(name,z3.MkRealType())) 
let make_const (x:int) = integer x
let conjunction xs = Z(z3.MkAnd (Array.of_list (List.map (fun (Z x) -> x) xs))) ;;
                                         
let make_constraint f (v:RowVector<z3e>) =
    let vl = Vector.Generic.fold (fun x (Z y) -> Z y::x) [] (v.Transpose) in
    let cs = List.map f vl in
    conjunction cs 

let (=*) v (k:int) = make_constraint (fun (Z x) -> Z(z3.MkEq(x,z3.MkNumeral(k,z3.MkRealType())))) v  
let (>=*) v (k:int) = make_constraint (fun (Z x) -> Z(z3.MkGe(x,z3.MkNumeral(k,z3.MkRealType())))) v
let (<*) v (k:int) = make_constraint (fun (Z x) -> Z(z3.MkLt(x,z3.MkNumeral(k,z3.MkRealType())))) v        


//---------------------------------------------------------------

// naturals = 0,1,2.......
let naturals = Seq.unfold (fun i -> Some (i,i+1I)) 0I   

// vars = v0,v1,v2,v3,...
let vars = { for i in naturals -> make_var (sprintf "v%O" i) }     

let varEnumerator = vars.GetEnumerator()                                    
let fresh_var () = let r = varEnumerator.MoveNext() in assert(r); varEnumerator.Current  

 

 

// -------------------------------------------------------------------
// Synthesis procedure 

let synthesis R =

    // TODO:  We should GC and re-create context so as to GC variables from
    // previous runs.

    // Cut the input relation into its components (as described in Podelski & Rybalchenko)
    // R defined as "coefs (X/X') + b <= 0" where coefs is a r*c matrix
    let coefs = Matrix.Generic.of_list R in                         
    let r,c = coefs.Dimensions in
    let b  = - coefs.[ 0 .. r-1 , c-1        .. c-1     ] in
    let A  =   coefs.[ 0 .. r-1 , 0          .. (c-2)/2 ] in
    let A' =   coefs.[ 0 .. r-1 , (c-2)/2 +1 .. c-2     ] in

    // Make z3e versions of matrices A, A', and b
    let b_symb  = Matrix.Generic.map make_const b  in                
    let A_symb  = Matrix.Generic.map make_const A  in
    let A_symb' = Matrix.Generic.map make_const A' in

    // Create z3e-vectors lambda1 and lambda2
    let lambda1 = RowVector.Generic.init r (fun i -> fresh_var ())  
    let lambda2 = RowVector.Generic.init r (fun i -> fresh_var ())  

    // Construct the query as described in Podelski & Rybalchenko, Fig. 1
    let query = conjunction [ lambda1 >=* 0 
                            ; lambda2 >=* 0 
                            ; lambda1 * A_symb' =* 0                          
                            ; (lambda1 - lambda2) * A_symb =* 0 
                            ; lambda2 * (A_symb + A_symb') =* 0
                            ; lambda2 * b_symb <* 0
                            ]
    in

    // Search for a model via Z3 solve
    match solve query with      
                                                   
    // Case: relation not proved well-founded, thus no ranking function is returned
    | None -> None     

    // Case: relation is well-founded, construct a ranking function and bound
    | Some (m as model) -> 
        // Get concrete instance for lambda1 and lambda2
        let get_val (Z x) = m.GetNumeralValueInt(m.Eval(x)) in
        let lambda1_inst  = RowVector.Generic.map get_val lambda1       
        let lambda2_inst  = RowVector.Generic.map get_val lambda2       
        m.Dispose();   
        
        // Compute ranking function "r" and bound "delta_0" as in Podelski & Rybalchenko, Fig. 1
        let r = lambda2_inst * A' in                                    
        let delta_0 = - lambda1_inst * b in                             
        Some(r,delta_0)


// ------------------------------------------------------------------
// Examples 

// Simple example.  R0 represents "x'=x-1 && x>0"      
let R0 = [ [-1;0;0]          // x >= 0
         ; [-1;1;1]          // x'>= x-1
         ; [1;-1;-1]         // x'<= x-1
         ]
         
let R0_expected = Some( RowVector.Generic.of_list [1]
                      , RowVector.Generic.of_list [0]
                      )
                                                               
 // Example, slide 17 from in http://research.microsoft.com/TERMINATOR/l2.pps
 // note: relation is A'A in the slides, here it is AA'
let R1 = [ [-1;0;0;0;1]      // x > 0
         ; [-1;0;1;0;1]      // x'>= x-1
         ; [1;0;-1;0;-1]     // x'<= x-1
         ; [0;-1;0;0;1]      // y > 0
         ; [0;1;0;-1;1]      // y' > y
         ]  

let R1_expected = Some( RowVector.Generic.of_list [1;0]
                      , RowVector.Generic.of_list [1]
                      )
 

// Example 1 from http://www.mpi-sws.mpg.de/~rybal/papers/vmcai04-linear-ranking.pdf   
// R2 represents loop "while (i-j>=1) do (i,j) := (i-Nat(),j+Pos()); od" 
// where "Nat()" could return any natural number and "Pos()" could return any positive number                                  
let R2 = [ [-1;1;0;0;1]      // -i + j + 1 <= 0
         ;  [-1;0;1;0;0]     // -i + i'+ 0 <= 0 
         ;  [0;1;0;-1;1]     // j - j' + 1 <= 0
         ]
         
let R2_expected = Some( RowVector.Generic.of_list [1;-1]
                      , RowVector.Generic.of_list [1]
                      )
                        
// Example of termination bug.  Shouldn't be well-founded.  Represents "x'=x+1 && x>0"     
let R3 = [ [-1;0;1]         // x > 0
         ;  [-1;1;-1]       // x'>= x+1
         ;  [1;-1;1]        // x'<= x+1
         ]

let R3_expected = None

let run s (R:int list list) expected =
    Printf.printf "Synthesis for %s\n" s;
    let result = synthesis R in
    assert(result=expected);
    begin match result with
    | None -> Printf.printf "Not well-founded\n"
    | Some(rf,b) ->  Printf.printf "Rank function: %s\n" (rf.ToString());
                     Printf.printf "Bound: %s\n" (b.ToString())
    end;
    Printf.printf "\n"


// EXPECTED RESULT:
// Synthesis for R0
// Rank function: rowvec [1]
// Bound: rowvec [0]
//
// Synthesis for R1
// Rank function: rowvec [1;0]
// Bound: rowvec [1]
//
// Synthesis for R2
// Rank function: rowvec [1;-1]
// Bound: rowvec [1]
//
// Synthesis for R3
// Not well-founded

run "R0" R0 R0_expected
run "R1" R1 R1_expected
run "R2" R2 R2_expected
run "R3" R3 R3_expected
z3.Dispose()
