/*
  Copyright (c) 1994-1996 The Regents of the Univ. of California.
  All rights reserved. 

  Permission is hereby granted, without written agreement and without license
  or royalty fees, to use, copy, modify, and distribute this software and its
  documentation for any purpose, provided that the above copyright notice and
  the following two paragraphs appear in all copies of this software.

  IN NO EVENT SHALL THE UNIVERSITY OF CALIFORNIA BE LIABLE TO ANY PARTY FOR
  DIRECT, INDIRECT, SPECIAL, INCIDENTAL, OR CONSEQUENTIAL DAMAGES ARISING OUT
  OF THE USE OF THIS SOFTWARE AND ITS DOCUMENTATION, EVEN IF THE UNIVERSITY OF
  CALIFORNIA HAS BEEN ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

  THE UNIVERSITY OF CALIFORNIA SPECIFICALLY DISCLAIMS ANY WARRANTIES,
  INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND
  FITNESS FOR A PARTICULAR PURPOSE.  THE SOFTWARE PROVIDED HEREUNDER IS ON AN
  "AS IS" BASIS, AND THE UNIVERSITY OF CALIFORNIA HAS NO OBLIGATION TO PROVIDE
  MAINTENANCE, SUPPORT, UPDATES, ENHANCEMENTS, OR MODIFICATIONS.
*/

package mocha.wrappers.jbdd; 

import java.util.BitSet;

public class jbdd {
  // the class member
  protected long jbdd;
  // the static functions. These typically take two or more symmetric
  // arguments so it is better to define them static. Use them as follows:
  // jbdd bdd3 = jbdd.jbdd_and(bdd1, bdd2) 
  public static	native jbdd jbdd_and(jbdd f, jbdd g, boolean f_phase,
                                       boolean g_phase);
  public static	native jbdd jbdd_and_smooth(jbdd f, jbdd g, jbdd[]
                                              smoothing_vars);
  public static native jbdd jbdd_clipping_and_smooth(jbdd f, jbdd g,
                                                       jbdd[]
                                                       smoothing_vars, int
                                                       f_phase, int g_phase);
  public static	native jbdd jbdd_xor_smooth(jbdd f, jbdd g, jbdd[]
                                              smoothing_vars);
  public static native jbdd jbdd_between(jbdd f_min, jbdd f_max);
  public static native jbdd jbdd_compose(jbdd f, jbdd v, jbdd g);
  public static native jbdd jbdd_ite(jbdd i, jbdd t, jbdd e, boolean
                                       i_phase, boolean t_phase, boolean
                                       e_phase);
  public static native jbdd jbdd_or(jbdd f, jbdd g, boolean f_phase,
                                      boolean g_phase);
  public static native jbdd jbdd_xnor (jbdd f, jbdd g);
  public static native jbdd jbdd_xor(jbdd f, jbdd g);
  public static native int jbdd_apa_compare_ratios(int a, jbdd f, jbdd g,
                                                   int j, int k);
  public static native int jbdd_estimate_cofactor(jbdd f, jbdd g, int n);
  // and these are the nonstatic functions
  public native jbdd jbdd_dup();
  public native	void jbdd_free();
  public native	jbdd jbdd_cofactor(jbdd g);
  public native	jbdd jbdd_var_cofactor(jbdd g);
  public native	jbdd jbdd_consensus(jbdd [] quantifying_vars);
  public native	jbdd jbdd_cproject(jbdd [] var_array);
  public native	jbdd jbdd_else();
  public native	jbdd jbdd_minimize(jbdd c);
  public native	jbdd jbdd_compact(jbdd c);
  public native	jbdd jbdd_squeeze(jbdd c); // not doc'd
  public native	jbdd jbdd_not();
  public native	jbdd jbdd_smooth (jbdd[] smoothing_vars);
  public native	jbdd jbdd_substitute(jbdd[] old_array, jbdd[] new_array);
  public native jbdd jbdd_then();
  public native	jbdd jbdd_top_var ();
  public native	jbdd jbdd_shortest_path(int [] weight, int [] support, int
                                          [] length); // check -- this is
  // trouble
  public native	boolean jbddest_unate(int var_id, int phase); // shouldn't
  // this be boolean?
  public native	jbdd[] jbdd_find_essential();
  public native	double[] jbdd_cof_minterm();
  public native	boolean jbdd_var_is_dependent(jbdd f);
  public native	boolean jbdd_equal(jbdd g);
  public native	jbdd jbdd_intersects(jbdd g); 
  public native	boolean jbdd_is_tautology (boolean phase);
  public native	boolean jbdd_leq(jbdd g, boolean f_phase, boolean g_phase);
  public native	double jbdd_count_onset(jbdd[] var_array);
  public native	double jbdd_correlation(jbdd g);
  public native	int jbdd_get_free ();
  public native	long jbdd_get_manager();
  public native	BitSet jbdd_get_support ();
  public native	void jbdd_print();
  public native	int jbdd_print_minterm();
  public native	int jbdd_size();
  public native	boolean jbdd_is_cube();
  public native	int jbdd_top_var_id();
  public jbdd(){
  }
  protected native void jbdd_finalize();

  protected void finalize () {
	jbdd_finalize();
  }
  static {
    System.loadLibrary("glu");
    System.loadLibrary("cu");
    System.loadLibrary("jbdd");
  }


}
