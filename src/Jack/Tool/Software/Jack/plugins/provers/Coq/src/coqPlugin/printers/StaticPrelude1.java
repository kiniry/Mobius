/*
 * Created on Feb 23, 2005
 */
package coqPlugin.printers;

import java.io.File;
import java.io.PrintStream;

import jml2b.IJml2bConfiguration;

/**
 * @author jcharles
 *
 */
public class StaticPrelude1 extends Printer {
	// On definit les types primitifs (calques sur Z)
	private final static String[] typesmall = {"byte","short","int", "char", "long"};
	private final static String[] type = {"t_byte","t_short","t_int", "t_char", "t_long"};
	
	/** the file containing the module: jack_arith */
	public static final String fileName ="jack_arith";
	
	/** the module contained in the file: JackArith */
	public static final String moduleName ="JackArith";
	
	public StaticPrelude1(File output_directory, IJml2bConfiguration config) {
		super(output_directory, fileName + ".v");
		startWriting(config);
	}
	protected void writeToFile(PrintStream stream, IJml2bConfiguration config){
		stream.println("Require Import Bool.");
		stream.println("Require Import ZArith.");
		stream.println("Require Import Zdiv.");
		stream.println("Open Scope Z_scope.\n");
		
		
		
		stream.println("Module JackArith.");
		for (int i = 0; i < type.length ; i++){
			stream.println("Definition " + type[i] + " := Z.");
		}		
		stream.println("Variable t_float : Set.\n");
		defineArithmetics(stream);
		stream.println("End JackArith.");
		
	}
	/**
	 * Prints the arithmetic operators definition
	 **/
	private void defineArithmetics(PrintStream stream) {
		stream.println("");
		stream.println("(* Primitive Type Definition:*)");
		//stream.println("Variable dom: (a,b:Set) (a->b)->a->Prop.\n");
		// On definit les variables
		String [][] vars = {{"c_minbyte", "" + Byte.MIN_VALUE}, {"c_maxbyte", "" + Byte.MAX_VALUE},
							{ "c_minshort", "" + Short.MIN_VALUE},{"c_maxshort", "" + Short.MAX_VALUE},
							{"c_minint", "" + Integer.MIN_VALUE}, { "c_maxint", "" + Integer.MAX_VALUE}, 
							{"c_minchar", "" + "0"}, {"c_maxchar", "65535"},
							{"c_minlong", ""+ Long.MIN_VALUE}, {"c_maxlong", "" + Long.MAX_VALUE}};
		for (int i=0; i < vars.length; i++){
			stream.println("Definition " + vars[i][0] + " := " + vars [i][1] + ".");	
		}



		for (int i = 0; i < type.length; i++) {
			stream.println("Definition " + type[i] + "Dom (n:Z): Prop" + 
					" := c_min" + typesmall[i] + " <= n /\\ n <= c_max" + typesmall[i] + ".");
		}
		
	/*	
		stream.println(
			"Definition t_intDom := {n:Z | (Zle c_minint n) & (Zle n c_maxint)}.");
		stream.println(
			"Definition t_shortDom := { n:Z | (Zle c_minshort n) & (Zle n c_maxshort)}.");
		stream.println(
			"Definition t_byteDom := {n:Z | (Zle c_minbyte n) & (Zle n c_maxbyte)}.");
		stream.println(
			"Definition t_char_dom := {n:Z | (Zle c_minchar n) & (Zle n c_maxchar)}.");
		stream.println(
			"Definition t_long_dom := {n:Z | (Zle c_minlong n) & (Zle n c_maxlong)}.");
*/

		stream.println("Variable F0 : t_float.");
		stream.println("Variable Fle : t_float -> t_float -> Prop.\n"); 
		stream.println("");


		
		stream.println("");
		stream.println("");
		stream.println("(* Arithmetic Operators *)");
		String [][] ops = {{"j_add", "Zplus", "+" }, {"j_sub","Zminus", "-"},
						   {"j_mul", "Zmult", "*"},  {"j_div", "Zdiv", "/"},
						   {"j_rem", "Zmod"}};
		for (int i = 0; i < ops.length; i++) {
			stream.println("Definition " + ops[i][0] + ": t_int -> t_int -> t_int := " +
					ops[i][1] + ".");
			if (ops[i].length == 3)
				stream.println("Infix \""+ ops[i][2] + "\" := " + ops[i][0] +": J_Scope.");
		}

		

		String [][] oops = {{"j_le", "Zle", "<=" }, {"j_gt","Zgt", ">"},
				   			{"j_lt", "Zlt", "<"},  {"j_ge", "Zge", ">="}};
		for (int i = 0; i < oops.length; i++) {
			stream.println("Definition " + oops[i][0] + ": t_int -> t_int -> Prop := " +
			oops[i][1] + ".");
			if (oops[i].length == 3)
				stream.println("Infix \""+ oops[i][2] + "\" := " + oops[i][0] +": J_Scope.");
		}	
		
		
		stream.println("Definition j_neg : t_int -> t_int := Zopp.");

		stream.println("Variable j_shl : t_int -> t_int -> t_int.");

		stream.println("Variable j_shr : t_int -> t_int -> t_int.");


		stream.println("Variable j_ushr : t_int -> t_int -> t_int.");

		stream.println("Variable j_and : t_int -> t_int -> t_int.");

		stream.println("Variable j_or : t_int -> t_int -> t_int.");

		stream.println("Variable j_xor : t_int -> t_int -> t_int.");

		
		
		// Les conversions arithmetiques
		stream.println("");
		stream.println("(* Dummy Arithmetic Conversions *)");
		stream.println("Definition j_convert := fun (min max:Z) =>\n" + 
					   "   let range :=  ((- min) + max ) in\n" +
					   "       fun (a:Z) => \n"+
					   "          let n := (if (Zle_bool 0 a) then a\n" +
					   "                    else  (a + ((((- a) / range) + 1) * range))) in\n" +
					   "             if (Zle_bool (n mod range) max) then\n" +
					   "                (n mod range)\n" + 
					   "             else ((n mod range) - range).");
		String [] typesSmaller = {"char", "byte", "short"};
		for (int i = 0; i < typesSmaller.length; i++) {
			String t = typesSmaller[i];
			stream.println("Definition j_int2" + t + " : t_int -> t_" + t +" := " +
									"j_convert c_min" + t + " c_max" + t + ".");
		}
		stream.println("");
		// seems ring doesn't work this way anymore
//		stream.println("Add Ring t_int j_add j_mul 1%Z 0%Z j_neg Zeq ZTheory\n" +
//						"[ Zpos Zneg 0%Z xO xI 1%positive ].\n");
		
		
		//TODO: Delete the following lines...
		//stream.println("Variable j_int2char : t_int -> t_char.");
		//stream.println(
		//	"(* Definition j_int2charRan : Z -> Prop := "
		//		+ "[n:Z] (t_char (j_int2char n)).*)");

		//stream.println("Definition j_int2byte : t_int -> t_byte := j_convert c_minbyte c_maxbyte.");
		//stream.println(
		//	"(* Definition j_int2byteRan : Z -> Prop := "
		//		+ "[n:Z] (t_byte (j_int2byte n)).*)");
		
		//stream.println("Variable j_int2short : t_int -> t_short.");
		//stream.println(
		//	"(* Definition j_int2shortRan : Z -> Prop := "
		//		+ "[n:Z] (t_short (j_int2short n)). *)");

		/* stream.println("Axiom j_int2byteAx : ");
		stream.println("   forall n:t_int,");
		stream.println("         ((Zle 0 n) ->");
		stream.println("            ((Zle (Zmod n 256) 127)");
		stream.println("                 -> ((j_int2byte n) = (Zmod n 256)))");
		stream.println("         /\\ ((not (Zle (Zmod n 256) 127))");
		stream.println("                  -> ((j_int2byte n) = (Zminus (Zmod n 256) 256))))");
		stream.println("   /\\   ((not (Zle 0 n))");
		stream.println("                  -> ((j_int2byte n) = (j_int2byte "
				+ "(Zplus n (Zmult (Zplus (Zdiv (-n) 256) 1) 256)))))."); */

	}
	public boolean mustRewrite() {
		return true;
	}
}
