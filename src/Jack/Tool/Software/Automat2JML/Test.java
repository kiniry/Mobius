/*
 * Created on Mar 14, 2005
 *
 * TODO To change the template for this generated file go to
 * Window - Preferences - Java - Code Style - Code Templates
 */

/**
 * @author tdupont
 *
 * TODO To change the template for this generated type comment go to
 * Window - Preferences - Java - Code Style - Code Templates
 */


import java.io.File;
import java.util.LinkedList;


public class Test {

	public Synthetiser synthetiser;
	
	Test(String document){
		synthetiser = new Synthetiser(document);
	}
	
	public static void main(String[] args) {
	
		LinkedList mpList;
		MethodProperty mp;
		
		if (args.length != 1) {
            System.err.println("give 1 parameters as input");
            System.err.println("read input" + args[0]);
            System.exit(1);
        }
		
		File outfile;
		outfile = new File(args[0]);
		if (! outfile.exists()) { return ;}
		System.err.println("Building Data Struct");
		Test Appli = new Test(args[0]);
		if (Appli.isSynthetizable() == false) {	
			System.err.println("Building property 1 failed");	
			System.exit(0);
		}
		
		System.err.println("Begin Synthesis");
		
		Appli.synthetiser.synthesize("/user/tdupont/home/workspace/JavaSynthesis/JMLsyn/",
									 "essaiGen",
									 "AutomataProp" );

		/*
		System.err.println("\nMethod Properties are: ");
		for(int i=0 ; i<mpList.size(); i++){
			System.err.println((MethodProperty)mpList.get(i));
		}*/
		
		System.err.println("Synthesis done");
		
	}

	
	
	private void displayTree(){synthetiser.displayXMLTree();	}
	private boolean isSynthetizable(){ return synthetiser.isSynthesizable();}
	private void displayGlobalVariables(){ 
		System.out.println(synthetiser.getGlobalVariables());}





}
