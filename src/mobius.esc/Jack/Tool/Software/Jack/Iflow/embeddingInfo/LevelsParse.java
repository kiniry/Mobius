package embeddingInfo;
/*
 * Created on Jan 14, 2005
 * @version $Id: LevelsParse.java,v 1.3 2005/03/21 09:36:38 lmartini Exp $
 */

/**
 * @author Luca Martini
 * 
 */

import java.io.BufferedReader;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.util.StringTokenizer;
import org.apache.bcel.Repository;
import org.apache.bcel.classfile.Attribute;
import org.apache.bcel.classfile.ConstantPool;
import org.apache.bcel.classfile.Field;
import org.apache.bcel.classfile.FieldOrMethod;
import org.apache.bcel.classfile.JavaClass;
import org.apache.bcel.classfile.Method;
import org.apache.bcel.generic.ConstantPoolGen;
import org.apache.bcel.generic.Type;

public class LevelsParse {
    private String filetoparse;
    private boolean debug = false;
    public static byte AW_CLASS = (byte) 0x00;
    public static byte IN_CLASS = (byte) 0x01;
    public static byte IN_METHOD = (byte) 0x02;
    public static char DIRSEP = System.getProperty("file.separator").charAt(0);
    
    // Temporary variables used in the parsing
    private byte curr_state = AW_CLASS;
    private JavaClass curr_class = null;
    private Method curr_method = null;
    private ConstantPool curr_cp = null;
    private ConstantPoolGen cpg;
    // the index of the UTF8 constants SecLevelField, SecLevelMethod, and ExceptionSafe
    private short slf_index=0, slm_index=0, es_index=0;


    /** 
     * Contains the last parsed tag.
     *
     */
    private TagEnum te;
        
    public LevelsParse (String filetoparse) {
	this.filetoparse = filetoparse;
    }
    
    private static void usage() {
	System.out.println("LevelParse: a little utility to store security levels information into Java class file.");
	System.out.println("$Id: LevelsParse.java,v 1.3 2005/03/21 09:36:38 lmartini Exp $");
	System.out.println("usage: java LevelParse [-v] file_to_parse");
	System.out.println("       where the -v switch adds verbose information to standard output");
	System.out.println("       and file_to_parse is the file which LevelParse extracts the information from.");
    }
    
    private void log(String s) {
	if (debug) 
	    System.out.println(s);
    }
	

    public static void main(String[] args) {

	LevelsParse lp;
	
	switch (args.length) {
	case 1:
	    lp = new LevelsParse(args[0]);
	    break;
	case 2:
	    if (args[0].equals("-v")) {
		lp = new LevelsParse(args[1]);
		lp.debug = true;
		break;
	    }
	default:
	    usage();
	    return;
	}
	
	BufferedReader in;
	try {
	    in = new BufferedReader(new FileReader(lp.filetoparse));
	    lp.parse(in);
	} catch (FileNotFoundException e) {
	    System.err.println("File "+lp.filetoparse+" not found.\nExiting...");
	    return;
	} // end of try-catch
	lp.parse(in);
    }
    
    

    private void parse(BufferedReader in){
	StringTokenizer stok;
	String s1, s2 = new String();
	String[] atok;
	SecLevelMethod curr_attr = null;
	short curr_max_locals = 0;
	
	try {
	    s1 = in.readLine();	
	    while (s1 != null) {
		log("[Parsing]"+s1);
		stok = new StringTokenizer(s1);
		atok = Util.tok2array(stok);
		if (atok.length>0) {
		    te = TagEnum.search(atok[0]);
		    if (te == null )
			throw new ParseError("Parse error. Tag unknown");
		    switch (te.getValue()) {
		    
		    case 0: // START_CLASS
			log("[START_CLASS]");
			checkstate(AW_CLASS);
			curr_class = Repository.lookupClass(atok[1]);
			if (curr_class == null) 
			    throw new ParseError("Class "+atok[1]+" not found in your classpath.");
		       
			// Insertion of the necessary UTF8constants
			// into the constant pool of the class
			cpg = new ConstantPoolGen(curr_class.getConstantPool());
			slf_index = (short) cpg.addUtf8("SecLevelField");
			slm_index = (short) cpg.addUtf8("SecLevelMethod");
			es_index = (short) cpg.addUtf8("ExceptionSafe");
			// updating the constant pool
			curr_cp = cpg.getFinalConstantPool();

			log("slf_index="+ slf_index);
			log("slm_index="+ slm_index);
			log("es_index="+es_index);
			curr_state = IN_CLASS;
			break;
		    
		    case 1:// END_CLASS
			log("[END_CLASS]");
			checkstate(IN_CLASS);
			curr_state = AW_CLASS;
			// setting the final constant pool
			curr_class.setConstantPool(curr_cp);
			// preparing the correct filename
			String sdump = new String(curr_class.getClassName());
			sdump = "out"+DIRSEP+sdump.replace('.', DIRSEP)+".class"; 
			curr_class.dump(sdump);
			curr_class = null;
			break;
			
		    case 2: // START_METHOD
			log("[START_METHOD]");
			checkstate(IN_CLASS);
			findAndSetMethod(atok[1],atok[2]);
			curr_max_locals = (short) curr_method.getCode().getMaxLocals();
			log("curr_max_locals="+curr_max_locals);
			curr_attr = new SecLevelMethod(slm_index, curr_cp, curr_max_locals);
			curr_state = IN_METHOD;
			break;

		    case 3: // END_METHOD
			log("[END_METHOD]");
			checkstate(IN_METHOD);
			Util.addAttribute(curr_method,curr_attr);
			curr_method = null;
			curr_attr = null;
			curr_state = IN_CLASS;
			break;
			
		    case 4: // comment
			log("[COMMENT]");
			//ignore
			break;

		    case 5: // FIELD
			log("[FIELD]");
			checkstate(IN_CLASS);
			FieldOrMethod f = Util.findFieldOrMethod(curr_class.getFields(), atok[2], atok[3]);
			if (f==null) 
			    throw new ParseError("Field " + atok[2] + "not found"); 
			Attribute a = new SecLevelField(slf_index,curr_cp,levelString2byte(atok[1]));
			Util.addAttribute(f,a);
			break;
			
		    case 6: // HEAP_EFFECT
			log("[HEAP]");
			checkstate(IN_METHOD);
			curr_attr.effect = new HL(atok[1]); 
			break;
		    
		    case 7: // EXC_EFFECT
			log("[EXC_EFFECT]");
			checkstate(IN_METHOD);
			curr_attr.exceffect = new HL(atok[1]); 
			break;

		    case 8: // REGISTER 
			log("[REGISTER]");
			checkstate(IN_METHOD);
			short nreg = Short.parseShort(atok[1]);
			if ((nreg < 0) || (nreg > curr_max_locals-1)) 
			    throw new ParseError("Register number invalid.");
			// search for []
			int brackpos=atok[2].lastIndexOf("[]");
			if (brackpos != -1) {
			    // marking the register as containing an array reference
			    curr_attr.b.set(nreg);
			    atok[2]=atok[2].substring(0,brackpos);
			}
			// note that the level of the array is not
			// important because is always equal to the
			// normal level. And the isArray status is
			// saved in the BitSet b
			curr_attr.registers[nreg] = new HL(atok[2]);
			break;
		    
		    case 9: // RETURN
			log("[RETURN]");
			checkstate(IN_METHOD);
			if (curr_method.getReturnType() == Type.VOID) 
			    log("[Warning] Method "+ curr_method.getName() + " is void. Return level specification will be ignored");
			curr_attr.return_value = new HL(atok[1]); 
			break;
						
		    case 10: // IMPLICIT
			log("[IMPLICIT]");
			checkstate(IN_METHOD);
			curr_attr.impl_par = new HL(atok[1]); 
			break;
		
		    case 11: //EXCSAFE
			parseExceptionSafe(atok);
			break;

		    default:
			throw new ParseError("Never reached :-).");
		    } // end of switch (te.getValue())
		}
		s1=in.readLine();
	    }		
	} catch (IOException e) {
	    System.err.println("IOException.\nExiting...");
	    System.exit(0);
	} catch (ParseError e) {
	    System.err.println(e+"\nExiting...");
	    System.exit(0);
	} // end of catch
	
    }    


    private byte levelString2byte(String s) throws ParseError {
	log("[string2level]" + s );
	if (s.equals("L")) 
	    return 0x00;
	else if (s.equals("H")) 
	    return 0x01;
	else throw new ParseError("Error in parsing the sec level");
    }

    private void checkstate(byte state) throws ParseError {
	if (curr_state != state) {
	    throw new ParseError("Parse Error: Tag "+te+" unexpected.");
	}
    }
    
    private void findAndSetMethod(String s1, String s2) throws ParseError {
	curr_method = (Method) Util.findFieldOrMethod(curr_class.getMethods(), s1, s2);
	if (curr_method == null) 
	    throw new ParseError("Method " + s1 + " " + s2 + " not found in class " + curr_class.getClassName());
    }

    private final void parseExceptionSafe(String[] line) throws ParseError {
	log("[EXCEPTIONSAFE]");
	checkstate(IN_CLASS);
	findAndSetMethod(line[2],line[3]); // set curr_method
	short excNameIndex = (short) cpg.addClass(line[1]);
	// updating the constant pool
	curr_cp = cpg.getFinalConstantPool();
	ExceptionSafe newattr = new ExceptionSafe(es_index, curr_cp, excNameIndex);
	for (int i = 4; i < line.length; i++) {
	    // TODO: check if the listed pcs are inside the current
	    // method
	    newattr.addPc(Integer.parseInt(line[i]));
	}
	Util.addAttribute(curr_method,newattr);
	curr_method = null;			
    }    

    private class ParseError extends RuntimeException {
	ParseError(String msg) {
	    super(msg);
	}
    }
}

    

