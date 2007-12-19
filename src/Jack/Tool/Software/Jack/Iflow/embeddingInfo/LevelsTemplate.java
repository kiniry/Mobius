package embeddingInfo;
/*
 * Created on Jan 12, 2005
 * @version $Revision: 1.4 $ $Date: 2005/03/24 10:28:30 $
 */

/**
 * @author Luca Martini
 *
 */
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.Iterator;
import java.util.Set;
import java.util.SortedSet;
import java.util.TreeSet;
import org.apache.bcel.Repository;
import org.apache.bcel.classfile.ConstantPool;
import org.apache.bcel.classfile.Field;
import org.apache.bcel.classfile.JavaClass;
import org.apache.bcel.classfile.LocalVariable;
import org.apache.bcel.classfile.LocalVariableTable;
import org.apache.bcel.classfile.Method;
import org.apache.bcel.classfile.Utility;
import org.apache.bcel.generic.ArrayType;
import org.apache.bcel.generic.ConstantPoolGen;
import org.apache.bcel.generic.InstructionHandle;
import org.apache.bcel.generic.MethodGen;
import org.apache.bcel.generic.Type;
import org.apache.bcel.util.InstructionFinder;

public class LevelsTemplate {
    private FileWriter fw;

    private void openOutputFile() {
	File levtemplateFile = new File("out.info");
	try {
	    fw = new FileWriter(levtemplateFile);
	} catch (IOException e) {
	    System.err.println("Error opening file out.info. Exiting...");
	    System.exit(0);
	}
    }
    
    private void classTemplate(String classname) {
	JavaClass  clazz = Repository.lookupClass(classname);
	if (clazz == null) {
	    System.err.println("Class "+classname+" not found in your classpath.\nExiting...");
	    System.exit(0);
	}
	// parsing the class file
	Method[] methods = clazz.getMethods();
	Field[] fields = clazz.getFields();
	ConstantPool cp = clazz.getConstantPool();
	ConstantPoolGen cpg = new ConstantPoolGen(cp);
	LocalVariableTable lcvt;
	try { 
	    // @startclass block
	    fw.write(TagEnum.START_CLASS+" "+classname+"\n"); 
	    // fields
	    for (int i=0; i<fields.length; i++) {
		fw.write("\t"+TagEnum.FIELD+" L "+fields[i].getName()+ " " +fields[i].getSignature()+"\n");
	    }
	    // methods
	    for (int i=0; i<methods.length; i++) {
		Method meth=methods[i];
		MethodGen mg= new MethodGen(meth,clazz.getClassName(),cpg);
		if (!(meth.isNative() || meth.isAbstract())) {
		    String methodID = meth.getName()+ " "+methods[i].getSignature();
		    // add simply provable assumptions
		    if (!(mg.isStatic())) {
			Set safeFieldAccesses = localFieldAccess(mg);
			if (!(safeFieldAccesses.isEmpty())) {
			    String s = "\n\t"+TagEnum.EXCSAFE+ " java.lang.NullPointerException "+ methodID;
			    for (Iterator k = safeFieldAccesses.iterator(); k.hasNext();) {
				s+=" "+((InstructionHandle) k.next()).getPosition();
			    }
			    fw.write(s+"\n");
			    
			}
			    
		    }

		    // calculating the number of registers in the frame
		    int maxlocals = meth.getCode().getMaxLocals();
		    // method attribute...
		    fw.write("\t"+TagEnum.START_METHOD+ " " + methodID +"\n");
		    fw.write("\t"+TagEnum.COMMENT+ " max locals "+maxlocals+"\n");
		    fw.write("\t\t"+TagEnum.HEAP_EFFECT+" L\n");
		    fw.write("\t\t"+TagEnum.EXC_EFFECT+" L\n");
		    fw.write("\t\t"+TagEnum.REGISTER+" 0 L\n");
		    // trying to see if the LocalVariableTabel debug attribute exists
		    try {
			lcvt = meth.getCode().getLocalVariableTable();
		    } catch (NullPointerException e) {
			lcvt = null;
		    }
			
		    if (lcvt != null) {
			for (int j = 1; j < maxlocals; j++) {
			    /* since more than one entry in the
			     * table may refer to the same index,
			     * we take the first one. If a
			     * register is used for more than a
			     * variable the comment may be
			     * misleading */ 
			    LocalVariable lv = lcvt.getLocalVariable(j);
			    if (lv != null) {
				fw.write("\t"+TagEnum.COMMENT+ " "+Utility.
					 signatureToString(lv.getSignature())+" "+
					 lv.getName()+"\n");
				String s = "\t\t"+TagEnum.REGISTER+" "+(j)+" L";
				if (lv.getSignature().startsWith("[")) {
				    s+="[]\n";
				} else 
				    s+="\n";
				fw.write(s);
			    }				
			}
		    } else {
			/* we have information only on the
			 * parameters */
			Type[] params = meth.getArgumentTypes(); 
			for (int j = 0; j < params.length; j++) {
			    String s = "\t\t"+TagEnum.REGISTER+" "+(j+1)+" L";
			    if (params[j] instanceof ArrayType) 
				s+="[]\n";
			    else 
				s+="\n"; 
			    fw.write(s); 
			}
		    }
			
		    // method attribute ...continue
		    fw.write("\t\t"+TagEnum.IMPLICIT+" L\n");
		    if (meth.getReturnType()!=Type.VOID)
			fw.write("\t\t"+TagEnum.RETURN+" L\n");
		    fw.write("\t"+TagEnum.END_METHOD+"\n"); 
		}		    
	    }
	    // @endclass block
	    fw.write(TagEnum.END_CLASS+"\n");
	    fw.flush();
	} catch (IOException e) {
	    System.err.println("Error writing on file out.info. Exiting...");
	    System.exit(0);
	}
    }
    
    public static void main(String[] args) {
	LevelsTemplate lt = new LevelsTemplate();
	lt.openOutputFile();
 
	// parse command line arguments 
	for(int k=0; k < args.length; k++) {
      	    if (args[k].endsWith(".class")){
		int dotclasspos = args[k].lastIndexOf(".class");
		if (dotclasspos != -1) args[k] = args[k].substring(0,dotclasspos);
	    }
	    args[k] = args[k].replace('/', '.');
	    
	    System.err.println("Analyzing class "+args[k]);
	    lt.classTemplate(args[k]);	    
	}        	
    }

    /**
     *  This function search into the body of the method passed as
     *  parameter accesses to the local fields. It returns a set of
     *  <code>InstructionHandle</code> correpsonding to local
     *  putfield/getfield. These instructions will not raise any
     *  NullPointerException.
     *
     */
    private static Set localFieldAccess(MethodGen mg) {
	SortedSet result = new TreeSet(new IHComparator());
	InstructionFinder finder = new InstructionFinder(mg.getInstructionList());
	for (Iterator k = finder.search("ALOAD_0 (GETFIELD | PUTFIELD)"); k.hasNext();) {
	    InstructionHandle[] match = (InstructionHandle[]) k.next();
	    result.add(match[1]);
	}
	return result;	
    }

}
