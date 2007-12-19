package embeddingInfo;
/*
 * Created on Jan 18, 2005
 * @version $Id: Util.java,v 1.2 2005/02/02 14:40:11 lmartini Exp $
 */

/**
 * @author Luca Martini
 *
 */


import org.apache.bcel.classfile.JavaClass;
import org.apache.bcel.classfile.Field;
import org.apache.bcel.classfile.Method;
import org.apache.bcel.classfile.FieldOrMethod;
import org.apache.bcel.classfile.Attribute;


import java.util.StringTokenizer;

public class Util {
    
    public static String[] tok2array(StringTokenizer s) {
	String[] sa = new String[s.countTokens()];
	for (int j=0; j<sa.length;j++) 
	    sa[j] = s.nextToken();
	return sa;
    }

// can be split in two overrided methods for performance
    public static FieldOrMethod findFieldOrMethod(FieldOrMethod[] fs, String name, String sig) {
	if (fs.length>0) {
	    for (int i=0; i< fs.length;i++) {
		if (fs[i].getName().equals(name) &&
		     fs[i].getSignature().equals(sig))
		    return fs[i];
	    }
	}
	return null;
    }

    public static void addAttribute(FieldOrMethod fm, Attribute a) {
	Attribute[] oldattrs = fm.getAttributes();
	Attribute[] newattrs = new Attribute[oldattrs.length+1];
	newattrs[oldattrs.length] = a;
	System.arraycopy(oldattrs, 0, newattrs, 0, oldattrs.length);
	fm.setAttributes(newattrs);
    }			
}