package checkingIF;
/*
 * Created on Jan 24, 2005
 * @version $Id: GetInfo.java,v 1.2 2005/03/21 09:36:37 lmartini Exp $
 */

/**
 * @author Luca Martini
 * 
 *  a collection of utility methods
 */

import embeddingInfo.AbstractSecLevelMethod;
import embeddingInfo.Constants;
import embeddingInfo.SecLevel;
import embeddingInfo.SecLevelField;
import embeddingInfo.SecLevelMethod;
import embeddingInfo.Util;
import exc.SecSpecificationError;
import java.util.HashMap;
import org.apache.bcel.Repository;
import org.apache.bcel.classfile.Attribute;
import org.apache.bcel.classfile.Code;
import org.apache.bcel.classfile.ConstantPool;
import org.apache.bcel.classfile.Field;
import org.apache.bcel.classfile.JavaClass;
import org.apache.bcel.classfile.Method;
import org.apache.bcel.generic.ConstantPoolGen;
import org.apache.bcel.generic.FieldInstruction;
import org.apache.bcel.generic.InvokeInstruction;
import org.apache.bcel.generic.Type;


public class GetInfo {
    // some caches to speed-up levels retrieval 
    private static HashMap fieldslevel = new HashMap(); 
    private static HashMap fieldsnamelevel = new HashMap(); 
    private static HashMap methsig = new HashMap();
    private static HashMap methodnamesig = new HashMap();
	
    public static SecLevel level(FieldInstruction fi, ConstantPoolGen cpg) {
	String classname = fi.getClassName(cpg);
	String fullfieldname = classname+"."+fi.getFieldName(cpg);
	Object ris = fieldsnamelevel.get(fullfieldname);
	if (ris != null) 
	    return (SecLevel) ris; 
	
	// Field Resolution to get the attributes 
	JavaClass clazz = Repository.lookupClass(classname);
	if (clazz == null) 
	    throw new SecSpecificationError("Coud not load class "+classname);
	
	Field f = (Field) Util.findFieldOrMethod(clazz.getFields(),fi.getFieldName(cpg),fi.getSignature(cpg));
	if (f==null) 
	    throw new SecSpecificationError("Coud not find field "+fullfieldname+".");
	Attribute[] aa = f.getAttributes();
	for (int i = 0; i < aa.length; i++) {
	    if (aa[i].getTag() == Constants.TAG_SECLEVELFIELD) {
		SecLevelField slf = (SecLevelField) aa[i];
		fieldsnamelevel.put(fullfieldname,slf.sl);
		return slf.sl;
	    }
	}
	
	// no attribute found, raise Exception
	throw new SecSpecificationError("Security Specification missing for field "+f.getClass()+"."+f.getName());
    }

    public static SecLevel level(Field f) throws Exception {
	Object ris = fieldslevel.get(f);
	if (ris != null) 
	    return (SecLevel) ris; 
	Attribute[] aa = f.getAttributes();
	for (int i = 0; i < aa.length; i++) {
	    if (aa[i].getTag() == Constants.TAG_SECLEVELFIELD) {
		SecLevelField slf = (SecLevelField) aa[i];
		fieldslevel.put(f,slf.sl);
		return slf.sl;
	    }
	}
	// no attribute found, raise Exception
	throw new Exception("Security Specification missing for field "+f.getClass()+"."+f.getName());
    }
    
    public static AbstractSecLevelMethod signature(InvokeInstruction ii, ConstantPoolGen cpg, SecLevel sl) {
	String classname = ii.getClassName(cpg);
	String fullmethodname = classname+"."+ii.getMethodName(cpg)+ii.getSignature(cpg);
	Object ris = methodnamesig.get(fullmethodname+sl);

	if (ris != null) 
	    return (AbstractSecLevelMethod) ris; 
	
	// Method Resolution to get the attributes 
	JavaClass clazz = Repository.lookupClass(classname);
	if (clazz == null) 
	    throw new SecSpecificationError("Coud not load class "+classname);
	
	Method m = (Method) Util.findFieldOrMethod(clazz.getMethods(),ii.getMethodName(cpg),ii.getSignature(cpg));
	if (m==null) 
	    throw new SecSpecificationError("Coud not find method "+fullmethodname+".");
	Attribute[] aa = m.getAttributes();
	for (int i = 0; i < aa.length; i++) {
	    if (aa[i].getTag() == Constants.TAG_SECLEVELMETHD) {
		AbstractSecLevelMethod slm = (AbstractSecLevelMethod) aa[i];
		if (slm.impl_par.equals(sl)) {
		    methodnamesig.put(fullmethodname+sl,slm);
		    return slm;
		}
	    }
	}
	
	// no attribute found, raise Exception
	throw new SecSpecificationError("Security Specification missing for method "+fullmethodname+ " and implicit parameter "+sl);
    }


    public static AbstractSecLevelMethod signature(Method m, SecLevel sl) {
	SigLevelPair pair = new SigLevelPair(m,sl);
	Object ris = methsig.get(pair);
	if (ris != null) 
	    return (AbstractSecLevelMethod) ris; 
	Attribute[] aa = m.getAttributes();
	//System.out.println("method "+m+ " with "+aa.length+ " attributes" );
	for (int i = 0; i < aa.length; i++) {
	    if (aa[i].getTag() == Constants.TAG_SECLEVELMETHD) {
		AbstractSecLevelMethod slm = (AbstractSecLevelMethod) aa[i];
		if (slm.impl_par.equals(sl)) {
		    methsig.put(pair,slm);
		    return slm;
		}
	    }
	}
	// no attribute found, raise Exception
	throw new SecSpecificationError("Security Specification missing for method "+m.getClass()+"."+m.getName()+ " and security level "+sl);
    }
    
    /**
     * The method <code>addStubSignature</code> adds stub signatures
     * in the hashmap of signature used in the verification for the
     * class passed as parameter.
     *
     * @param classname the nem of the class whose method are inserted in the hashmap
     * @param levelsStub a <code>SecLevel</code> array: for each
     * element of the array a stub signature is created with all level
     * bounded to this element.
     */
    public static void addStubSignature(String classname, SecLevel[] levelsStub){
	JavaClass clazz = Repository.lookupClass(classname);
	if (clazz == null) 
	    throw new SecSpecificationError("Coud not load class "+classname);
	Method[] methods = clazz.getMethods();
	ConstantPool cp = clazz.getConstantPool();
	for (int i = 0; i < methods.length; i++) {
	    Type[] parameters = methods[i].getArgumentTypes();
	    int nargs = parameters.length;
	    boolean isstatic = methods[i].isStatic();
	    nargs = isstatic?nargs:nargs+1;
	    for (int j = 0; j < levelsStub.length; j++) {
		AbstractSecLevelMethod slm = new SecLevelMethod((short)0,cp,(short)nargs);
		SecLevel stub = levelsStub[j];
		slm.return_value = (SecLevel) stub.clone();
		slm.effect = (SecLevel) stub.clone();
		slm.exceffect = (SecLevel) stub.clone();
		slm.impl_par = (SecLevel) stub.clone();
		for (int k = 0; k < nargs; k++) 
		    slm.registers[k] = (SecLevel)stub.clone();
		//  bitset, index name and other stuff not set for
		//  stub signatures
		methodnamesig.put(clazz.getClassName()+"."+methods[i].getName()+methods[i].getSignature()+stub, slm);
	    }
	}
    }

    public static void emptyCaches() {
        fieldslevel.clear();
	methsig.clear();
	fieldsnamelevel.clear();
	methodnamesig.clear();
    }
}   
class SigLevelPair{
    Method m;
    SecLevel sl;
    SigLevelPair (Method a, SecLevel s) {
        m = a;
	sl = s;
    }
}
