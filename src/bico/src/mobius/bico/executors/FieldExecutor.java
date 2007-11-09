package mobius.bico.executors;

import java.util.ArrayList;

import mobius.bico.Util;

import org.apache.bcel.classfile.Field;
import org.apache.bcel.classfile.JavaClass;
import org.apache.bcel.generic.ObjectType;
import org.apache.bcel.generic.Type;


/**
 * This class is used in the treatment of fields by bico.
 * 
 * @author J. Charles (julien.charles@inria.fr), 
 * P. Czarnik (czarnik@mimuw.edu.pl), 
 * L. Hubert (laurent.hubert@irisa.fr)
 */
class FieldExecutor extends ASignatureExecutor {
  
  /** determine the span of the 'reserved' fields names number default is 1. */
  private static final int RESERVED_FIELDS = 1;
  
  /** the currently treated JavaClass from which the fields are taken. */
  private JavaClass fJavaClass;
  
  
  
  
  
  /**
   * Create a field executor in the context of another
   * executor.
   * @param be the BasicExecutor to get the initialization from
   * @param jc the current class
   */
  public FieldExecutor(final ASignatureExecutor be, final JavaClass jc) {
    super(be);
    
    fJavaClass = jc;
  }
  
  /**
   * Fields handling.
   * @throws ClassNotFoundException if a class typing a field
   * cannot be resolved
   */
  public void start() throws ClassNotFoundException {
	//doImport();
    for (Field field : fJavaClass.getFields()) {
      doField(field);
      fOut.println();
    }
    
  }
  /**
   * probably should be @deprecated
   */
  private void doImport() {
	  ArrayList<String> modulesToImports = startModulesToBeImported();
	  for (String moduleToImport : modulesToImports) {
		  String signature = Util.classFormatName2Standard(moduleToImport); 
		  signature = Util.coqify(signature) + "_signature";
		  fOut.println(Constants.REQ_IMPORT + Constants.SPACE + signature   + ".v.");
		  fOut.println(Constants.IMPORT + Constants.SPACE + signature+ ".");
	  }
	
  }

/**
   * Enumerates in a Coq friendly form all the fields of the class.
   */
  public void doEnumeration() {
    // fields
    final Field[] ifield = fJavaClass.getFields();
    if (ifield.length == 0) {
      fOut.println(fImplemSpecif.getNoFields());
    } 
    else {
      String str2 = "(";
      for (int i = 0; i < ifield.length - 1; i++) {
        str2 += fImplemSpecif.fieldsCons(Util.coqify(ifield[i].getName()) + "Field");
      }
      str2 += fImplemSpecif.fieldsEnd(Util.coqify(ifield[ifield.length - 1].getName()) + 
                                      "Field");
      str2 += ")";
      fOut.println(str2);
    }
  }

  /**
   * Collects the modules  which contain the description of the field type
   * to be imported in the current module
   * 
   * @throws ClassNotFoundException if a class typing a field
   * cannot be resolved
   */
  public ArrayList<String> startModulesToBeImported() {
	  /*the list of modules to be imported in the current module. 
	   *  For instance, the module which describes the type of the field 
	   *  must be imported in the current module:
	   *  
	   *  Require Import D_type.v
	   *  
	   *  Field c := (Name, D)
	   *  
	   */
	ArrayList<String> modulesToBeImported = new ArrayList<String>();
    for (Field field : fJavaClass.getFields()) {
      Type type = field.getType();
   	  if (type  instanceof ObjectType) {
   		  String  signature = ((ObjectType)type).getSignature();
   		  modulesToBeImported.add(signature);  
   	  }
    }
    return modulesToBeImported;
  }
  
  
	
  
  /**
   * Definition of the field signature.
   * @param field the current field
   * @param fieldIdx the index which represents the name of the field
   * @throws ClassNotFoundException if the field is of a class type which
   * cannot be resolved 
   */
  private void doFieldSignature(final Field field, 
                                final int fieldIdx) throws ClassNotFoundException {

    String strf = "Definition " + Util.coqify(field.getName()) +
           "ShortFieldSignature : ShortFieldSignature := FIELDSIGNATURE.Build_t ";
    fOutSig.println(strf);
    fOutSig.incTab();
    // !!! here positives
    
    strf = "(" + fieldIdx + "%positive)";
    fOutSig.println(strf);
    
    // !!! here will be conversion
    strf = Util.convertType(field.getType(), fRepos);
    fOutSig.println(strf);
    fOutSig.decTab();
    fOutSig.println(".\n");
    strf = "Definition " + Util.coqify(field.getName()) +
           "FieldSignature : FieldSignature := (className, " + 
           Util.coqify(field.getName()) + "ShortFieldSignature).\n";
    fOutSig.println(strf);
  }

  /**
   * Proper definition of the field for Coq.
   * @param field the field to compute
   */
  private void doField(final Field field) {
    
    String strf = "Definition " + Util.coqify(field.getName()) +
           "Field : Field := FIELD.Build_t";
    fOut.println(strf);
    fOut.incTab();
    strf = Util.coqify(field.getName()) + "ShortFieldSignature";
    fOut.println(strf);
    
    fOut.println("" + field.isFinal());
    fOut.println("" + field.isStatic());
    String visibility = "Package";
    if (field.isPrivate()) {
      visibility = "Private";
    } 
    else if (field.isProtected()) {
      visibility = "Protected";
    }
    if (field.isPublic()) {
      visibility = "Public";
    }
    fOut.println(visibility);
    // FIXME current solution
    strf = "FIELD.UNDEF";
    fOut.println(strf);
    fOut.decTab();
    fOut.println(".");
  }

  /**
   * Trigger the writing of the signature of the fields.
   * @throws ClassNotFoundException if there is a type which cannot be
   * properly resolved.
   */
  @Override
  public void doSignature() throws ClassNotFoundException {
    int fieldIdx = RESERVED_FIELDS;
    
    for (Field field : fJavaClass.getFields()) {
      fieldIdx++;
      fDico.addField(field.getName(), 
                     fDico.getCoqPackageName(fJavaClass), 
                     fDico.getCoqClassName(fJavaClass), 
                     fieldIdx);
      doFieldSignature(field, fieldIdx);
    }

    
  }
}
