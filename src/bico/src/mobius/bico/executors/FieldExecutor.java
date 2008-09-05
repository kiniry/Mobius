package mobius.bico.executors;

import java.util.ArrayList;
import java.util.List;

import mobius.bico.Util;
import mobius.bico.bicolano.AType;
import mobius.bico.bicolano.coq.CType;
import mobius.bico.bicolano.coq.CoqStream;
import mobius.bico.bicolano.coq.Translator;
import mobius.bico.bicolano.coq.Translator.Access;
import mobius.bico.implem.IImplemSpecifics;

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
    for (Field field : fJavaClass.getFields()) {
      doField(field);
      getOut().println();
    }
    
  }

/**
   * Enumerates in a Coq friendly form all the fields of the class.
   */
  public void doEnumeration() {
    final CoqStream fOut = getOut();
    final IImplemSpecifics fImplemSpecif = getImplemSpecif();
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
   * to be imported in the current module.
   * 
   * @return The list of module to be imported
   */
  public List<String> startModulesToBeImported() {
    /*the list of modules to be imported in the current module. 
     *  For instance, the module which describes the type of the field 
     *  must be imported in the current module:
     *  
     *  Require Import D_type.v
     *  
     *  Field c := (Name, D)
     *  
     */
    final List<String> modulesToBeImported = 
      new ArrayList<String>();
    for (Field field : fJavaClass.getFields()) {
      final Type type = field.getType();
      if (type  instanceof ObjectType) {
        final String  signature = ((ObjectType)type).getSignature();
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

    fOutSig.definitionStart(Util.coqify(field.getName()) + "ShortFieldSignature", 
                             "ShortFieldSignature");
    fOutSig.println("FIELDSIGNATURE.Build_t");
    fOutSig.incTab();
    // !!! here positives
    fOutSig.println("(" + fieldIdx + "%positive)");
    
    // !!! here will be conversion
    fOutSig.println(AType.getInstance().convertType(field.getType(), getRepository()));
    fOutSig.decTab();
    fOutSig.println(".\n");
    fOutSig.definition(Util.coqify(field.getName()) + "FieldSignature", 
                       "FieldSignature",
                       Translator.couple("name",
                                         Util.coqify(field.getName()) + 
                                         "ShortFieldSignature"));
    
  }

  /**
   * Proper definition of the field for Coq.
   * @param field the field to compute
   */
  private void doField(final Field field) {
    final CoqStream out = getOut();
    out.definitionStart(Util.coqify(field.getName()) + "Field", "Field");
    out.print("FIELD.Build_t");
    out.incTab();
    String strf = Util.coqify(field.getName()) + "ShortFieldSignature";
    out.println(strf);
    
    out.println("" + field.isFinal());
    out.println("" + field.isStatic());
    out.println(Access.translate(field));
    // FIXME current solution
    strf = "FIELD.UNDEF";
    out.println(strf);
    out.decTab();
    out.println(".");
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
      getDico().addField(field.getName(), 
                     getDico().getCoqPackageName(fJavaClass), 
                     getDico().getCoqClassName(fJavaClass), 
                     fieldIdx);
      doFieldSignature(field, fieldIdx);
    }

    
  }
}
