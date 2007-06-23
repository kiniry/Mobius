package mobius.bico;

import org.apache.bcel.classfile.Field;
import org.apache.bcel.classfile.JavaClass;


/**
 * This class is used in the treatment of fields by bico.
 * 
 * @author J. Charles (julien.charles@inria.fr), 
 * P. Czarnik (czarnik@mimuw.edu.pl), 
 * L. Hubert (laurent.hubert@irisa.fr)
 */
class FieldExecutor extends ABasicExecutor {
  
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
  public FieldExecutor(final ABasicExecutor be, final JavaClass jc) {
    super(be);
    
    fJavaClass = jc;
  }
  
  /**
   * Fields handling.
   * @throws ClassNotFoundException if a class typing a field
   * cannot be resolved
   */
  public void start() throws ClassNotFoundException {
    int fieldIdx = RESERVED_FIELDS;
    
    for (Field field : fJavaClass.getFields()) {
      fieldIdx++;
      fDico.addField(field.getName(), 
                     fDico.getCoqPackageName(fJavaClass), 
                     fDico.getCoqClassName(fJavaClass), 
                     fieldIdx);
      doFieldSignature(field, fieldIdx);
      doField(field);

      fOut.println();
    }
    
  }
  
  /**
   * Enumerates in a Coq friendly form all the fields of the class.
   * @param tab the current tabulation level.
   */
  public void doEnumeration(final int tab) {
    // fields
    final Field[] ifield = fJavaClass.getFields();
    if (ifield.length == 0) {
      fOut.println(tab + 1, fImplemSpecif.getNoFields());
    } 
    else {
      String str2 = "(";
      for (int i = 0; i < ifield.length - 1; i++) {
        str2 += fImplemSpecif.fieldsCons(Util.coqify(ifield[i].getName()) + "Field");
      }
      str2 += fImplemSpecif.fieldsEnd(Util.coqify(ifield[ifield.length - 1].getName()) + 
                                      "Field");
      str2 += ")";
      fOut.println(tab + 1, str2);
    }
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
    final int tab = 2;
    
    String strf = "Definition " + Util.coqify(field.getName()) +
           "ShortFieldSignature : ShortFieldSignature := FIELDSIGNATURE.Build_t ";
    fOut.println(tab, strf);
    // !!! here positives
    
    strf = "(" + fieldIdx + "%positive)";
    fOut.println(tab + 1, strf);
    // !!! here will be conversion
    strf = Util.convertType(field.getType(), fRepos);
    fOut.println(tab + 1, strf);
    fOut.println(tab, ".");
    fOut.println();
    strf = "Definition " + Util.coqify(field.getName()) +
           "FieldSignature : FieldSignature := (className, " + 
           Util.coqify(field.getName()) + "ShortFieldSignature).\n";
    fOut.println(tab, strf);
  }

  /**
   * Proper definition of the field for Coq.
   * @param field the field to compute
   */
  private void doField(final Field field) {
    final int tab = 2;
    
    String strf = "Definition " + Util.coqify(field.getName()) +
           "Field : Field := FIELD.Build_t";
    fOut.println(tab, strf);
    strf = Util.coqify(field.getName()) + "ShortFieldSignature";
    fOut.println(tab + 1, strf);
    
    fOut.println(tab + 1, "" + field.isFinal());
    fOut.println(tab + 1, "" + field.isStatic());
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
    fOut.println(tab + 1, visibility);
    // FIXME current solution
    strf = "FIELD.UNDEF";
    fOut.println(tab + 1, strf);
    fOut.println(tab, ".");
  }
}
