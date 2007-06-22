package mobius.bico;

import org.apache.bcel.classfile.Field;
import org.apache.bcel.classfile.JavaClass;

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
      Util.writeln(fOut, tab + 1, fImplemSpecif.getNoFields());
    } 
    else {
      String str2 = "(";
      for (int i = 0; i < ifield.length - 1; i++) {
        str2 += fImplemSpecif.fieldsCons(Util.coqify(ifield[i].getName()) + "Field");
      }
      str2 += fImplemSpecif.fieldsEnd(Util.coqify(ifield[ifield.length - 1].getName()) + 
                                      "Field");
      str2 += ")";
      Util.writeln(fOut, tab + 1, str2);
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
    Util.writeln(fOut, tab, strf);
    // !!! here positives
    
    strf = "(" + fieldIdx + "%positive)";
    Util.writeln(fOut, tab + 1, strf);
    // !!! here will be conversion
    strf = Util.convertType(field.getType(), fRepos);
    Util.writeln(fOut, tab + 1, strf);
    Util.writeln(fOut, tab, ".");
    fOut.println();
    strf = "Definition " + Util.coqify(field.getName()) +
           "FieldSignature : FieldSignature := (className, " + 
           Util.coqify(field.getName()) + "ShortFieldSignature).\n";
    Util.writeln(fOut, tab, strf);
  }

  /**
   * Proper definition of the field for Coq.
   * @param field the field to compute
   */
  private void doField(final Field field) {
    final int tab = 2;
    
    String strf = "Definition " + Util.coqify(field.getName()) +
           "Field : Field := FIELD.Build_t";
    Util.writeln(fOut, tab, strf);
    strf = Util.coqify(field.getName()) + "ShortFieldSignature";
    Util.writeln(fOut, tab + 1, strf);
    
    Util.writeln(fOut, tab + 1, "" + field.isFinal());
    Util.writeln(fOut, tab + 1, "" + field.isStatic());
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
    Util.writeln(fOut, tab + 1, visibility);
    // FIXME current solution
    strf = "FIELD.UNDEF";
    Util.writeln(fOut, tab + 1, strf);
    Util.writeln(fOut, tab, ".");
  }
}
