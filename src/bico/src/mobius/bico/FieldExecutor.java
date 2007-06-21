package mobius.bico;

import org.apache.bcel.classfile.Field;
import org.apache.bcel.classfile.JavaClass;

public class FieldExecutor extends ABasicExecutor {
  /** determine the span of the 'reserved' fields names number default is 1. */
  private static final int RESERVED_FIELDS = 1;

  private JavaClass jc;
  
  
  /**
   * @param jc the current class
   * @param packageName the index representing the package
   * @param className the number representing the class
   */
  public FieldExecutor(ABasicExecutor be, JavaClass jc) {
    super(be);
    
    this.jc = jc;
  }
  
  /**
   * Fields handling.
   * @throws ClassNotFoundException if a class typing a field
   * cannot be resolved
   */
  public void start() throws ClassNotFoundException {
    int fieldIdx = RESERVED_FIELDS;
    
    for (Field field : jc.getFields()) {
      fieldIdx++;
      fDico.addField(field.getName(), 
                     fDico.getCoqPackageName(jc), 
                     fDico.getCoqClassName(jc), 
                     fieldIdx);
      doFieldSignature(field, fieldIdx);
      doField(field);

      fOut.println();
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
