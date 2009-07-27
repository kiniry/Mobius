package mobius.cct.classfile.types;

import java.io.IOException;
import java.io.Reader;
import java.io.StringReader;

/**
 * Type of field or method argument.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public abstract class FieldType extends ResultType {
  /**
   * Parse field type in internal form.
   * @param reader Input stream.
   * @return Parsed type.
   * @throws IOException .
   */
  public static FieldType parse(final Reader reader) 
    throws IOException {

    final ResultType result = ResultType.parse(reader);
    if (result instanceof FieldType) {
      return (FieldType)result;
    } else {
      throw new IOException("Invalid field type");
    }
  }
  
  /**
   * Parse field type in internal form.
   * @param str Input string.
   * @return Parsed type.
   * @throws IOException .
   */
  public static FieldType parse(final String str) 
    throws IOException {
    return parse(new StringReader(str));
  }
  
  /** Check if this object represents the void type.
   * @return false.
   */
  public boolean isVoid() {
    return false;
  }
  
}
