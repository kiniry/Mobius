package mobius.bmlvcgen.args.converters;

/**
 * Default implementation of converter interface. Can convert strings, integers
 * and booleans.
 * @author Tadeusz Sznuk (tsznuk@mimuw.edu.pl)
 */
public class DefaultConverter implements Converter {

  /** {@inheritDoc} */
  public boolean canConvertTo(final Class<?> clazz) {
    return Integer.class.equals(clazz) || 
           int.class.equals(clazz) ||
           String.class.equals(clazz) || 
           boolean.class.equals(clazz) ||
           Boolean.class.equals(clazz);
  }

  /** {@inheritDoc} */
  public Object convert(final Class<?> clazz, final String v) {
    Object result;
    
    if (Integer.class.equals(clazz)) {
      if (v == null || "".equals(v)) {
        result = null;
      } else {
        result = parseInt(v);
      }
    } else if (int.class.equals(clazz)) {
      if (v == null || "".equals(v)) {
        result = 0;
      } else {
        result = parseInt(v);
      }
    } else if (String.class.equals(clazz)) {
      result = v;
    } else if (Boolean.class.equals(clazz) || 
        boolean.class.equals(clazz)) {
      result = parseBool(v);
    } else {
      throw new IllegalArgumentException(
                  "Argument conversion error. ");
    }
    return result;
  }

  private static Object parseInt(final String v) {
    try {
      return Integer.parseInt(v);
    } catch (final NumberFormatException e) {
      throw new IllegalArgumentException(e);
    }
  }

  private static Object parseBool(final String v) {
    return !"no".equalsIgnoreCase(v) && 
           !"false".equalsIgnoreCase(v) &&
           !"n".equalsIgnoreCase(v);
  }
  
}
