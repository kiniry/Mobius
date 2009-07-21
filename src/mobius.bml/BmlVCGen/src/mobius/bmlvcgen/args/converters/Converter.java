package mobius.bmlvcgen.args.converters;

/**
 * Interface of objects which can convert strings to values of another type.
 * Converter classes must have a zero argument constructor.
 * @author Tadeusz Sznuk (tsznuk@mimuw.edu.pl)
 */
public interface Converter {
  /**
   * Check if this converter can create
   * values of required type.
   * @param clazz Desired result type.
   * @return True if conversion is possible.
   */
  boolean canConvertTo(Class<?> clazz);

  /**
   * Convert string to value.
   * @param clazz Desired result type.
   * @param v String to be converted. 
   * This parameter can be null.
   * @return Conversion result.
   * @throws IllegalArgumentException 
   * If the string cannot be converted.
   */
  Object convert(Class<?> clazz, String v);
}
