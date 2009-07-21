package mobius.bmlvcgen.args;

import java.lang.reflect.Field;

import mobius.bmlvcgen.args.converters.Converter;
import mobius.bmlvcgen.args.exceptions.ReflectionException;

/**
 * This type of option uses reflection to set value of a field.
 * @author Tadeusz Sznuk (tsznuk@mimuw.edu.pl)
 */
public class FieldOption extends AbstractOption {
  private final Object target;

  private final Field field;

  private final Converter converter;

  private final String defaultValue;

  /**
   * Constructor.
   * @param target Target object.
   * @param field Field to set.
   * @param converter Converter to be used.
   * @param defaultValue Default value.
   * @param shortName Option name (short).
   * @param arity Parameter arity.
   */
  public FieldOption(final Object target, final Field field,
                     final Converter converter, final String defaultValue,
                     final char shortName, final Arity arity) {
    super(shortName, arity);
    this.target = target;
    this.field = field;
    this.converter = converter;
    this.defaultValue = defaultValue;
  }

  /**
   * Constructor.
   * @param target Target object.
   * @param field Field to set.
   * @param converter Converter to be used.
   * @param defaultValue Default value.
   * @param longName Option name (long).
   * @param arity Parameter arity.
   */
  public FieldOption(final Object target, final Field field,
                     final Converter converter, final String defaultValue,
                     final String longName, final Arity arity) {
    super(longName, arity);
    this.target = target;
    this.field = field;
    this.converter = converter;
    this.defaultValue = defaultValue;
  }

  /**
   * Constructor.
   * @param target Target object.
   * @param field Field to set.
   * @param converter Converter to be used.
   * @param defaultValue Default value.
   * @param shortName Option name (short).
   * @param longName Option name (long).
   * @param arity Parameter arity.
   */
  public FieldOption(final Object target, final Field field,
                     final Converter converter, final String defaultValue,
                     final char shortName, final String longName,
                     final Arity arity) {
    super(shortName, longName, arity);
    this.target = target;
    this.field = field;
    this.converter = converter;
    this.defaultValue = defaultValue;
  }

  /** {@inheritDoc} */
  public void setValue(final String value) {
    final Object converted;
    if (value == null) {
      converted = converter.convert(field.getType(), defaultValue);
    } else {
      converted = converter.convert(field.getType(), value);
    }
    try {
      field.set(target, converted);
    } catch (IllegalAccessException e) {
      throw new ReflectionException(e);
    }
  }
}
