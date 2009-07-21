package mobius.bmlvcgen.args;

import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;

import mobius.bmlvcgen.args.converters.Converter;
import mobius.bmlvcgen.args.exceptions.ReflectionException;

/**
 * This type of option uses reflection to call a method with option argument as
 * a parameter.
 * @author Tadeusz Sznuk (tsznuk@mimuw.edu.pl)
 */
public class SetterOption extends AbstractOption {
  private final Object target;

  private final Method method;

  private final Converter converter;

  private final String defaultValue;

  /**
   * Constructor.
   * @param target Target object.
   * @param method Method to call.
   * @param converter Converter to be used before call.
   * @param defaultValue Default value.
   * @param shortName Option name (short).
   * @param arity Parameter arity.
   */
  public SetterOption(final Object target, final Method method,
                      final Converter converter, final String defaultValue,
                      final char shortName, final Arity arity) {
    super(shortName, arity);
    this.target = target;
    this.method = method;
    this.converter = converter;
    this.defaultValue = defaultValue;
  }

  /**
   * Constructor.
   * @param target Target object.
   * @param method Method to call.
   * @param converter Converter to be used before call.
   * @param defaultValue Default value.
   * @param longName Option name (long).
   * @param arity Parameter arity.
   */
  public SetterOption(final Object target, final Method method,
                      final Converter converter, final String defaultValue,
                      final String longName, final Arity arity) {
    super(longName, arity);
    this.target = target;
    this.method = method;
    this.converter = converter;
    this.defaultValue = defaultValue;
  }

  /**
   * Constructor.
   * @param target Target object.
   * @param method Method to call.
   * @param converter Converter to be used before call.
   * @param defaultValue Default value.
   * @param shortName Option name (short).
   * @param longName Option name (long).
   * @param arity Parameter arity.
   */
  public SetterOption(final Object target, final Method method,
                      final Converter converter, final String defaultValue,
                      final char shortName, final String longName,
                      final Arity arity) {
    super(shortName, longName, arity);
    this.target = target;
    this.method = method;
    this.converter = converter;
    this.defaultValue = defaultValue;
  }

  /** {@inheritDoc} */
  public void setValue(final String value) {
    final Class<?>[] params = method.getParameterTypes();
    if (params.length == 1) {
      final Object converted;
      if (value == null) {
        converted = converter.convert(params[0], defaultValue);
      } else {
        converted = converter.convert(params[0], value);
      }
      try {
        method.invoke(target, converted);
      } catch (IllegalAccessException e) {
        throw new ReflectionException(e);
      } catch (InvocationTargetException e) {
        throw new ReflectionException(e);
      }
    } else {
      try {
        method.invoke(target);
      } catch (IllegalAccessException e) {
        throw new ReflectionException(e);
      } catch (InvocationTargetException e) {
        throw new ReflectionException(e);
      }
    }
  }
}
