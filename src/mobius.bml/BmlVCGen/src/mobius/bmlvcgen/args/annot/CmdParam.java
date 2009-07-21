/**
 * 
 */
package mobius.bmlvcgen.args.annot;

import java.lang.annotation.ElementType;
import java.lang.annotation.Inherited;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;

import mobius.bmlvcgen.args.converters.Converter;
import mobius.bmlvcgen.args.converters.DefaultConverter;

/**
 * This annotation can be placed on setter methods 
 * or directly on fields. Setter can have 0 or 1 parameter.
 * @author Tadeusz Sznuk (tsznuk@mimuw.edu.pl)
 */
@Retention(RetentionPolicy.RUNTIME)
@Target({ ElementType.METHOD, ElementType.FIELD })
@Inherited
public @interface CmdParam {
  /** Short option name. 
   * Hyphen (default) = no short name. */
  char shortName() default '-';

  /** 
   * Long option name.
   * Empty string (default) = no long name.
   */
  String longName() default "";

  /** Is this argument required? */
  boolean required() default false;

  /** Is parameter value optional? */
  boolean valueOptional() default false;

  /** Default value 
   * (useful only if parameter value is optional).
   * If the string is empty, no default value is set. 
   **/
  String defaultValue() default "";

  /**
   * Converter class.
   * Instance of this class will be used to process
   * argument before it is passed to a setter (or before
   * a field is set to it). If this option has no argument,
   * converter is ignored.
   */
  Class<? extends Converter> converter() default DefaultConverter.class;
}
