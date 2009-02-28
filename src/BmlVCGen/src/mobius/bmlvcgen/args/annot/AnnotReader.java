package mobius.bmlvcgen.args.annot;

import java.lang.reflect.Field;
import java.lang.reflect.Method;

import mobius.bmlvcgen.args.ArgParser;
import mobius.bmlvcgen.args.FieldOption;
import mobius.bmlvcgen.args.Option;
import mobius.bmlvcgen.args.SetterOption;
import mobius.bmlvcgen.args.Option.Arity;
import mobius.bmlvcgen.args.converters.Converter;

/**
 * Reads annotations from an object and adds all 
 * found options to a parser.
 * @author Tadeusz Sznuk (tsznuk@mimuw.edu.pl)
 */
public final class AnnotReader {
  /**
   * Constructor (should not be invoked).
   */
  private AnnotReader() {
  }
  
  /**
   * Read annotations from a class and add all declared
   * options to an ArgParser.
   * @param obj Object to be processed.
   * @param parser Parser to which options should be added.
   * @throws RuntimeException If annotations are not valid.
   */
  public static void findOptions(final Object obj, 
                                 final ArgParser parser) {
    final Class<?> clazz = obj.getClass();

    for (final Method m : clazz.getMethods()) {
      final CmdParam annot = m.getAnnotation(CmdParam.class);
      if (annot != null) {
        final Option option = processMethod(obj, m, annot);
        if (annot.required()) {
          parser.addRequiredOption(option);
        } else {
          parser.addOption(option);
        }
      }
    }
    for (final Field f : clazz.getFields()) {
      final CmdParam annot = f.getAnnotation(CmdParam.class);
      if (annot != null) {
        final Option option = processField(obj, f, annot);
        if (annot.required()) {
          parser.addRequiredOption(option);
        } else {
          parser.addOption(option);
        }
      }
    }
  }

  // Construct option corresponding to given
  // annotated method.
  private static Option processMethod(final Object obj, 
                                      final Method m,
                                      final CmdParam annot) {

    final Converter converter = getConverter(annot);
    final Arity arity = getArity(m, annot);
    final Class<?>[] params = m.getParameterTypes();
    if (!(params.length != 1 || converter.canConvertTo(params[0]))) {
      throw new AnnotReaderException("Invalid converter");
    }
    final Option option;
    if (annot.shortName() == '-') {
      option = new SetterOption(obj, m, converter, 
                                annot.defaultValue(), 
                                annot.longName(), arity);
    } else {
      option = new SetterOption(obj, m, converter, 
                                annot.defaultValue(), 
                                annot.shortName(), 
                                annot.longName(), arity);
    }
    return option;
  }

  // Construct converter object.
  private static Converter getConverter(final CmdParam annot) {
    try {
      return annot.converter().newInstance();
    } catch (InstantiationException e) {
      throw new AnnotReaderException(
                  "Converter must have a default constructor.", e);
    } catch (IllegalAccessException e) {
      throw 
        new AnnotReaderException(
          "Converter must have a PUBLIC default constructor.", e);
    }
  }

  // Deduce arity from function signature and annotations.
  private static Arity getArity(final Method m, 
                                final CmdParam annot) {
    final Class<?>[] params = m.getParameterTypes();
    if (params.length == 0) {
      return Arity.NO_ARGUMENT;
    } else if (params.length == 1) {
      if (annot.valueOptional()) {
        return Arity.OPTIONAL_ARGUMENT;
      } else {
        return Arity.REQUIRED_ARGUMENT;
      }
    } else {
      throw new AnnotReaderException("Too many arguments");
    }
  }

  // Construct option corresponding to given
  // annotated field.
  private static Option processField(final Object obj, 
                                     final Field field,
                                     final CmdParam annot) {

    final Converter converter = getConverter(annot);
    if (!converter.canConvertTo(field.getType())) {
      throw new AnnotReaderException(
                  "Invalid converter for type " + 
                  field.getType() + ".");
    }
    final Arity arity;
    if (annot.valueOptional()) {
      arity = Arity.OPTIONAL_ARGUMENT;
    } else {
      arity = Arity.REQUIRED_ARGUMENT;
    }
    final Option option;
    if (annot.shortName() == '-') {
      option = new FieldOption(obj, field, converter, 
                               annot.defaultValue(),
                               annot.longName(), arity);
    } else {
      option = new FieldOption(obj, field, converter, 
                               annot.defaultValue(),
                               annot.shortName(), 
                               annot.longName(), arity);
    }
    return option;
  }

}
