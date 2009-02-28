package mobius.bmlvcgen.args;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import mobius.bmlvcgen.args.Option.Arity;
import mobius.bmlvcgen.args.exceptions.ArgException;
import mobius.bmlvcgen.args.exceptions.ArgMissingException;
import mobius.bmlvcgen.args.exceptions.IllegalValueException;
import mobius.bmlvcgen.args.exceptions.UnknownOptionException;
import mobius.bmlvcgen.args.exceptions.ValueMissingException;

/**
 * Class used to parse command-line arguments.
 * @author Tadeusz Sznuk (tsznuk@mimuw.edu.pl)
 */
public class ArgParser {
  private final Map<Character, Option> shortOpts;

  private final Map<String, Option> longOpts;

  private final Set<Option> requiredOpts;

  /**
   * Constructor.
   */
  public ArgParser() {
    shortOpts = new HashMap<Character, Option>();
    longOpts = new HashMap<String, Option>();
    requiredOpts = new HashSet<Option>();
  }

  /**
   * Add option.
   * @param o Option.
   */
  public void addOption(final Option o) {
    if (o.getShortName() != null) {
      shortOpts.put(o.getShortName(), o);
    }
    if (o.getLongName() != null) {
      longOpts.put(o.getLongName(), o);
    }
  }

  /**
   * Add required option.
   * @param o Option.
   */
  public void addRequiredOption(final Option o) {
    addOption(o);
    requiredOpts.add(o);
  }

  /**
   * Parse list of command line arguments.
   * @param args Argument list.
   * @return Non-option arguments.
   * @throws ArgException If arguments are invalid.
   */
  public String[] parse(final String... args) throws ArgException {
    final ParserState state = new ParserState(this, args);

    while (state.i < args.length) {
      if (state.noMoreOptions) {
        state.other.add(state.currentArg());
        state.i++;
      } else if (state.currentArg().startsWith("--")) {
        parseLong(state);
      } else if (state.currentArg().startsWith("-")) {
        parseShort(state);
      } else {
        state.other.add(state.currentArg());
        state.i++;
      }
    }

    if (state.req.isEmpty()) {
      return state.other.toArray(new String[0]);
    } else {
      throw new ArgMissingException(state.req);
    }
  }

  // Local variables of parsing function.
  //CHECKSTYLE:OFF
  private static final class ParserState {
    // Non-option arguments.
    public final List<String> other;

    // Required options which were not encountered yet.
    public final Set<Option> req;

    // Arguments.
    public final String[] args;

    // Flag set when '--' is encountered.
    public boolean noMoreOptions;

    // Index of current argument.
    public int i;

    public ParserState(final ArgParser p, final String[] args) {
      other = new ArrayList<String>();
      req = new HashSet<Option>(p.requiredOpts);
      this.args = args;
      i = 0;
      noMoreOptions = false;
    }

    public final String currentArg() {
      return args[i];
    }
  }
  //CHECKSTYLE:ON
  
  // Parse an option starting with two hyphens.
  private void parseLong(final ParserState state) throws ArgException {

    final String arg = state.currentArg();
    if (arg.length() > 2) {
      final int eq = arg.indexOf('=');
      final String argName;
      if (eq >= 0) {
        argName = arg.substring(2, eq);
      } else {
        argName = arg.substring(2);
      }
      final Option option = longOpts.get(argName);
      if (option == null) {
        throw new UnknownOptionException(arg);
      } else {
        state.req.remove(option);
        state.i++;
        if (eq >= 0) {
          setArgument(state, option, arg.substring(eq + 1, arg.length()));
        } else {
          fetchArgument(state, option);
        }
      }
    } else {
      state.noMoreOptions = true;
      state.i++;
    }
  }

  // Parse an option starting with single hyphen.
  private void parseShort(final ParserState state) throws ArgException {

    final String arg = state.currentArg();

    if (arg.length() > 1) {
      final Option first = shortOpts.get(arg.charAt(1));
      if (first == null) {
        throw new UnknownOptionException(arg.substring(0, 2));
      }
      if (first.getArity() == Arity.NO_ARGUMENT) {
        parseFlags(state);
      } else {
        state.req.remove(first);
        if (arg.length() > 2) {
          setArgument(state, first, arg.substring(2));
          state.i++;
        } else {
          state.i++;
          fetchArgument(state, first);
        }
      }
    } else {
      state.other.add("-");
      state.i++;
    }
  }

  // Parse an argument of the form -xyz... ,
  // where x, y, z, ... are options without 
  // arguments.
  private void parseFlags(final ParserState state) throws ArgException {

    final String arg = state.currentArg();
    for (int j = 1; j < arg.length(); j++) {
      final char optName = arg.charAt(j);
      final Option opt = shortOpts.get(optName);
      if (opt == null) {
        throw new UnknownOptionException("-" + optName);
      }
      if (opt.getArity() == Arity.REQUIRED_ARGUMENT) {
        throw new ValueMissingException(opt);
      }
      state.req.remove(opt);
      opt.setValue(null);
    }
    state.i++;
  }

  // Try to read an argument and pass it to given option.
  private void fetchArgument(final ParserState state, final Option option)
    throws ArgException {

    final String value;

    switch (option.getArity()) {
      case NO_ARGUMENT:
        value = null;
        break;
      case REQUIRED_ARGUMENT:
        if (state.i < state.args.length) {
          value = state.currentArg();
          state.i++;
        } else {
          throw new ValueMissingException(option);
        }
        break;
      case OPTIONAL_ARGUMENT:
        if (state.i < state.args.length && isValue(state.currentArg())) {
          value = state.currentArg();
          state.i++;
        } else {
          value = null;
        }
        break;
      default:
        assert (false);
        return;
    }
    setArgument(state, option, value);
  }

  // Call option.setValue().
  // If the value is null but the argument is required,
  // an exception is raised.
  private void setArgument(final ParserState state, final Option option,
                           final String value) throws ArgException {
    if (option.getArity() == Arity.NO_ARGUMENT && value != null) {

      throw new IllegalValueException(option, value,
                                      "This option should not have a value");
    } else {
      try {
        option.setValue(value);
      } catch (final IllegalArgumentException e) {
        throw new IllegalValueException(option, value);
      }
    }
  }

  private static boolean isValue(final String s) {
    return (!s.startsWith("-")) || s.length() <= 1;
  }

}
