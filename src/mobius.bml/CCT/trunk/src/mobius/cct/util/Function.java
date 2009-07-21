package mobius.cct.util;

/**
 * Interface of functions wrapped in classes.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 * @param <Args> Type of function arguments.
 * @param <Result> Result type.
 */
public interface Function<Args, Result> {
  /**
   * Call function.
   * @param args Arguments.
   * @return Result.
   */
  Result call(Args args);
}
