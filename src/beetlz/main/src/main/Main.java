package main;

/**
 * Main class for the ConsistencyChecker.
 * @author Eva Darulova (edarulova@googlemail.com)
 * @version beta-1
 */
public final class Main {

  /** */
  private Main() { }

  /**
   * Main entry point for stand-alone use.
   * @param some_args parameters and options
   */
  public static void main(final String[] some_args) {
    final Beetlz checker = new Beetlz(some_args, System.err, System.out);
    checker.run();
  }
}
