package mobius.bmlvcgen.bml;

/**
 * An assertion can be evaluated before or
 * after an instruction.
 * @author Tadeusz Sznuk (tsznuk@mimuw.edu.pl)
 */
public enum AssertType {
  /** Evaluated before statement. */
  PRE, 
  /** Evaluated after statement. */
  POST;
}
