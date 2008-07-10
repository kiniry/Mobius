package mobius.cct.repositories.cp;

import mobius.cct.repositories.cp.entries.ClassEntry;
import mobius.cct.repositories.cp.entries.DoubleEntry;
import mobius.cct.repositories.cp.entries.FloatEntry;
import mobius.cct.repositories.cp.entries.IntegerEntry;
import mobius.cct.repositories.cp.entries.LongEntry;
import mobius.cct.repositories.cp.entries.StringEntry;
import mobius.cct.repositories.cp.entries.Utf8Entry;

/**
 * Abstract class implementing ConstantPoolBuilder new* methods
 * using newEntry().
 * @see mobius.cct.repositories.cp.ConstantPoolBuilder 
 * ConstantPoolBuilder
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public abstract class AbstractBuilder 
  implements ConstantPoolBuilder {
  /**
   * Add class reference.
   * @param c Class name in internal form.
   * @return Index of new or existing constant.
   */
  @Override
  public int newClass(final String c) {
    return newEntry(new ClassEntry(newUtf8(c)));
  }

  /**
   * Add double value.
   * @param v Double value.
   * @return Index of new or existing constant.
   */
  @Override
  public int newDouble(final double v) {
    return newEntry(new DoubleEntry(v));
  }

  /**
   * Add float value.
   * @param v Float value.
   * @return Index of new or existing constant.
   */
  @Override
  public int newFloat(final float v) {
    return newEntry(new FloatEntry(v));
  }

  /**
   * Add integer value.
   * @param v Integer value.
   * @return Index of new or existing constant.
   */
  @Override
  public int newInt(final int v) {
    return newEntry(new IntegerEntry(v));
  }

  /**
   * Add long value.
   * @param v Long value.
   * @return Index of new or existing constant.
   */
  @Override
  public int newLong(final long v) {
    return newEntry(new LongEntry(v));
  }

  /**
   * Add string value.
   * @param s String value.
   * @return Index of new or existing constant.
   */
  @Override
  public int newString(final String s) {
    return newEntry(new StringEntry(newUtf8(s)));
  }

  /**
   * Add Utf8 value.
   * @param v Utf8 value.
   * @return Index of new or existing constant.
   */
  @Override
  public int newUtf8(final String v) {
    return newEntry(new Utf8Entry(v));
  }

}
