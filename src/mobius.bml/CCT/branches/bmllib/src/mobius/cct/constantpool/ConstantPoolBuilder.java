package mobius.cct.constantpool;

import mobius.cct.constantpool.entries.Entry;

/**
 * Interface of objects used to build constant pools
 * by adding constants.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public interface ConstantPoolBuilder {
  
  /**
   * Convert to constant pool.
   * @param factory Factory used to create the pool.
   * @return Constant pool.
   */
  ConstantPool toConstantPool(ConstantPoolFactory factory);
  
  /**
   * Add class reference constant v to the pool, unless such
   * constant is already present.
   * @param c Class name in internal format.
   * @return Index of a new or already existing constant.
   */
  int newClass(String c);
  
  /**
   * Add string constant v to the pool, unless such
   * constant is already present.
   * @param s String value.
   * @return Index of a new or already existing constant.
   */
  int newString(String s);
  
  /**
   * Add integer constant v to the pool, unless such
   * constant is already present.
   * @param v Integer value.
   * @return Index of a new or already existing constant.
   */
  int newInt(int v);
  
  /**
   * Add long constant v to the pool, unless such
   * constant is already present.
   * @param v Long value.
   * @return Index of a new or already existing constant.
   */
  int newLong(long v);
  
  /**
   * Add float constant v to the pool, unless such
   * constant is already present.
   * @param v Float value.
   * @return Index of a new or already existing constant.
   */
  int newFloat(float v);
  
  /**
   * Add double constant v to the pool, unless such
   * constant is already present.
   * @param v Integer value.
   * @return Index of a new or already existing constant.
   */
  int newDouble(double v);
  
  /**
   * Add Utf8 constant v to the pool, unless such
   * constant is already present.
   * @param v Utf8 value.
   * @return Index of a new or already existing constant.
   */
  int newUtf8(String v);
  
  /**
   * Add entry e to the pool, unless an entry with the same 
   * value is already present.
   * @param e Entry.
   * @return Index of a new or already existing constant.
   */
  int newEntry(Entry e);
}
