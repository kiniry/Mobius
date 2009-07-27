package mobius.cct.constantpool;

import java.io.IOException;
import java.io.InputStream;

import mobius.cct.constantpool.entries.Entry;

/**
 * Interace of objects used to create and read constant pools.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public interface ConstantPoolFactory {
  /**
   * Create constant pool from array of entries.
   * It is important to note that index of an entry in the pool
   * does not have to be the same as its index in the array 
   * (because some fields use more than one index).
   * {@code null} entries are skipped.
   * @param entries Array of entries.
   * @return Constant pool.
   */
  ConstantPool create(Entry[] entries);
  
  /** 
   * Read constant pool from given input stream.
   * First bytes of the stream represent size of the pool.
   * @param is Input stream.
   * @return Constant pool.
   * @throws UnknownConstantException If a constant of unsupported
   * type is encountered.
   * @throws IOException .
   */
  ConstantPool read(InputStream is) 
    throws IOException, UnknownConstantException;
}
