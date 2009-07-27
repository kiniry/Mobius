package mobius.cct.constantpool;

import java.io.IOException;
import java.io.OutputStream;
import java.util.Iterator;

import mobius.cct.constantpool.entries.Entry;

/**
 * Interface of constant pools.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public interface ConstantPool {
  /**
   * Return constant pool size. This number defines the range
   * of valid indices (1..getSize()), but not all indices are
   * usable (because some constants require more than one index).
   * @return size.
   */
  int getSize();
  
  /** 
   * Iterate over all entries (ordered by indices).
   * @return Iterator.
   */
  Iterator<Entry> iterator();
  
  /**
   * Return entry with given index.
   * @param index Index.
   * @return Entry.
   * @throws IllegalIndexException If the index is invalid or unusable.
   */
  Entry getEntry(int index) throws IllegalIndexException;
  
  /**
   * Write constant pool (including size) to given output stream.
   * @param os Output stream.
   * @throws IOException .
   */
  void write(OutputStream os) throws IOException;
}
