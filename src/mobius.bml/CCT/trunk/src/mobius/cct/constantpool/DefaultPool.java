package mobius.cct.constantpool;

import java.io.DataOutputStream;
import java.io.IOException;
import java.io.OutputStream;
import java.util.Iterator;

import mobius.cct.constantpool.entries.Entry;
import mobius.cct.constantpool.entries.Utf8Entry;
import mobius.cct.util.ArrayIterator;

/**
 * Default implementation of constant pool.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public class DefaultPool implements ConstantPool {
  /**
   * Array of entries, with null values stored under
   * unusable indices.
   */
  private final Entry[] fEntries;
  
  /**
   * Constructor.
   * @param entries Array of constant pool entries.
   */
  public DefaultPool(final Entry[] entries) {
    int size;
    int i, j;
    
    size = 0;
    for (i = 0; i < entries.length; i++) {
      if (entries[i] != null) {
        size += entries[i].getSize();
      }
    }
    if (size > 65536) {
      throw new IllegalArgumentException("Too many constants!");
    }
    fEntries = new Entry[size];
    j = 0;
    for (i = 0; i < entries.length; i++) {
      if (entries[i] != null) {
        fEntries[j] = entries[i];
        j += entries[i].getSize();
      }
    }
  }

  /**
   * Try to read and return string value from
   * given index in a constant pool.
   * Returns null if the index as invalid.
   * @param cp Constant pool.
   * @param index Index. 
   * @return String value or null.
   */
  public static String getString(final ConstantPool cp,
                                 final int index) {
    final Entry entry;
    try {
      entry = cp.getEntry(index);
    } catch (IllegalIndexException e) {
      return null;
    }
    if (!(entry instanceof Utf8Entry)) {
      return null;
    }
    return ((Utf8Entry)entry).getValue();
  }
  
  /**
   * Iterate over all entries.
   * @return Iterator.
   */
  public Iterator<Entry> iterator() {
    return new ArrayIterator<Entry>(fEntries);
  }
  
  /**
   * Get entry.
   * @param index Entry index.
   * @return Entry.
   * @throws IllegalIndexException .
   */
  public Entry getEntry(final int index) 
    throws IllegalIndexException {
    final Entry entry;
    
    if ((index < 1) || (index > fEntries.length)) {
      throw new InvalidIndexException(index);
    }
    entry = fEntries[index - 1];
    if (entry == null) {
      throw new UnusableIndexException(index);
    }
    return entry;
  }

  /**
   * Return constant pool size (number of valid indices).
   * @return Size.
   */
  public int getSize() {
    return fEntries.length;
  }

  /**
   * Write to stream.
   * @param os Output stream.
   * @throws IOException .
   */
  public void write(final OutputStream os) throws IOException {
    int i;
    Entry entry;
    final DataOutputStream ds = new DataOutputStream(os);
    ds.writeShort(fEntries.length + 1);
    for (i = 0; i < fEntries.length; i++) {
      entry = fEntries[i]; 
      if (entry != null) {
        ds.writeByte(entry.getType());
        entry.write(ds);
      }
    }
  }

}
