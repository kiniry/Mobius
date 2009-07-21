package mobius.cct.constantpool;

import java.io.DataInputStream;
import java.io.IOException;
import java.io.InputStream;

import mobius.cct.constantpool.entries.Entry;
import mobius.cct.constantpool.readers.DefaultEntryReader;

/**
 * Default implementation of constant pool factory.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public class DefaultFactory implements ConstantPoolFactory {  
  /**
   * Create pool from array of entries.
   * @param entries Array of entries.
   * @return Pool.
   */
  public ConstantPool create(final Entry[] entries) {
    return new DefaultPool(entries);
  }

  /**
   * Read pool from stream.
   * @param is Input stream.
   * @return Constant pool.
   * @throws IOException .
   * @throws UnknownConstantException If a constant type not described
   * in JSR-202 is encountered.
   */
  public ConstantPool read(final InputStream is) 
    throws IOException, UnknownConstantException {
    final int size;
    final Entry[] entries;
    Entry entry;
    int i; 
    int t;
    final DefaultEntryReader reader = new DefaultEntryReader();
    final DataInputStream ds = new DataInputStream(is);
    
    size = ds.readShort();
    entries = new Entry[size];
    i = 0;
    while (i < size - 1) {
      t = ds.readUnsignedByte();
      entry = reader.read(ds, t);
      entries[i] = entry;
      i += entry.getSize();
    }
    return new DefaultPool(entries);
  }
  
}
