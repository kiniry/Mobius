package mobius.cct.repositories.cp;

import java.io.DataInputStream;
import java.io.IOException;
import java.io.InputStream;

import mobius.cct.repositories.cp.entries.Entry;
import mobius.cct.repositories.cp.readers.DefaultEntryReader;

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
  @Override
  public ConstantPool create(final Entry[] entries) {
    return new DefaultPool(entries);
  }

  /**
   * Read pool from stream.
   * @param is Input stream.
   * @throws IOException .
   * @throws UnknownConstantException If a constant type not described
   * in JSR-202 is encountered.
   */
  @Override
  public ConstantPool read(InputStream is) throws IOException,
      UnknownConstantException {
    final int size;
    final Entry[] entries;
    Entry entry;
    int i; 
    byte t;
    final DefaultEntryReader reader = new DefaultEntryReader();
    final DataInputStream ds = new DataInputStream(is);
    
    size = ds.readShort();
    entries = new Entry[size];
    i = 0;
    while (i < size - 1) {
      t = ds.readByte();
      entry = reader.read(ds, t);
      entries[i] = entry;
      i += entry.getSize();
    }
    return new DefaultPool(entries);
  }
  
}
