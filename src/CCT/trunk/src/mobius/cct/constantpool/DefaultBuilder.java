package mobius.cct.constantpool;

import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Vector;

import mobius.cct.constantpool.entries.Entry;

/**
 * Deafult implementation of constant pool builder.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public class DefaultBuilder extends AbstractBuilder {
  /**
   * Vector of entries (passed to ConstantPoolFactory).
   * Contains null values under unusable indices.
   */
  private final List<Entry> fEntries;
  
  /**
   * Map of constants of recognized types.
   */
  private Map<Entry, Integer> fMap;
  
  /**
   * Constructor - create empty pool.
   */
  public DefaultBuilder() {
    fEntries = new Vector<Entry>();
    fMap = new HashMap<Entry, Integer>();
  }
  
  /**
   * Constructor - initialize with given constant pool.
   * Indices of existing entries will not change.
   * @param pool Initial constant pool.
   */
  public DefaultBuilder(final ConstantPool pool) {
    Iterator<Entry> it;
    int i, j;
    Entry e;
    
    fEntries = new Vector<Entry>();
    fMap = new HashMap<Entry, Integer>();
    
    it = pool.iterator();
    i = 1;
    while (it.hasNext()) {
      e = it.next();
      fMap.put(e, i);
      fEntries.add(e);
      i++;
      for (j = 1; j < e.getSize(); j++) {
        fEntries.add(null);
        i++;
      }
    }
  }

  /**
   * Convert to ConstantPool.
   * @param factory Factory to be used.
   * @return Constant pool.
   */
  public ConstantPool toConstantPool(final ConstantPoolFactory factory) {
    return factory.create(fEntries.toArray(new Entry[fEntries.size()]));
  }

  /**
   * Add entry.
   * @param e Entry.
   * @return Index.
   */
  public int newEntry(final Entry e) {
    int i, r;
    
    if (fMap.containsKey(e)) {
      return fMap.get(e);
    } else {
      fEntries.add(e);
      r = fEntries.size();
      fMap.put(e, r);
      for (i = 1; i < e.getSize(); i++) {
        fEntries.add(null);
      }
      return r;
    }
  }

}
