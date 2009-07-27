package mobius.cct.classfile;

import java.io.DataInputStream;
import java.io.IOException;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.NoSuchElementException;

import mobius.cct.constantpool.ConstantPool;
import mobius.cct.util.FlattenIterator;
import mobius.cct.util.GetIterator;
import mobius.cct.util.MappedIterator;

/**
 * Attributes of a class, field or method.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public final class AttributeMap {
  /**
   * Attributes.
   */
  private final Map<String, List<Attribute>> fAttributes;
  
  /**
   * Constructor - create empty map.
   */
  public AttributeMap() {
    fAttributes = new HashMap<String, List<Attribute>>();
  }
  
  /**
   * Constructor - read attributes from a stream.
   * @param ds Input stream.
   * @param cp Constant pool.
   * @throws IOException .
   */
  public AttributeMap(final DataInputStream ds,
                      final ConstantPool cp) throws IOException {
    final int count = ds.readUnsignedShort();
    fAttributes = new HashMap<String, List<Attribute>>(count);
    for (int i = 0; i < count; i++) {
      final Attribute a = new DefaultAttribute(ds, cp);
      addAttribute(a);
    }
  }
  
  /**
   * Get number of attributes with given name.
   * @param name Attribute name.
   * @return Attribute count.
   */
  public int getCount(final String name) {
    final List<Attribute> list = fAttributes.get(name);
    if (list != null) {
      return list.size();
    } else {
      return 0;
    }
  }

  /**
   * Get attribute.
   * @param name Attribute name.
   * @param i Attribute index.
   * @return Attribute.
   */
  public Attribute get(final String name, final int i) {
    final List<Attribute> list = fAttributes.get(name);
    if (list != null) {
      if ((i >= 0) && (i < list.size())) {
        return list.get(i);
      }
    }
    throw new NoSuchElementException();
  }
  
  /**
   * Remove attribute.
   * @param name Attribute name.
   * @param i Attribute index.
   */
  public void remove(final String name, final int i) {
    final List<Attribute> list = fAttributes.get(name);
    if (list != null) {
      if ((i >= 0) && (i < list.size())) {
        list.remove(i);
      }
    }
  }
  
  /**
   * Add attribute.
   * @param attr Attribute.
   */
  public void addAttribute(final Attribute attr) {
    final String name = attr.getName();
    if (fAttributes.get(name) == null) {
      fAttributes.put(name, new LinkedList<Attribute>());
    }
    fAttributes.get(name).add(attr);
  }
  
  /**
   * Method used to iterate over all attributes.
   * @return Iterator.
   */
  public Iterator<Attribute> iterator() {
    return new FlattenIterator<Attribute>(
        new MappedIterator<List<Attribute>, Iterator<Attribute>>(
          fAttributes.values().iterator(),
          new GetIterator<Attribute>()
      )
    );   
  }
  
  /**
   * Count all attributes.
   * @return Total number of attributes.
   */
  public int size() {
    int c = 0;
    final Iterator<List<Attribute>> i = 
      fAttributes.values().iterator();
    while (i.hasNext()) {
      c = c + i.next().size();
    }
    return c;
  }
}
