package mobius.cct.tests.mocks;

import java.io.OutputStream;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import mobius.cct.classfile.Attribute;
import mobius.cct.classfile.ClassName;
import mobius.cct.classfile.ClassVisitor;
import mobius.cct.classfile.MethodName;
import mobius.cct.classfile.MethodVisitor;
import mobius.cct.classfile.MutableClassFile;
import mobius.cct.util.VisitorException;

/**
 * Mock implementation of ClassFile.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public class MockClassFile implements MutableClassFile {
  /**
   * Class name.
   */
  private final ClassName fName;
  
  /**
   * List of class attributes.
   */
  private final List<Attribute> fClassAttributes;
  
  /**
   * Map of method attributes.
   */
  private final Map<MethodName, List<Attribute>> fMethods;
  
  /**
   * Writer.
   */
  private ClassVisitor fWriter;
  
  /**
   * Constructor - create empty class with no attributes.
   * @param name Class name. 
   */
  public MockClassFile(final ClassName name) {
    fName = name;
    fClassAttributes = new ArrayList<Attribute>();
    fMethods = new HashMap<MethodName, List<Attribute>>();
  }
  
  /**
   * Add class attribute.
   * @param attr Attribute.
   */
  public void addAttribute(final Attribute attr) {
    fClassAttributes.add(attr);
  }
  
  /**
   * Add method attribute.
   * @param m Method name.
   * @param attr Attribute.
   */
  public void addAttribute(final MethodName m,
                           final Attribute attr) {
    final List<Attribute> list;
    if (fMethods.containsKey(m)) {
      list = fMethods.get(m);
    } else {
      list = new LinkedList<Attribute>();
      fMethods.put(m, list);
    }
    list.add(attr);
  }
  
  /**
   * Visit class.
   * @param v Visitor.
   * @throws VisitorException .
   */
  public void visit(final ClassVisitor v) 
    throws VisitorException {
    
    v.begin(fName);
    final Iterator<Attribute> i = fClassAttributes.iterator();
    while (i.hasNext()) {
      v.visitAttribute(i.next());
    }
    final Iterator<MethodName> j = fMethods.keySet().iterator();
    while (j.hasNext()) {
      final MethodName m = j.next();
      final MethodVisitor mv = v.visitMethod(m);
      if (mv != null) {
        mv.begin(m);
        final Iterator<Attribute> k = fMethods.get(m).iterator();
        while (k.hasNext()) {
          mv.visitAttribute(k.next());
        }
        mv.end();
      }
    }
    v.end();
  }

  /**
   * Set writer.
   * @param w New writer.
   */
  public void setWriter(final ClassVisitor w) {
    fWriter = w;
  }
  
  /**
   * Get writer.
   * @return Writer.
   */
  public ClassVisitor getWriter(OutputStream os) {
    return fWriter;
  }

}
