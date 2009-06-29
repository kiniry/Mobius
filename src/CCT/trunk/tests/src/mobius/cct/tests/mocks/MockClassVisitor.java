package mobius.cct.tests.mocks;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.fail;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import mobius.cct.classfile.Attribute;
import mobius.cct.classfile.ClassFile;
import mobius.cct.classfile.ClassName;
import mobius.cct.classfile.ClassVisitor;
import mobius.cct.classfile.MethodName;
import mobius.cct.classfile.MethodVisitor;
import mobius.cct.tests.classfile.ClassFileTest;
import mobius.cct.util.VisitorException;

/**
 * A class visitor that checks if the visited class contains
 * specified set of attributes.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public class MockClassVisitor implements ClassVisitor {
  
  /**
   * All attributes.
   */
  private final List<Attribute> fAttributes;
  
  /**
   * Map of class attributes' indices.
   */
  private final Map<String, List<Integer>> fClassAttrs;
  
  /**
   * Map of method attributes.
   */
  private final Map<MethodName, 
                    Map<String, List<Integer>>> fMethodAttrs;
  
  /**
   * Set of visited certificates.
   */
  private final boolean[] fFound;
  
  /**
   * List of unexpected attributes.
   */
  private final List<String> fUnexpected;
  
  /**
   * Constructor.
   * @param f Class file with expected attributes.
   */
  public MockClassVisitor(final ClassFile f) {
    fAttributes = new ArrayList<Attribute>();
    fMethodAttrs = new HashMap<MethodName, 
                               Map<String,List<Integer>>>();
    fClassAttrs = new HashMap<String, List<Integer>>();
    try {
      f.visit(new AttributeCollector());
    } catch (Exception e) {
    }
    fFound = new boolean[fAttributes.size()];
    fUnexpected = new ArrayList<String>();
  }

  /**
   * Assert that all specified attributes were found
   * and no other attributes were encountered.
   */
  public void assertVisitOK() {
    assertEquals("Unexpected attributes: " + 
                 Arrays.toString(fUnexpected.toArray()),
                 0, 
                 fUnexpected.size());
    for (int i = 0; i < fFound.length; i++) {
      if (!fFound[i]) {
        fail("Attribute not found");
      }
    }
  }
  
  public void begin(ClassName cls) throws VisitorException {
    fUnexpected.clear();
    for (int i = 0; i < fFound.length; i++) {
      fFound[i] = false;
    }
  }

  public void end() throws VisitorException {
  }

  public void visitAttribute(Attribute attr) throws VisitorException {
    final List<Integer> list = fClassAttrs.get(attr.getName());
    if (list != null) {
      final Iterator<Integer> i = list.iterator();
      while (i.hasNext()) {
        final int index = i.next();
        if (fFound[index]) { continue; }
        final Attribute a = fAttributes.get(index);
        if (ClassFileTest.attributesEqual(attr, a)) {
          fFound[index] = true;
          return;
        }
      }
    }
    fUnexpected.add(attr.getName());
  }

  public MethodVisitor visitMethod(MethodName m) 
    throws VisitorException {
    return new MockMethodVisitor();
  }

  /**
   * Class used to visit methods.
   */
  private final class MockMethodVisitor implements MethodVisitor {

    private Map<String, List<Integer>> fMap;

    private String fMethod;
    
    public void begin(MethodName m) throws VisitorException {
      if (fMethodAttrs.containsKey(m)) {
        fMap = fMethodAttrs.get(m);
      } else {
        fMap = new HashMap<String, List<Integer>>();
      }
      fMethod = m.internalForm();
    }

    public void end() throws VisitorException {
    }

    public void visitAttribute(Attribute attr) throws VisitorException {
      final List<Integer> list = fMap.get(attr.getName());
      if (list != null) {
        final Iterator<Integer> i = list.iterator();
        while (i.hasNext()) {
          final int index = i.next();
          if (fFound[index]) { continue; }
          final Attribute a = fAttributes.get(index);
          if (ClassFileTest.attributesEqual(attr, a)) {
            fFound[index] = true;
            return;
          }
        }
      }
      fUnexpected.add(fMethod + "::" + attr.getName());
    }
    
  }
  
  /**
   * Class used to collect attributes.
   */
  private final class AttributeCollector implements ClassVisitor {

    public void begin(ClassName cls) throws VisitorException {
    }

    public void end() throws VisitorException {
    }

    public void visitAttribute(final Attribute attr) 
      throws VisitorException {
      
      final List<Integer> list;
      if (fClassAttrs.containsKey(attr.getName())) {
        list = fClassAttrs.get(attr.getName());
      } else {
        list = new LinkedList<Integer>();
        fClassAttrs.put(attr.getName(), list);
      }
      list.add(fAttributes.size());
      fAttributes.add(attr);
    }

    public MethodVisitor visitMethod(MethodName m) {
      return new MethodAttrCollector();
    }
    
    /**
     * Class used to collect method certificates.
     */
    private final class MethodAttrCollector implements MethodVisitor {

      private Map<String, List<Integer>> fMap;
      
      public void begin(MethodName m) throws VisitorException {
        if (fMethodAttrs.containsKey(m)) {
          fMap = fMethodAttrs.get(m);
        } else {
          fMap = new HashMap<String, List<Integer>>();
          fMethodAttrs.put(m, fMap);
        }
      }

      public void end() throws VisitorException {
      }

      public void visitAttribute(Attribute attr) throws VisitorException {
        final List<Integer> list;
        if (fMap.containsKey(attr.getName())) {
          list = fMap.get(attr.getName());
        } else {
          list = new LinkedList<Integer>();
          fMap.put(attr.getName(), list);
        }
        list.add(fAttributes.size());
        fAttributes.add(attr);
      }
      
    }
    
  }
}
