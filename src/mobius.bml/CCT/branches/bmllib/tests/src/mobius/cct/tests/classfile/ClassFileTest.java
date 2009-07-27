package mobius.cct.tests.classfile;

import java.io.ByteArrayOutputStream;
import java.io.FileInputStream;
import java.io.IOException;
import java.util.Arrays;

import mobius.cct.classfile.Attribute;
import mobius.cct.classfile.ClassFile;
import mobius.cct.classfile.ClassName;
import mobius.cct.classfile.ClassVisitor;
import mobius.cct.classfile.DefaultAttribute;
import mobius.cct.classfile.DefaultClassReader;
import mobius.cct.classfile.MethodName;
import mobius.cct.classfile.MutableClassFile;
import mobius.cct.tests.mocks.MockClassFile;
import mobius.cct.tests.mocks.MockClassVisitor;

import org.junit.Test;

/**
 * Tests of default implementation of class files.
 * @author Tadeusz Sznuk (ts209501@gmail.com)
 */
public class ClassFileTest {
  /**
   * Test class location.
   */
  private static final String TEST_CLASS = 
    "./tests/data/mobius/cct/classfile/DefaultClassFile.class";
  
  /**
   * Test parsing of a class file.
   */
  @Test
  public void testParse() throws Exception {
    final MockClassFile f = makeTest1();
    final MockClassVisitor v = new MockClassVisitor(f);
    final DefaultClassReader r = new DefaultClassReader();
    final ClassFile f2 = r.read(new FileInputStream(TEST_CLASS));
    f2.visit(v);
    v.assertVisitOK();
  }
  
  /**
   * Test writing.
   */
  @Test
  public void testWrite() throws Exception {
    final MockClassFile f = makeTest1();
    final MockClassVisitor v = new MockClassVisitor(f);
    final DefaultClassReader r = new DefaultClassReader();
    final MutableClassFile f2 = r.read(new FileInputStream(TEST_CLASS));
    final ByteArrayOutputStream bos = new ByteArrayOutputStream();
    final ClassVisitor w = f2.getWriter(bos);
    f2.visit(w);
    r.read(new FileInputStream(TEST_CLASS)).visit(v);
    v.assertVisitOK();
    
  }
  
  /**
   * Test equality of attributes.
   * @param attr1 First attribute.
   * @param attr2 Second attribute.
   * @return Comparison result.
   */
  public static boolean attributesEqual(final Attribute attr1,
                                        final Attribute attr2) {
    try {
      if (!attr1.getName().equals(attr2.getName())) {
        return false;
      }
      final ByteArrayOutputStream bos1 = 
        new ByteArrayOutputStream();
      final ByteArrayOutputStream bos2 = 
        new ByteArrayOutputStream();
      attr1.writeData(bos1);
      attr2.writeData(bos2);
      return 
        Arrays.equals(bos1.toByteArray(), bos2.toByteArray());
    } catch (IOException e) {
      return false;
    } catch (NullPointerException e) {
      return attr1 == null && attr2 == null;
    }
  }
  
  // GENERATED FROM CLASS FILE
  private MockClassFile makeTest1() {
    final MockClassFile result = new MockClassFile(ClassName.parseInternal("mobius.cct.classfile.DefaultClassFile"));
    final String cattr0type = "SourceFile";
    final byte[] cdata0 = new byte[]{0, -35};
    final Attribute cattr0 = new DefaultAttribute(cattr0type, cdata0);
    result.addAttribute(cattr0);
    final MethodName m0 = MethodName.get("<init>", "(Ljava/io/InputStream;)V");
    final String m0attr0type = "Code";
    final byte[] m0data0 = new byte[]{0, 5, 0, 3, 0, 0, 0, -99, 42, -73, 0, 1, -69, 0, 2, 89, 43, -73, 0, 3, 77, 44, -74, 0, 4, 18, 5, -97, 0, 13, -69, 0, 6, 89, 18, 7, -73, 0, 8, -65, 42, 42, 44, -73, 0, 9, -75, 0, 10, 42, 42, 44, -73, 0, 11, -75, 0, 12, 42, 44, -74, 0, 13, -75, 0, 14, 42, 44, -74, 0, 13, -75, 0, 15, 42, 44, -74, 0, 13, -75, 0, 16, 42, -76, 0, 16, -102, 0, 11, 42, 1, -75, 0, 17, -89, 0, 15, 42, 42, 42, -76, 0, 16, -73, 0, 18, -75, 0, 17, 42, 42, 42, -76, 0, 15, -73, 0, 18, -75, 0, 19, 42, 42, 44, -73, 0, 20, -75, 0, 21, 42, 42, 44, -73, 0, 22, -75, 0, 23, 42, 42, 44, -73, 0, 24, -75, 0, 25, 42, -69, 0, 26, 89, 44, 42, -76, 0, 12, -73, 0, 27, -75, 0, 28, -79, 0, 0, 0, 3, 0, 114, 0, 0, 0, 74, 0, 18, 0, 0, 0, -116, 0, 4, 0, -115, 0, 13, 0, -113, 0, 22, 0, -112, 0, 32, 0, -110, 0, 41, 0, -108, 0, 50, 0, -107, 0, 58, 0, -106, 0, 66, 0, -105, 0, 74, 0, -103, 0, 81, 0, -102, 0, 89, 0, -100, 0, 101, 0, -98, 0, 113, 0, -97, 0, 122, 0, -96, 0, -125, 0, -95, 0, -116, 0, -93, 0, -100, 0, -92, 0, 115, 0, 0, 0, 32, 0, 3, 0, 0, 0, -99, 0, 116, 0, 117, 0, 0, 0, 0, 0, -99, 0, 118, 0, 119, 0, 1, 0, 13, 0, -112, 0, 120, 0, 121, 0, 2, 0, 122, 0, 0, 0, 20, 0, 3, -1, 0, 32, 0, 3, 7, 0, 123, 7, 0, 124, 7, 0, 125, 0, 0, 56, 11};
    final Attribute m0attr0 = new DefaultAttribute(m0attr0type, m0data0);
    result.addAttribute(m0, m0attr0);
    final String m0attr1type = "Exceptions";
    final byte[] m0data1 = new byte[]{0, 1, 0, 127};
    final Attribute m0attr1 = new DefaultAttribute(m0attr1type, m0data1);
    result.addAttribute(m0, m0attr1);
    final MethodName m1 = MethodName.get("readVersion", "(Ljava/io/DataInputStream;)Lmobius/cct/util/Version;");
    final String m1attr0type = "Code";
    final byte[] m1data0 = new byte[]{0, 4, 0, 4, 0, 0, 0, 20, 43, -74, 0, 13, 61, 43, -74, 0, 13, 62, -69, 0, 29, 89, 29, 28, -73, 0, 30, -80, 0, 0, 0, 2, 0, 114, 0, 0, 0, 14, 0, 3, 0, 0, 0, -82, 0, 5, 0, -81, 0, 10, 0, -80, 0, 115, 0, 0, 0, 42, 0, 4, 0, 0, 0, 20, 0, 116, 0, 117, 0, 0, 0, 0, 0, 20, 0, 120, 0, 121, 0, 1, 0, 5, 0, 15, 0, -126, 0, 73, 0, 2, 0, 10, 0, 10, 0, -125, 0, 73, 0, 3};
    final Attribute m1attr0 = new DefaultAttribute(m1attr0type, m1data0);
    result.addAttribute(m1, m1attr0);
    final String m1attr1type = "Exceptions";
    final byte[] m1data1 = new byte[]{0, 1, 0, 127};
    final Attribute m1attr1 = new DefaultAttribute(m1attr1type, m1data1);
    result.addAttribute(m1, m1attr1);
    final MethodName m2 = MethodName.get("readConstantPool", "(Ljava/io/DataInputStream;)Lmobius/cct/constantpool/ConstantPool;");
    final String m2attr0type = "Code";
    final byte[] m2data0 = new byte[]{0, 3, 0, 4, 0, 0, 0, 27, -69, 0, 31, 89, -73, 0, 32, 77, 44, 43, -71, 0, 33, 2, 0, -80, 78, -69, 0, 6, 89, 18, 35, -73, 0, 8, -65, 0, 1, 0, 8, 0, 15, 0, 16, 0, 34, 0, 3, 0, 114, 0, 0, 0, 18, 0, 4, 0, 0, 0, -68, 0, 8, 0, -66, 0, 16, 0, -65, 0, 17, 0, -64, 0, 115, 0, 0, 0, 42, 0, 4, 0, 17, 0, 10, 0, -122, 0, -121, 0, 3, 0, 0, 0, 27, 0, 116, 0, 117, 0, 0, 0, 0, 0, 27, 0, 120, 0, 121, 0, 1, 0, 8, 0, 19, 0, -120, 0, -119, 0, 2, 0, 122, 0, 0, 0, 21, 0, 1, -1, 0, 16, 0, 3, 7, 0, 123, 7, 0, 125, 7, 0, -118, 0, 1, 7, 0, -117};
    final Attribute m2attr0 = new DefaultAttribute(m2attr0type, m2data0);
    result.addAttribute(m2, m2attr0);
    final String m2attr1type = "Exceptions";
    final byte[] m2data1 = new byte[]{0, 1, 0, 127};
    final Attribute m2attr1 = new DefaultAttribute(m2attr1type, m2data1);
    result.addAttribute(m2, m2attr1);
    final MethodName m3 = MethodName.get("readInterfaces", "(Ljava/io/DataInputStream;)[Lmobius/cct/classfile/ClassName;");
    final String m3attr0type = "Code";
    final byte[] m3data0 = new byte[]{0, 4, 0, 5, 0, 0, 0, 39, 43, -74, 0, 13, 61, 28, -67, 0, 36, 78, 3, 54, 4, 21, 4, 28, -94, 0, 21, 45, 21, 4, 42, 43, -74, 0, 13, -73, 0, 18, 83, -124, 4, 1, -89, -1, -21, 45, -80, 0, 0, 0, 3, 0, 114, 0, 0, 0, 26, 0, 6, 0, 0, 0, -51, 0, 5, 0, -50, 0, 10, 0, -49, 0, 19, 0, -48, 0, 31, 0, -49, 0, 37, 0, -46, 0, 115, 0, 0, 0, 52, 0, 5, 0, 13, 0, 24, 0, -114, 0, 73, 0, 4, 0, 0, 0, 39, 0, 116, 0, 117, 0, 0, 0, 0, 0, 39, 0, 120, 0, 121, 0, 1, 0, 5, 0, 34, 0, -113, 0, 73, 0, 2, 0, 10, 0, 29, 0, -112, 0, 99, 0, 3, 0, 122, 0, 0, 0, 13, 0, 2, -2, 0, 13, 1, 7, 0, -111, 1, -6, 0, 23};
    final Attribute m3attr0 = new DefaultAttribute(m3attr0type, m3data0);
    result.addAttribute(m3, m3attr0);
    final String m3attr1type = "Exceptions";
    final byte[] m3data1 = new byte[]{0, 1, 0, 127};
    final Attribute m3attr1 = new DefaultAttribute(m3attr1type, m3data1);
    result.addAttribute(m3, m3attr1);
    final MethodName m4 = MethodName.get("readFields", "(Ljava/io/DataInputStream;)[Lmobius/cct/classfile/Field;");
    final String m4attr0type = "Code";
    final byte[] m4data0 = new byte[]{0, 6, 0, 5, 0, 0, 0, 43, 43, -74, 0, 13, 61, 28, -67, 0, 37, 78, 3, 54, 4, 21, 4, 28, -94, 0, 25, 45, 21, 4, -69, 0, 37, 89, 43, 42, -76, 0, 12, -73, 0, 38, 83, -124, 4, 1, -89, -1, -25, 45, -80, 0, 0, 0, 3, 0, 114, 0, 0, 0, 26, 0, 6, 0, 0, 0, -34, 0, 5, 0, -33, 0, 10, 0, -32, 0, 19, 0, -31, 0, 35, 0, -32, 0, 41, 0, -29, 0, 115, 0, 0, 0, 52, 0, 5, 0, 13, 0, 28, 0, -114, 0, 73, 0, 4, 0, 0, 0, 43, 0, 116, 0, 117, 0, 0, 0, 0, 0, 43, 0, 120, 0, 121, 0, 1, 0, 5, 0, 38, 0, -108, 0, 73, 0, 2, 0, 10, 0, 33, 0, -107, 0, 101, 0, 3, 0, 122, 0, 0, 0, 13, 0, 2, -2, 0, 13, 1, 7, 0, -106, 1, -6, 0, 27};
    final Attribute m4attr0 = new DefaultAttribute(m4attr0type, m4data0);
    result.addAttribute(m4, m4attr0);
    final String m4attr1type = "Exceptions";
    final byte[] m4data1 = new byte[]{0, 1, 0, 127};
    final Attribute m4attr1 = new DefaultAttribute(m4attr1type, m4data1);
    result.addAttribute(m4, m4attr1);
    final MethodName m5 = MethodName.get("readMethods", "(Ljava/io/DataInputStream;)Ljava/util/Map;");
    final String m5attr0type = "Code";
    final byte[] m5data0 = new byte[]{0, 4, 0, 6, 0, 0, 0, 59, 43, -74, 0, 13, 61, -69, 0, 39, 89, 28, -73, 0, 40, 78, 3, 54, 4, 21, 4, 28, -94, 0, 37, -69, 0, 41, 89, 43, 42, -76, 0, 12, -73, 0, 42, 58, 5, 45, 25, 5, -74, 0, 43, 25, 5, -71, 0, 44, 3, 0, 87, -124, 4, 1, -89, -1, -37, 45, -80, 0, 0, 0, 4, 0, 114, 0, 0, 0, 30, 0, 7, 0, 0, 0, -18, 0, 5, 0, -17, 0, 14, 0, -15, 0, 23, 0, -14, 0, 37, 0, -13, 0, 51, 0, -15, 0, 57, 0, -11, 0, 115, 0, 0, 0, 62, 0, 6, 0, 37, 0, 14, 0, -103, 0, -102, 0, 5, 0, 17, 0, 40, 0, -114, 0, 73, 0, 4, 0, 0, 0, 59, 0, 116, 0, 117, 0, 0, 0, 0, 0, 59, 0, 120, 0, 121, 0, 1, 0, 5, 0, 54, 0, -101, 0, 73, 0, 2, 0, 14, 0, 45, 0, -100, 0, 103, 0, 3, 0, -99, 0, 0, 0, 12, 0, 1, 0, 14, 0, 45, 0, -100, 0, 105, 0, 3, 0, 122, 0, 0, 0, 13, 0, 2, -2, 0, 17, 1, 7, 0, -98, 1, -6, 0, 39};
    final Attribute m5attr0 = new DefaultAttribute(m5attr0type, m5data0);
    result.addAttribute(m5, m5attr0);
    final String m5attr1type = "Exceptions";
    final byte[] m5data1 = new byte[]{0, 1, 0, 127};
    final Attribute m5attr1 = new DefaultAttribute(m5attr1type, m5data1);
    result.addAttribute(m5, m5attr1);
    final String m5attr2type = "Signature";
    final byte[] m5data2 = new byte[]{0, -97};
    final Attribute m5attr2 = new DefaultAttribute(m5attr2type, m5data2);
    result.addAttribute(m5, m5attr2);
    final MethodName m6 = MethodName.get("parseName", "(I)Lmobius/cct/classfile/ClassName;");
    final String m6attr0type = "Code";
    final byte[] m6data0 = new byte[]{0, 3, 0, 5, 0, 0, 0, 81, 42, -76, 0, 12, 27, -71, 0, 45, 2, 0, 77, -89, 0, 14, 78, -69, 0, 6, 89, 18, 47, -73, 0, 8, -65, 44, -63, 0, 48, -102, 0, 13, -69, 0, 6, 89, 18, 47, -73, 0, 8, -65, 44, -64, 0, 48, -74, 0, 49, 62, 42, -76, 0, 12, 29, -72, 0, 50, 58, 4, 25, 4, -57, 0, 13, -69, 0, 6, 89, 18, 47, -73, 0, 8, -65, 25, 4, -72, 0, 51, -80, 0, 1, 0, 0, 0, 11, 0, 14, 0, 46, 0, 3, 0, 114, 0, 0, 0, 46, 0, 11, 0, 0, 1, 3, 0, 11, 1, 6, 0, 14, 1, 4, 0, 15, 1, 5, 0, 25, 1, 7, 0, 32, 1, 8, 0, 42, 1, 10, 0, 50, 1, 11, 0, 60, 1, 13, 0, 65, 1, 14, 0, 75, 1, 16, 0, 115, 0, 0, 0, 62, 0, 6, 0, 15, 0, 10, 0, -122, 0, -94, 0, 3, 0, 0, 0, 81, 0, 116, 0, 117, 0, 0, 0, 0, 0, 81, 0, -93, 0, 73, 0, 1, 0, 11, 0, 70, 0, -92, 0, -91, 0, 2, 0, 50, 0, 31, 0, -90, 0, 73, 0, 3, 0, 60, 0, 21, 0, -89, 0, -88, 0, 4, 0, 122, 0, 0, 0, 20, 0, 4, 78, 7, 0, -87, -4, 0, 10, 7, 0, -86, 16, -3, 0, 32, 1, 7, 0, -85};
    final Attribute m6attr0 = new DefaultAttribute(m6attr0type, m6data0);
    result.addAttribute(m6, m6attr0);
    final String m6attr1type = "Exceptions";
    final byte[] m6data1 = new byte[]{0, 1, 0, 6};
    final Attribute m6attr1 = new DefaultAttribute(m6attr1type, m6data1);
    result.addAttribute(m6, m6attr1);
    final MethodName m7 = MethodName.get("visit", "(Lmobius/cct/classfile/ClassVisitor;)V");
    final String m7attr0type = "Code";
    final byte[] m7data0 = new byte[]{0, 2, 0, 6, 0, 0, 0, 115, 43, 42, -76, 0, 19, -71, 0, 52, 2, 0, 42, -76, 0, 28, -74, 0, 53, 77, 44, -71, 0, 54, 1, 0, -103, 0, 21, 43, 44, -71, 0, 55, 1, 0, -64, 0, 56, -71, 0, 57, 2, 0, -89, -1, -24, 42, -76, 0, 25, -71, 0, 58, 1, 0, -71, 0, 59, 1, 0, 78, 45, -71, 0, 54, 1, 0, -103, 0, 42, 45, -71, 0, 55, 1, 0, -64, 0, 41, 58, 4, 43, 25, 4, -74, 0, 43, -71, 0, 60, 2, 0, 58, 5, 25, 5, -58, 0, 10, 25, 4, 25, 5, -74, 0, 61, -89, -1, -45, 43, -71, 0, 62, 1, 0, -79, 0, 0, 0, 4, 0, 114, 0, 0, 0, 54, 0, 13, 0, 0, 1, 26, 0, 10, 1, 27, 0, 18, 1, 28, 0, 27, 1, 29, 0, 45, 1, 31, 0, 60, 1, 32, 0, 69, 1, 33, 0, 80, 1, 34, 0, 93, 1, 35, 0, 98, 1, 36, 0, 105, 1, 38, 0, 108, 1, 39, 0, 114, 1, 40, 0, 115, 0, 0, 0, 62, 0, 6, 0, 80, 0, 25, 0, -103, 0, -102, 0, 4, 0, 93, 0, 12, 0, -82, 0, -81, 0, 5, 0, 0, 0, 115, 0, 116, 0, 117, 0, 0, 0, 0, 0, 115, 0, -80, 0, -79, 0, 1, 0, 18, 0, 97, 0, -78, 0, -77, 0, 2, 0, 60, 0, 55, 0, -76, 0, -77, 0, 3, 0, -99, 0, 0, 0, 22, 0, 2, 0, 18, 0, 97, 0, -78, 0, -75, 0, 2, 0, 60, 0, 55, 0, -76, 0, -74, 0, 3, 0, 122, 0, 0, 0, 17, 0, 5, -4, 0, 18, 7, 0, -73, 26, -4, 0, 14, 7, 0, -73, 44, 2};
    final Attribute m7attr0 = new DefaultAttribute(m7attr0type, m7data0);
    result.addAttribute(m7, m7attr0);
    final String m7attr1type = "Exceptions";
    final byte[] m7data1 = new byte[]{0, 1, 0, -72};
    final Attribute m7attr1 = new DefaultAttribute(m7attr1type, m7data1);
    result.addAttribute(m7, m7attr1);
    final MethodName m8 = MethodName.get("getMethod", "(Lmobius/cct/classfile/MethodName;)Lmobius/cct/classfile/Method;");
    final String m8attr0type = "Code";
    final byte[] m8data0 = new byte[]{0, 2, 0, 2, 0, 0, 0, 29, 42, -76, 0, 25, 43, -71, 0, 63, 2, 0, -103, 0, 17, 42, -76, 0, 25, 43, -71, 0, 64, 2, 0, -64, 0, 41, -80, 1, -80, 0, 0, 0, 3, 0, 114, 0, 0, 0, 14, 0, 3, 0, 0, 1, 48, 0, 13, 1, 49, 0, 27, 1, 51, 0, 115, 0, 0, 0, 22, 0, 2, 0, 0, 0, 29, 0, 116, 0, 117, 0, 0, 0, 0, 0, 29, 0, -103, 0, -69, 0, 1, 0, 122, 0, 0, 0, 3, 0, 1, 27};
    final Attribute m8attr0 = new DefaultAttribute(m8attr0type, m8data0);
    result.addAttribute(m8, m8attr0);
    final MethodName m9 = MethodName.get("getVersion", "()Lmobius/cct/util/Version;");
    final String m9attr0type = "Code";
    final byte[] m9data0 = new byte[]{0, 1, 0, 1, 0, 0, 0, 5, 42, -76, 0, 10, -80, 0, 0, 0, 2, 0, 114, 0, 0, 0, 6, 0, 1, 0, 0, 1, 60, 0, 115, 0, 0, 0, 12, 0, 1, 0, 0, 0, 5, 0, 116, 0, 117, 0, 0};
    final Attribute m9attr0 = new DefaultAttribute(m9attr0type, m9data0);
    result.addAttribute(m9, m9attr0);
    final MethodName m10 = MethodName.get("getAccessFlags", "()I");
    final String m10attr0type = "Code";
    final byte[] m10data0 = new byte[]{0, 1, 0, 1, 0, 0, 0, 5, 42, -76, 0, 14, -84, 0, 0, 0, 2, 0, 114, 0, 0, 0, 6, 0, 1, 0, 0, 1, 68, 0, 115, 0, 0, 0, 12, 0, 1, 0, 0, 0, 5, 0, 116, 0, 117, 0, 0};
    final Attribute m10attr0 = new DefaultAttribute(m10attr0type, m10data0);
    result.addAttribute(m10, m10attr0);
    final MethodName m11 = MethodName.get("getConstantPool", "()Lmobius/cct/constantpool/ConstantPool;");
    final String m11attr0type = "Code";
    final byte[] m11data0 = new byte[]{0, 1, 0, 1, 0, 0, 0, 5, 42, -76, 0, 12, -80, 0, 0, 0, 2, 0, 114, 0, 0, 0, 6, 0, 1, 0, 0, 1, 76, 0, 115, 0, 0, 0, 12, 0, 1, 0, 0, 0, 5, 0, 116, 0, 117, 0, 0};
    final Attribute m11attr0 = new DefaultAttribute(m11attr0type, m11data0);
    result.addAttribute(m11, m11attr0);
    final MethodName m12 = MethodName.get("getName", "()Lmobius/cct/classfile/ClassName;");
    final String m12attr0type = "Code";
    final byte[] m12data0 = new byte[]{0, 1, 0, 1, 0, 0, 0, 5, 42, -76, 0, 19, -80, 0, 0, 0, 2, 0, 114, 0, 0, 0, 6, 0, 1, 0, 0, 1, 84, 0, 115, 0, 0, 0, 12, 0, 1, 0, 0, 0, 5, 0, 116, 0, 117, 0, 0};
    final Attribute m12attr0 = new DefaultAttribute(m12attr0type, m12data0);
    result.addAttribute(m12, m12attr0);
    final MethodName m13 = MethodName.get("getSuperName", "()Lmobius/cct/classfile/ClassName;");
    final String m13attr0type = "Code";
    final byte[] m13data0 = new byte[]{0, 1, 0, 1, 0, 0, 0, 5, 42, -76, 0, 17, -80, 0, 0, 0, 2, 0, 114, 0, 0, 0, 6, 0, 1, 0, 0, 1, 92, 0, 115, 0, 0, 0, 12, 0, 1, 0, 0, 0, 5, 0, 116, 0, 117, 0, 0};
    final Attribute m13attr0 = new DefaultAttribute(m13attr0type, m13data0);
    result.addAttribute(m13, m13attr0);
    final MethodName m14 = MethodName.get("interfaceCount", "()I");
    final String m14attr0type = "Code";
    final byte[] m14data0 = new byte[]{0, 1, 0, 1, 0, 0, 0, 6, 42, -76, 0, 21, -66, -84, 0, 0, 0, 2, 0, 114, 0, 0, 0, 6, 0, 1, 0, 0, 1, 100, 0, 115, 0, 0, 0, 12, 0, 1, 0, 0, 0, 6, 0, 116, 0, 117, 0, 0};
    final Attribute m14attr0 = new DefaultAttribute(m14attr0type, m14data0);
    result.addAttribute(m14, m14attr0);
    final MethodName m15 = MethodName.get("getInterfaces", "()Ljava/util/Iterator;");
    final String m15attr0type = "Code";
    final byte[] m15data0 = new byte[]{0, 3, 0, 1, 0, 0, 0, 12, -69, 0, 65, 89, 42, -76, 0, 21, -73, 0, 66, -80, 0, 0, 0, 2, 0, 114, 0, 0, 0, 6, 0, 1, 0, 0, 1, 108, 0, 115, 0, 0, 0, 12, 0, 1, 0, 0, 0, 12, 0, 116, 0, 117, 0, 0};
    final Attribute m15attr0 = new DefaultAttribute(m15attr0type, m15data0);
    result.addAttribute(m15, m15attr0);
    final String m15attr1type = "Signature";
    final byte[] m15data1 = new byte[]{0, -56};
    final Attribute m15attr1 = new DefaultAttribute(m15attr1type, m15data1);
    result.addAttribute(m15, m15attr1);
    final MethodName m16 = MethodName.get("fieldCount", "()I");
    final String m16attr0type = "Code";
    final byte[] m16data0 = new byte[]{0, 1, 0, 1, 0, 0, 0, 6, 42, -76, 0, 23, -66, -84, 0, 0, 0, 2, 0, 114, 0, 0, 0, 6, 0, 1, 0, 0, 1, 116, 0, 115, 0, 0, 0, 12, 0, 1, 0, 0, 0, 6, 0, 116, 0, 117, 0, 0};
    final Attribute m16attr0 = new DefaultAttribute(m16attr0type, m16data0);
    result.addAttribute(m16, m16attr0);
    final MethodName m17 = MethodName.get("getFields", "()Ljava/util/Iterator;");
    final String m17attr0type = "Code";
    final byte[] m17data0 = new byte[]{0, 3, 0, 1, 0, 0, 0, 12, -69, 0, 65, 89, 42, -76, 0, 23, -73, 0, 66, -80, 0, 0, 0, 2, 0, 114, 0, 0, 0, 6, 0, 1, 0, 0, 1, 124, 0, 115, 0, 0, 0, 12, 0, 1, 0, 0, 0, 12, 0, 116, 0, 117, 0, 0};
    final Attribute m17attr0 = new DefaultAttribute(m17attr0type, m17data0);
    result.addAttribute(m17, m17attr0);
    final String m17attr1type = "Signature";
    final byte[] m17data1 = new byte[]{0, -54};
    final Attribute m17attr1 = new DefaultAttribute(m17attr1type, m17data1);
    result.addAttribute(m17, m17attr1);
    final MethodName m18 = MethodName.get("getMethods", "()Ljava/util/Iterator;");
    final String m18attr0type = "Code";
    final byte[] m18data0 = new byte[]{0, 1, 0, 1, 0, 0, 0, 15, 42, -76, 0, 25, -71, 0, 58, 1, 0, -71, 0, 59, 1, 0, -80, 0, 0, 0, 2, 0, 114, 0, 0, 0, 6, 0, 1, 0, 0, 1, -124, 0, 115, 0, 0, 0, 12, 0, 1, 0, 0, 0, 15, 0, 116, 0, 117, 0, 0};
    final Attribute m18attr0 = new DefaultAttribute(m18attr0type, m18data0);
    result.addAttribute(m18, m18attr0);
    final String m18attr1type = "Signature";
    final byte[] m18data1 = new byte[]{0, -52};
    final Attribute m18attr1 = new DefaultAttribute(m18attr1type, m18data1);
    result.addAttribute(m18, m18attr1);
    final MethodName m19 = MethodName.get("getAttributes", "()Ljava/util/Iterator;");
    final String m19attr0type = "Code";
    final byte[] m19data0 = new byte[]{0, 1, 0, 1, 0, 0, 0, 8, 42, -76, 0, 28, -74, 0, 53, -80, 0, 0, 0, 2, 0, 114, 0, 0, 0, 6, 0, 1, 0, 0, 1, -116, 0, 115, 0, 0, 0, 12, 0, 1, 0, 0, 0, 8, 0, 116, 0, 117, 0, 0};
    final Attribute m19attr0 = new DefaultAttribute(m19attr0type, m19data0);
    result.addAttribute(m19, m19attr0);
    final String m19attr1type = "Signature";
    final byte[] m19data1 = new byte[]{0, -50};
    final Attribute m19attr1 = new DefaultAttribute(m19attr1type, m19data1);
    result.addAttribute(m19, m19attr1);
    final MethodName m20 = MethodName.get("getWriter", "(Ljava/io/OutputStream;)Lmobius/cct/classfile/ClassVisitor;");
    final String m20attr0type = "Code";
    final byte[] m20data0 = new byte[]{0, 4, 0, 2, 0, 0, 0, 10, -69, 0, 67, 89, 42, 43, -73, 0, 68, -80, 0, 0, 0, 2, 0, 114, 0, 0, 0, 6, 0, 1, 0, 0, 1, -107, 0, 115, 0, 0, 0, 22, 0, 2, 0, 0, 0, 10, 0, 116, 0, 117, 0, 0, 0, 0, 0, 10, 0, -47, 0, -46, 0, 1};
    final Attribute m20attr0 = new DefaultAttribute(m20attr0type, m20data0);
    result.addAttribute(m20, m20attr0);
    final MethodName m21 = MethodName.get("isPublic", "()Z");
    final String m21attr0type = "Code";
    final byte[] m21data0 = new byte[]{0, 2, 0, 1, 0, 0, 0, 15, 42, -76, 0, 14, 4, 126, -103, 0, 7, 4, -89, 0, 4, 3, -84, 0, 0, 0, 3, 0, 114, 0, 0, 0, 6, 0, 1, 0, 0, 1, -99, 0, 115, 0, 0, 0, 12, 0, 1, 0, 0, 0, 15, 0, 116, 0, 117, 0, 0, 0, 122, 0, 0, 0, 5, 0, 2, 13, 64, 1};
    final Attribute m21attr0 = new DefaultAttribute(m21attr0type, m21data0);
    result.addAttribute(m21, m21attr0);
    final MethodName m22 = MethodName.get("isFinal", "()Z");
    final String m22attr0type = "Code";
    final byte[] m22data0 = new byte[]{0, 2, 0, 1, 0, 0, 0, 16, 42, -76, 0, 14, 16, 16, 126, -103, 0, 7, 4, -89, 0, 4, 3, -84, 0, 0, 0, 3, 0, 114, 0, 0, 0, 6, 0, 1, 0, 0, 1, -92, 0, 115, 0, 0, 0, 12, 0, 1, 0, 0, 0, 16, 0, 116, 0, 117, 0, 0, 0, 122, 0, 0, 0, 5, 0, 2, 14, 64, 1};
    final Attribute m22attr0 = new DefaultAttribute(m22attr0type, m22data0);
    result.addAttribute(m22, m22attr0);
    final MethodName m23 = MethodName.get("isSuper", "()Z");
    final String m23attr0type = "Code";
    final byte[] m23data0 = new byte[]{0, 2, 0, 1, 0, 0, 0, 16, 42, -76, 0, 14, 16, 32, 126, -103, 0, 7, 4, -89, 0, 4, 3, -84, 0, 0, 0, 3, 0, 114, 0, 0, 0, 6, 0, 1, 0, 0, 1, -85, 0, 115, 0, 0, 0, 12, 0, 1, 0, 0, 0, 16, 0, 116, 0, 117, 0, 0, 0, 122, 0, 0, 0, 5, 0, 2, 14, 64, 1};
    final Attribute m23attr0 = new DefaultAttribute(m23attr0type, m23data0);
    result.addAttribute(m23, m23attr0);
    final MethodName m24 = MethodName.get("isInterface", "()Z");
    final String m24attr0type = "Code";
    final byte[] m24data0 = new byte[]{0, 2, 0, 1, 0, 0, 0, 17, 42, -76, 0, 14, 17, 2, 0, 126, -103, 0, 7, 4, -89, 0, 4, 3, -84, 0, 0, 0, 3, 0, 114, 0, 0, 0, 6, 0, 1, 0, 0, 1, -78, 0, 115, 0, 0, 0, 12, 0, 1, 0, 0, 0, 17, 0, 116, 0, 117, 0, 0, 0, 122, 0, 0, 0, 5, 0, 2, 15, 64, 1};
    final Attribute m24attr0 = new DefaultAttribute(m24attr0type, m24data0);
    result.addAttribute(m24, m24attr0);
    final MethodName m25 = MethodName.get("isAbstract", "()Z");
    final String m25attr0type = "Code";
    final byte[] m25data0 = new byte[]{0, 2, 0, 1, 0, 0, 0, 17, 42, -76, 0, 14, 17, 4, 0, 126, -103, 0, 7, 4, -89, 0, 4, 3, -84, 0, 0, 0, 3, 0, 114, 0, 0, 0, 6, 0, 1, 0, 0, 1, -71, 0, 115, 0, 0, 0, 12, 0, 1, 0, 0, 0, 17, 0, 116, 0, 117, 0, 0, 0, 122, 0, 0, 0, 5, 0, 2, 15, 64, 1};
    final Attribute m25attr0 = new DefaultAttribute(m25attr0type, m25data0);
    result.addAttribute(m25, m25attr0);
    final MethodName m26 = MethodName.get("isSynthetic", "()Z");
    final String m26attr0type = "Code";
    final byte[] m26data0 = new byte[]{0, 2, 0, 1, 0, 0, 0, 17, 42, -76, 0, 14, 17, 16, 0, 126, -103, 0, 7, 4, -89, 0, 4, 3, -84, 0, 0, 0, 3, 0, 114, 0, 0, 0, 6, 0, 1, 0, 0, 1, -64, 0, 115, 0, 0, 0, 12, 0, 1, 0, 0, 0, 17, 0, 116, 0, 117, 0, 0, 0, 122, 0, 0, 0, 5, 0, 2, 15, 64, 1};
    final Attribute m26attr0 = new DefaultAttribute(m26attr0type, m26data0);
    result.addAttribute(m26, m26attr0);
    final MethodName m27 = MethodName.get("isAnnotation", "()Z");
    final String m27attr0type = "Code";
    final byte[] m27data0 = new byte[]{0, 2, 0, 1, 0, 0, 0, 17, 42, -76, 0, 14, 17, 32, 0, 126, -103, 0, 7, 4, -89, 0, 4, 3, -84, 0, 0, 0, 3, 0, 114, 0, 0, 0, 6, 0, 1, 0, 0, 1, -57, 0, 115, 0, 0, 0, 12, 0, 1, 0, 0, 0, 17, 0, 116, 0, 117, 0, 0, 0, 122, 0, 0, 0, 5, 0, 2, 15, 64, 1};
    final Attribute m27attr0 = new DefaultAttribute(m27attr0type, m27data0);
    result.addAttribute(m27, m27attr0);
    final MethodName m28 = MethodName.get("isEnum", "()Z");
    final String m28attr0type = "Code";
    final byte[] m28data0 = new byte[]{0, 2, 0, 1, 0, 0, 0, 17, 42, -76, 0, 14, 17, 64, 0, 126, -103, 0, 7, 4, -89, 0, 4, 3, -84, 0, 0, 0, 3, 0, 114, 0, 0, 0, 6, 0, 1, 0, 0, 1, -50, 0, 115, 0, 0, 0, 12, 0, 1, 0, 0, 0, 17, 0, 116, 0, 117, 0, 0, 0, 122, 0, 0, 0, 5, 0, 2, 15, 64, 1};
    final Attribute m28attr0 = new DefaultAttribute(m28attr0type, m28data0);
    result.addAttribute(m28, m28attr0);
    return result;
  }
}
