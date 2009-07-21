package tests;

import java.io.File;
import java.util.LinkedList;
import java.util.List;

import jml2bml.bytecode.ClassFileLocation;
import jml2bml.bytecode.LoopDescription;
import jml2bml.bytecode.LoopDetector;
import junit.framework.TestCase;
import oldTests.ProjectDirectory;

import org.apache.bcel.generic.Instruction;
import org.apache.bcel.verifier.structurals.InstructionContext;

import annot.bcclass.BCClass;
import annot.bcclass.BCMethod;

public class LoopDetectorTests extends TestCase {
  private BCClass clazz;

  private ClassFileLocation classLoc;

  protected void setUp() {
    clazz = null;

  }

  private class MyDesc {
    public int inv;

    public int start;

    public int end;

    public MyDesc(int inv, int start, int end) {
      this.inv = inv;
      this.start = start;
      this.end = end;
    }
  }

  private List<LoopDescription> doTest() {
    final BCMethod method = clazz.getMethod(1);
    for (Instruction instr : method.getInstructions().getInstructions())
      System.out.println(instr);
    return LoopDetector.detectLoop(method);
  }

  private void compare(List<MyDesc> desc, List<LoopDescription> loops) {
    assertEquals(desc.size(), loops.size());
    for (int i = 0; i < desc.size(); i++) {
      MyDesc d = desc.get(i);
      int inv = extractLineNo(loops.get(i).getInstructionToAnnotate());
      int start = extractLineNo(loops.get(i).getLoopStart());
      int end = extractLineNo(loops.get(i).getLoopEnd());
      assertEquals(d.inv, inv);
      assertEquals(start, d.start);
      assertEquals(end, d.end);
    }
  }

  private int extractLineNo(InstructionContext instr) {
    String str = instr.toString();
    String s = str.substring(0, str.indexOf(":"));
    s = s.substring(s.lastIndexOf(" ") + 1);
    return Integer.parseInt(s);
  }

  private void mySetUp(String testName) {
    classLoc = new ClassFileLocation(ProjectDirectory.PROJECT_DIR
                                     + File.separator + "bin", "testClasses."
                                                               + testName);
    try {
      clazz = new BCClass(classLoc.getDirectoryName(), classLoc
          .getClassQualifiedName());
    } catch (Exception e) {
      System.err.println("error " + e);
    }
  }

  public void test1() {
    mySetUp("Test1");
    List<LoopDescription> loops = doTest();
    List<MyDesc> l = new LinkedList<MyDesc>();
    l.add(new MyDesc(15, 7, 15));
    compare(l, loops);
  }

  public void test2() {
    mySetUp("Test2");
    List<LoopDescription> loops = doTest();
    List<MyDesc> l = new LinkedList<MyDesc>();
    l.add(new MyDesc(36, 20, 36));
    compare(l, loops);
  }

  public void test3() {
    mySetUp("Test3");
    List<LoopDescription> loops = doTest();
    List<MyDesc> l = new LinkedList<MyDesc>();
    l.add(new MyDesc(2, 2, 5));
    compare(l, loops);
  }

  public void test4() {
    mySetUp("Test4");
    List<LoopDescription> loops = doTest();
    List<MyDesc> l = new LinkedList<MyDesc>();
    l.add(new MyDesc(2, 2, 5));
    compare(l, loops);
  }

  public void test5() {
    mySetUp("Test5");
    List<LoopDescription> loops = doTest();
    List<MyDesc> l = new LinkedList<MyDesc>();
    l.add(new MyDesc(11, 5, 11));
    compare(l, loops);
  }

  public void test6() {
    mySetUp("Test6");
    List<LoopDescription> loops = doTest();
    List<MyDesc> l = new LinkedList<MyDesc>();
    l.add(new MyDesc(2, 2, 5));
    compare(l, loops);
  }

  public void test7() {
    mySetUp("Test7");
    List<LoopDescription> loops = doTest();
    List<MyDesc> l = new LinkedList<MyDesc>();
    l.add(new MyDesc(2, 2, 8));
    compare(l, loops);
  }

  public void test8() {
    mySetUp("Test8");
    List<LoopDescription> loops = doTest();
    List<MyDesc> l = new LinkedList<MyDesc>();
    l.add(new MyDesc(21, 12, 21));
    l.add(new MyDesc(30, 7, 30));
    compare(l, loops);
  }

}
