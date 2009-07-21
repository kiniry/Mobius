package test;

import visitor.TranslatingVisitor;
import b2bpl.bytecode.JClassType;
import annot.bcclass.BCClass;

public class Test {
  public static void main(String[] args) throws Exception {
    String dirName = "F:\\mimuw\\OpenJml-workspace\\BmlLib-ucd\\testClasses";
    String className = "Bill";
    final BCClass clazz = new BCClass(dirName, className);
    JClassType type = new JClassType(clazz.getBCELClass().getClassName());
    TranslatingVisitor v = new TranslatingVisitor();
    v.visit(clazz);
    System.out.println(type.getDescriptor());
  }
}
