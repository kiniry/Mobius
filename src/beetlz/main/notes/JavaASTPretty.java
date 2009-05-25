package pretty;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.Writer;
import java.util.HashMap;
import java.util.Map;
import java.util.SortedSet;
import java.util.Vector;

import javax.swing.JOptionPane;
import main.Beetlz;

import org.jmlspecs.openjml.JmlPretty;
import org.jmlspecs.openjml.JmlSpecs;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.Main;
import org.jmlspecs.openjml.JmlSpecs.TypeSpecs;
import org.jmlspecs.openjml.JmlTree.JmlClassDecl;
import org.jmlspecs.openjml.JmlTree.JmlCompilationUnit;

import com.sun.tools.javac.code.Symtab;
import com.sun.tools.javac.code.Symbol.PackageSymbol;
import com.sun.tools.javac.jvm.ClassReader;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCAnnotation;
import com.sun.tools.javac.tree.JCTree.JCClassDecl;
import com.sun.tools.javac.tree.JCTree.JCExpression;
import com.sun.tools.javac.tree.JCTree.JCMethodDecl;
import com.sun.tools.javac.tree.JCTree.JCModifiers;
import com.sun.tools.javac.tree.JCTree.JCTypeParameter;
import com.sun.tools.javac.tree.JCTree.JCVariableDecl;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.Name;

import structure.ClassCollection;
import structure.ClassStructure;
import structure.FeatureStructure;
import utils.Helper;
import utils.smart.GenericParameter;
import utils.smart.SmartString;
import utils.PrettyFormatter;

/**
 * @author evka
 *
 */
public class JavaASTPretty {
  
  private Writer out;
  private Map < String, JCTree > my_trees;
  private JmlTree.Maker factory;
  private Context context;
  private JmlPretty printer;
  private Name.Table nameTable;
  private PrettyUtils xxUtil;
  private Symtab symtab;
  private ClassReader reader;
 
  
  //TODO: adjust indentation and other settings
  public JavaASTPretty(Writer a_writer) {
    out = a_writer;
    my_trees = new HashMap < String, JCTree >();
    
    try {
      Main m = new Main(new String[0]);
      context = m.context();
      factory = (JmlTree.Maker)JmlTree.Maker.instance(context);
      JmlPretty printer = (JmlPretty)JmlPretty.instance(out, true);
      nameTable = Name.Table.instance(context);
      xxUtil = new PrettyUtils(factory, nameTable);
      symtab = Symtab.instance(context);
      reader = ClassReader.instance(context);
    }
    catch (Exception e) {
      e.printStackTrace();
    }
  }

  public void printToFiles(String dir, ClassCollection the_classes) {
    my_trees = this.createTreesFromClasses(the_classes);
    JOptionPane.showMessageDialog(null, "I am happy."); //$NON-NLS-1$
    //Check that the directory exists
    File file=new File(dir);
    if (!file.exists()) {
      Beetlz.java_logger.severe("The directory you specified " + //$NON-NLS-1$
          "for your skeleton code does not exists.");          //$NON-NLS-1$
      return;
    }
    
    for (String fileName: my_trees.keySet()) {
      JCTree tree  = my_trees.get(fileName);
      try {
        //TODO: OS independent file path
        BufferedWriter out = new BufferedWriter(new FileWriter(dir + "/" + fileName)); //$NON-NLS-1$
        out.write("Hello pretty."); //$NON-NLS-1$
        out.close();
      } 
      catch (IOException e) {
        
      } 
    
    }
      
  }
      
  
  public void printClassCollection(ClassCollection the_classes) {
    my_trees = this.createTreesFromClasses(the_classes);
    try {
      for (String fileName: my_trees.keySet()) {
        JCTree tree  = my_trees.get(fileName);
        String s = printer.write(tree);
        System.out.println(s);
      }
   
    }
    catch (Exception e) {
      System.err.println("Error using OpenJML in JavaPretty."); //$NON-NLS-1$
      e.printStackTrace();
    }
   
  }
  
  
  public Map < String, JCTree > createTreesFromClasses(ClassCollection the_classes) {
    
    Map < String, JCTree > trees = new HashMap < String, JCTree >();
    Vector < JCTree > list = new Vector < JCTree>();
    for (ClassStructure c: the_classes.getClasses()) {
      List<JCAnnotation> ann = List.nil();
      List < JCTree > cls = List.of((JCTree)xxClassDef(c));
      JmlCompilationUnit unit = (JmlCompilationUnit) factory.TopLevel(ann, null, cls);
      
      list.add(unit);
      //JCFieldAccess pid = factory.Select(selected, selector);
      /*JmlCompilationUnit unit = factory.TopLevel(List<JCAnnotation> packageAnnotations,
               JCExpression pid,
               List<JCTree> defs)
      */
      trees.put(PrettyFormatter.getFileName(c)[1], unit);
      
      /*JCTree cls = xxClassDef(c);
      List<JCTree> list = List.of(cls);
      List<JCAnnotation> ann = List.of(factory.Annotation(Attribute.Class));
      trees.put(xxUtil.getFileName(c), 
                new JmlTree.JmlCompilationUnit(ann, null,  list,null, ((JmlClassDecl)cls).sym.owner, 
                                          null, null);*/
    }
    
   
    
    return trees;
  }
  
    
  private JCClassDecl xxClassDef(ClassStructure cls) {
    JCModifiers mods = factory.Modifiers(xxClassFlags(cls));
    Name name = xxUtil.getObjectName(cls.getName());
    Name packageName = nameTable.fromString("zoo"); //$NON-NLS-1$
    List < JCTypeParameter > typarams = xxTypeParams(cls);
    JCTree extending = xxExtending(cls);
    List < JCExpression > implementing = xxImplementing(cls);
    List < JCTree > defs = xxMethods(cls);
    defs = defs.appendList(xxConstructors(cls));
    JmlClassDecl cl = (JmlClassDecl) factory.ClassDef(mods, name, typarams, extending, implementing, defs);
    PackageSymbol pack = reader.enterPackage(packageName);
    cl.sym = reader.enterClass(name, pack);
    System.err.println(cl.sym);
    TypeSpecs specs = new TypeSpecs();
    JmlSpecs.instance(context).putSpecs(cl.sym, specs);
    //cl.typeSpecs = new TypeSpecs();
    return cl;
  }
    
  private long xxClassFlags (ClassStructure cls) {
    /* Modifier flags:
     * public 1, private 2, protected 4
     * abstract 1024, interface 512, enum 16384 (1<<14), annotation 8192 (1<<13)
     * final 16, static 8
     * native 256, strictfp 2048, synchronized 32, transient 128, volatile 64 
     */
    long flags = 0;
    if (cls.isPublic()) {
      flags += 1;
    }
    else if (cls.isProtected()) {
      flags += 4;
    }
    else if (cls.isPrivate()) {
      flags += 2;
    }
    //else if(cls.isPackagePrivate())
    
    if (cls.isEnum() || Helper.qualifiesAsEnum(cls)) {
      flags += 16384;
    }
    else if (cls.isInterface()) {
      flags += 512;
    }
    else if (cls.isAbstract()) {
      flags += 1024;
    }
    
    return flags;
    
    /*if (cls.isPersistent())
    if(cls.isRestricted())
    if(cls.isRoot())*/
    
  }
    
  private JCTree xxExtending(ClassStructure cls) {
    //TODO: we need to decide which class we choose for extension...
    return null;
  }
  
  private List < JCTypeParameter> xxTypeParams(ClassStructure cls) {
    if (cls.isGeneric()) {
      Vector < JCTypeParameter> typeParams = new Vector < JCTypeParameter >(); 
      for (SmartString str: cls.getGenerics()) {
        GenericParameter p = (GenericParameter) str; 
        //System.err.println(p.toString());
        Name name = nameTable.fromString(p.getDummyName());
        List < JCExpression > list = List.nil();
        if (p.isParametrized()) {
          Vector < JCExpression > bounds = new Vector < JCExpression >();
          for (SmartString s: p.getTypes()) {
            JCExpression b = xxUtil.getObjectType(s);
            bounds.add(b);
          }
          list = xxUtil.createList(bounds);
        }
        JCTypeParameter type = factory.TypeParameter(name, list);
        typeParams.add(type);
      }
      return xxUtil.createTypeParamList(typeParams);
      
    }
    else {
      return List.nil();
    }
    
    
  }
  
  private List < JCExpression> xxImplementing(ClassStructure cls) {
    SortedSet < SmartString > intf = cls.getInterfaces();
    Vector < JCExpression > interfaces = new Vector < JCExpression >();
    if (intf.size() > 0) {
      for (SmartString s: intf) {
        //JCExpression i = factory.Ident(nameTable.fromString(util.formatJava(s.toString())));   
        JCExpression i = xxUtil.getObjectType(s);
        interfaces.add(i);
      }
    }
    return xxUtil.createList(interfaces);
  }
  
  private List < JCTree> xxMethods(ClassStructure cls) {
    Vector < JCTree > features = new Vector < JCTree >();
    
    for (FeatureStructure feature: cls.getFeatures()) {
      Map < String, SmartString > params = feature.getSignature().getFormalParameter();
      JCModifiers mods = factory.Modifiers(xxMethodModifier(feature));
      Name name = nameTable.fromString(feature.getSimpleName());
      JCExpression returnType = xxUtil.getGeneralType(feature.getSignature().getReturnValue());
      JCExpression init = null;
      
      //queries with no params are translated as public fields, for now
      if (feature.isQuery() && params.isEmpty()) {
        //VariableDecl: JCModifiers mods, Name name, JCExpression vartype, JCExpression init
        JCVariableDecl variable = factory.VarDef(mods, name, returnType, init); 
        features.add(variable);
      }
      //queries with params are translated as pure methods
      else if (feature.isQuery()) {
        //JCModifiers mods, Name name, JCExpression restype, List<JCTypeParameter> typarams,
        //List<JCVariableDecl> params, List<JCExpression> thrown, JCBlock body,
        //JCExpression defaultValue
        List<JCExpression> thrown = List.nil();
        List<JCTypeParameter> typarams = List.nil();
        Vector < JCVariableDecl > parameter = new Vector < JCVariableDecl >();
        for(String s: params.keySet()) {
          JCExpression type = xxUtil.getGeneralType(params.get(s));
          Name n = nameTable.fromString(s);
          JCVariableDecl var = factory.VarDef(factory.Modifiers(0), n, type, null);
          parameter.add(var);
        }
        
        JCMethodDecl method = factory.MethodDef(mods, name, returnType, typarams, 
                                                 xxUtil.createVariableDeclList(parameter), 
                                                 thrown, null, null);
        features.add(method);
      }
      //commands are normal methods, and so are mixins
      else {
        List<JCExpression> thrown = List.nil();
        List<JCTypeParameter> typarams = List.nil();
        Vector < JCVariableDecl > parameter = new Vector < JCVariableDecl >();
        for(String s: params.keySet()) {
          JCExpression type = xxUtil.getGeneralType(params.get(s));
          Name n = nameTable.fromString(s);
          JCVariableDecl var = factory.VarDef(factory.Modifiers(0), n, type, null);
          parameter.add(var);
        }
        
        JCMethodDecl method = factory.MethodDef(mods, name, returnType, typarams, 
                                                 xxUtil.createVariableDeclList(parameter), 
                                                 thrown, null, null);
        features.add(method);
      }
    }
    return xxUtil.createJCTreeList(features);
  }
  
  private List < JCTree> xxConstructors(ClassStructure cls) {
    Vector < JCTree > features = new Vector < JCTree >();
    
    for (FeatureStructure feature: cls.getConstructors()) {
      Map < String, SmartString > params = feature.getSignature().getFormalParameter();
      JCModifiers mods = factory.Modifiers(xxMethodModifier(feature));
      Name name = nameTable.init;
      JCExpression returnType = xxUtil.getGeneralType(feature.getSignature().getReturnValue());
      JCExpression init = null;
      
      List<JCExpression> thrown = List.nil();
      List<JCTypeParameter> typarams = List.nil();
      Vector < JCVariableDecl > parameter = new Vector < JCVariableDecl >();
      for(String s: params.keySet()) {
        JCExpression type = xxUtil.getGeneralType(params.get(s));
        Name n = nameTable.fromString(s);
        JCVariableDecl var = factory.VarDef(factory.Modifiers(0), n, type, null);
        parameter.add(var);
      }
      
      JCMethodDecl method = factory.MethodDef(mods, name, returnType, typarams, 
                                               xxUtil.createVariableDeclList(parameter), 
                                               thrown, null, null);
      features.add(method);
    }
    return xxUtil.createJCTreeList(features);
  }
  
  private long xxMethodModifier(FeatureStructure f) {
    long flags = 0;
    if (f.isPublic()) {
      flags += 1;
    }
    else if (f.isProtected()) {
      flags += 4;
    }
    else if (f.isPrivate()) {
      flags += 2;
    }
    else if (f.isRestricted()) {
      flags += 1; //TODO: this is not correct...
    }
    
    if (f.isAbstract()) {
      flags += 1024;
    }
    
    return flags;
  }
  
  
  
  
  
}
