/* Copyright 2000, 2001, Compaq Computer Corporation */
/* Copyright 2007, Systems Research Group, University College Dublin, Ireland */


/*
 * ========================================================================= 
 * BCELAdaptor.java
 * (derived from ASTClassFileParser.java)
 * =========================================================================
 */

package javafe.reader;

import java.io.DataInput;
import java.io.DataInputStream;
import java.io.IOException;
import java.util.Vector;

import javafe.ast.BlockStmt;
import javafe.ast.ClassDecl;
import javafe.ast.CompilationUnit;
import javafe.ast.ConstructorDecl;
import javafe.ast.FieldDecl;
import javafe.ast.FormalParaDecl;
import javafe.ast.FormalParaDeclVec;
import javafe.ast.Identifier;
import javafe.ast.ImportDeclVec;
import javafe.ast.InterfaceDecl;
import javafe.ast.LexicalPragma;
import javafe.ast.LexicalPragmaVec;
import javafe.ast.LiteralExpr;
import javafe.ast.MethodDecl;
import javafe.ast.Modifiers;
import javafe.ast.Name;
import javafe.ast.PrettyPrint;
import javafe.ast.RoutineDecl;
import javafe.ast.StmtVec;
import javafe.ast.TagConstants;
import javafe.ast.TypeDecl;
import javafe.ast.TypeDeclElem;
import javafe.ast.TypeDeclElemVec;
import javafe.ast.TypeDeclVec;
import javafe.ast.TypeName;
import javafe.ast.TypeNameVec;
import javafe.genericfile.GenericFile;
import javafe.genericfile.NormalGenericFile;
import javafe.util.Location;

import com.sun.org.apache.bcel.internal.Constants;
import com.sun.org.apache.bcel.internal.classfile.ClassParser;
import com.sun.org.apache.bcel.internal.classfile.Field;
import com.sun.org.apache.bcel.internal.classfile.JavaClass;
import com.sun.org.apache.bcel.internal.classfile.Method;

/*
 * ------------------------------------------------------------------------- 
 * BCELAdaptor (derived from ASTClassFileParser)
 * -------------------------------------------------------------------------
 */

/**
 * Parses the contents of a class file into an AST for the purpose of type checking. Ignores
 * components of the class file that have no relevance to type checking (e.g. method bodies).
 */

class BCELReader extends Reader {
   /* -- package instance methods ------------------------------------------- */

   /**
    * The package name of the class being parsed. Initialized by constructor (by way of
    * set_this_class)
    */
   public Name classPackage;

   /**
    * The AST of the class parsed by this parser. Initialized by constructor (by way of
    * parse_file).
    */
   // @ invariant typeDecl != null;
   // @ invariant typeDecl.specOnly;
   public TypeDecl typeDecl;

   /**
    * A dummy location representing the class being parsed. Initialized by constructor.
    */
   // @ invariant classLocation != Location.NULL;
   public int classLocation;

   /**
    * The BCEL representation of the binary classfile.
    */
   protected JavaClass javaClass;

   /* -- protected instance methods ----------------------------------------- */

   /**
    * Add only AST nodes that are not synthetic decls to v. nodes should be an array of
    * TypeDeclElems. A synthetic decl is one that had the synthetic attribute, or is a static
    * method decl for an interface.
    */
   protected void addNonSyntheticDecls(/* @ non_null */TypeDeclElemVec v,
   /* @ non_null */TypeDeclElem[] elems) {
      for (int i = 0; i < elems.length; i++) {
         if (synthetics.contains(elems[i])) { // @ nowarn;
            continue;
         }
         if ((javaClass.isInterface()) && elems[i] instanceof RoutineDecl) {
            RoutineDecl rd = (RoutineDecl) elems[i];
            if (Modifiers.isStatic(rd.modifiers)) {
               continue;
            }
         }
         if (omitPrivateFields && elems[i] instanceof FieldDecl) {
            if (Modifiers.isPrivate(((FieldDecl) elems[i]).modifiers)) {
               continue;
            }
         }
         v.addElement(elems[i]); // @ nowarn Pre;
      }
   }

   /**
    * Vector of methods and fields with Synthetic attributes. Use this to weed out synthetic
    * while constructing TypeDecl.
    */
   private/* @ non_null */Vector synthetics = new Vector();

   /**
    * Flag indicating whether the class being parsed has the synthetic attribute.
    */
   private boolean syntheticClass = false;

   protected boolean includeBodies;

   protected boolean omitPrivateFields = true;

   /**
    * Load a BCEL representation of a binary classfile.  
    * 
    * @param inputFile
    *           the name of the binary classfile
    * @param includeBodies 
    *           if true, bodies are included, if not, only a spec is produced
    * @throws IOException 
    */
   protected BCELReader(GenericFile inputFile, boolean includeBodies) throws IOException {
      
      this.includeBodies = includeBodies;
      this.classLocation = Location.createWholeFileLoc(inputFile);
      
//    Parse the class file using the BCEL parser
      ClassParser classParser = new ClassParser(inputFile.getInputStream(), inputFile
            .getLocalName());
      this.javaClass = classParser.parse();


   }

   /**
    * Load a BCEL representation of a binary classfile. 
    * 
    *  
    * @param inputFile
    *           the name of the binary classfile
    * @param includeBodies 
    *           if true, bodies are included, if not, only a spec is produced
    * @throws IOException 
    * @throws ClassFormatError 
    */
   public static BCELReader make(GenericFile inputFile, boolean includeBodies) throws ClassFormatError, IOException {
      return new BCELReader(inputFile, includeBodies);
   }

   /**
    * Binary inner class constructors have an extra initial argument to their constructors (the
    * enclosing class). This is not present in the source file. To make the AST generated by
    * reading the binary correspond to that obtained from a source file, we remove that extra
    * argument for each inner (non-static) class. Since we do this at the end of parse_file,
    * each nested class does this for its own direct inner classes. - DRCok
    */
   protected void removeExtraArg() {
      TypeDeclElemVec vv = typeDecl.elems;
      for (int k = 0; k < vv.size(); ++k) {
         if (!(vv.elementAt(k) instanceof ClassDecl))
            continue;
         ClassDecl cd = (ClassDecl) vv.elementAt(k);
         if (Modifiers.isStatic(cd.modifiers))
            continue;
         TypeDeclElemVec v = cd.elems;
         for (int j = 0; j < v.size(); ++j) {
            if (!(v.elementAt(j) instanceof ConstructorDecl))
               continue;
            ConstructorDecl cdl = (ConstructorDecl) v.elementAt(j);
            cdl.args.removeElementAt(0);
         }
      }
   }

   /**
    * Convert the BCEL JavaClass format into an abstract syntax tree of a 
    * compilation unit suitable for extended static checking.
    * 
    * @author dermotcochran
    * @return An abstract syntax tree of a compilation unit.
    */

   public CompilationUnit read() {

      int loc = javaClass.getClassNameIndex();
      Name pkgName = Name.make(javaClass.getPackageName(), 1);
      TypeDeclElemVec otherPragmas = extractTypeDeclElemVec(javaClass);
      ImportDeclVec imports = extractImportDeclVec(javaClass);
      TypeDeclVec elems = extractTypeDeclVec(javaClass);

      int[] interfaces = javaClass.getInterfaces();
      TypeNameVec interfaceVec = TypeNameVec.make(interfaces.length); // @ nowarn Pre
      set_num_interfaces (interfaces.length);
      
      Method[] methods = javaClass.getMethods();

      for (int loopVar = 0; loopVar < methods.length; loopVar++) {
         int mod = 0;
         Method method = methods[loopVar];
         set_method(loopVar, method.getName(), method.getSignature(), mod);
         routineDecl[loopVar].body = // @ nowarn Null, IndexTooBig;
         BlockStmt.make(StmtVec.make(), classLocation, classLocation);
         routineDecl[loopVar].locOpenBrace = classLocation;
      }

      Field[] fields = javaClass.getFields();
      int predict = classMembers.size() + methods.length + fields.length;
      TypeDeclElemVec elementVec = TypeDeclElemVec.make(predict);

      elementVec.append(classMembers);

      // only add routines and fields that are not synthetic.
      this.addNonSyntheticDecls(elementVec, routineDecl);
      this.addNonSyntheticDecls(elementVec, fieldDecl);

      // @ assume classIdentifier != null;
      if ((javaClass.isInterface())) {
         typeDecl = (TypeDecl) InterfaceDecl.make(modifiers, null, classIdentifier,
               interfaceVec, null, elementVec, classLocation, classLocation, classLocation,
               classLocation);
      } else {
         typeDecl = (TypeDecl) ClassDecl.make(modifiers, null, classIdentifier, interfaceVec,
               null, elementVec, classLocation, classLocation, classLocation, classLocation,
               super_class);
      }
      typeDecl.specOnly = true;
      
      removeExtraArg();


      // Return
      TypeDeclVec types = TypeDeclVec.make(new TypeDecl[] { typeDecl });
      TypeDeclElemVec emptyTypeDeclElemVec = TypeDeclElemVec.make();
      ImportDeclVec emptyImportDeclVec = ImportDeclVec.make();
      CompilationUnit result = CompilationUnit.make(pkgName, null, emptyImportDeclVec, types,
            loc, emptyTypeDeclElemVec);
      return result;
   }

   protected int extractLocation(JavaClass javaClass) {
      int loc = javaClass.getClassNameIndex();
      return loc;
   }

   protected ImportDeclVec extractImportDeclVec(JavaClass javaClass) {
      ImportDeclVec importDeclVec = ImportDeclVec.make();
      return importDeclVec;
   }

   protected TypeDeclVec extractTypeDeclVec(JavaClass javaClass) {
      TypeDeclVec typeDeclVec = TypeDeclVec.make();

      return typeDeclVec;
   }

   protected TypeDeclElemVec extractTypeDeclElemVec(JavaClass javaClass) {
      TypeDeclElemVec typeDeclElemVec = TypeDeclElemVec.make();

      return typeDeclElemVec;
   }

   /* -- protected instance methods ----------------------------------------- */

   /**
    * Add only AST nodes that are not synthetic decls to v. nodes should be an array of
    * TypeDeclElems. A synthetic decl is one that had the synthetic attribute, or is a static
    * method decl for an interface.
    */
   protected void addNonSyntheticDecls(/* @ non_null */TypeDeclElemVec v,
   /* @ non_null */TypeDeclElem[] elems, JavaClass javaClass) {
      for (int i = 0; i < elems.length; i++) {
         if (synthetics.contains(elems[i])) { // @ nowarn;
            continue;
         }
         if ((javaClass.isInterface()) && elems[i] instanceof RoutineDecl) {
            RoutineDecl rd = (RoutineDecl) elems[i];
            if (Modifiers.isStatic(rd.modifiers)) {
               continue;
            }
         }
         if (omitPrivateFields && elems[i] instanceof FieldDecl) {
            if (Modifiers.isPrivate(((FieldDecl) elems[i]).modifiers)) {
               continue;
            }
         }
         v.addElement(elems[i]); // @ nowarn Pre;
      }
   }

 
 
    
   protected void set_num_constants(int cnum) throws ClassFormatError {
      constants = new Object[cnum];
      rawConstants = new Object[cnum];
   }

    
   protected void set_const(int i, int ctype, Object value) throws ClassFormatError {
      constants[i] = ctype == Constants.CONSTANT_Class ? // @ nowarn IndexTooBig;
      DescriptorParser.parseClass((String) value)
            : value;
      rawConstants[i] = value;
   }

    
   protected void set_const_ref(int i, int ctype, int class_index, String field_name,
         String type) throws ClassFormatError {
      // don't need ref constants
   }

    
   protected void set_class_attribute(/* @non_null */String aname,
   /* @non_null */DataInput stream, int n) throws IOException, ClassFormatError {
      if (aname.equals("Synthetic")) {
         syntheticClass = true;
      } else if (!aname.equals("InnerClasses")) {
         stream.skipBytes(n);
      } else {
         int num_classes = stream.readUnsignedShort();
         for (int j = 0; j < num_classes; j++) {
            int inner = stream.readUnsignedShort();
            // @ assume inner < constants.length; // property of class files
            int outer = stream.readUnsignedShort();
            int name = stream.readUnsignedShort();
            // @ assume name < constants.length; // property of class files
            int flags = stream.readUnsignedShort();
            // System.out.println("PPP" + Modifiers.toString(flags));
            if (outer == this_class_index && name != 0) {
               // We've found a member that needs to be parsed...
               if (!(rawConstants[name] instanceof String)) {
                  throw new ClassFormatError("bad constant reference");
               }
               // @ assume rawConstants[inner] instanceof String; // property of class files
               String nm = (String) rawConstants[inner];
               int i = nm.lastIndexOf("/");
               String icfn = (i < 0 ? nm : nm.substring(i + 1)) + ".class";
               GenericFile icf = inputFile.getSibling(icfn);
               if (icf == null) {
                  throw new IOException(icfn + ": inner class not found");
               }
               BCELReader parser = BCELReader.make(icf, true);

               if (Modifiers.isPublic(parser.typeDecl.modifiers)) {
               }

               // Only add classes that are not synthetic and are not anonymous inner classes,
               // which are identified by names that start with a number.
               if (!parser.syntheticClass
                     && !Character.isDigit(parser.typeDecl.id.toString().charAt(0))) {
                  classMembers.addElement(parser.typeDecl);
               }
            }
         }
      }
   }

       protected void set_this_class(int cindex) throws ClassFormatError {
      // record the class type and synthesize a location for the class binary

      TypeName typeName = (TypeName) constants[cindex]; // @ nowarn Cast, IndexTooBig;
      // @ assume typeName != null;

      Name qualifier = getNameQualifier(typeName.name);
      Identifier terminal = getNameTerminal(typeName.name);

      this_class_index = cindex;
      // this_class = typeName;
      classPackage = qualifier;
      classIdentifier = terminal;

      // This is not the correct location; it may be useful later, though.
      // int location = Location.createWholeFileLoc(terminal+".java");
      // classLocation = location;

      DescriptorParser.classLocation = classLocation;
   }

 
   protected void set_super_class(int cindex) throws ClassFormatError {
      super_class = (TypeName) constants[cindex]; // @ nowarn Cast, IndexTooBig;
   }

   /**
    * Call back from ClassFileParser.
    */
   protected void set_num_interfaces(int n) throws ClassFormatError {
      typeNames = new TypeName[n];
   }

   /**
    * Call back from ClassFileParser.
    */
   protected void set_interface(int index, int cindex) throws ClassFormatError {
      typeNames[index] = (TypeName) constants[cindex]; // @ nowarn Cast,IndexTooBig;
   }

   /**
    * Call back from ClassFileParser.
    */
   protected void set_num_fields(int n) throws ClassFormatError {
      fieldDecl = new FieldDecl[n];
   }

   /**
    * Call back from ClassFileParser.
    */
   protected void set_field(int i, String fname, String type, int mod) throws ClassFormatError {
      fieldDecl[i] = // @ nowarn IndexTooBig;
      FieldDecl.make(mod, null, Identifier.intern(fname), DescriptorParser.parseField(type),
            classLocation, null, classLocation);
   }

   /**
    * Call back from ClassFileParser.
    */
   protected void set_field_initializer(int i, Object value) throws ClassFormatError {
      // construct a literal expression for the initializer

      FieldDecl field = fieldDecl[i]; // @ nowarn IndexTooBig;
      // @ assume field != null ;

      int tag;
      Object literal;

      switch (field.type.getTag()) {
      case TagConstants.BOOLEANTYPE:
         tag = TagConstants.BOOLEANLIT;
         literal = Boolean.valueOf(((Integer) value).intValue() != 0); // @ nowarn Cast,Null;
         break;

      case TagConstants.INTTYPE:
      case TagConstants.BYTETYPE:
      case TagConstants.SHORTTYPE:
         tag = TagConstants.INTLIT;
         literal = (Integer) value; // @ nowarn Cast;
         break;

      case TagConstants.LONGTYPE:
         tag = TagConstants.LONGLIT;
         literal = (Long) value; // @ nowarn Cast;
         break;

      case TagConstants.CHARTYPE:
         tag = TagConstants.CHARLIT;
         literal = (Integer) value; // @ nowarn Cast;
         break;

      case TagConstants.FLOATTYPE:
         tag = TagConstants.FLOATLIT;
         literal = (Float) value; // @ nowarn Cast;
         break;

      case TagConstants.DOUBLETYPE:
         tag = TagConstants.DOUBLELIT;
         literal = (Double) value; // @ nowarn Cast;
         break;

      default:
         tag = TagConstants.STRINGLIT;
         literal = (String) value; // @ nowarn Cast;
         break;
      }

      field.init = LiteralExpr.make(tag, literal, classLocation);
   }

    
   protected void set_num_methods(int n) throws ClassFormatError {
      routineDecl = new RoutineDecl[n];
   }

    
   /**
    * Parse a method
    * 
    * @param i
    * @param mname
    * @param sig
    * @param mod
    * @throws ClassFormatError
    */
   protected void set_method(int i, String mname, String sig, int mod) throws ClassFormatError {
      MethodSignature signature = DescriptorParser.parseMethod(sig);
      FormalParaDeclVec formalVec = FormalParaDeclVec.make(makeFormals(signature));
      BlockStmt body = null;

      if (mname.equals("<init>")) {
      RoutineDecl constructor = (RoutineDecl) ConstructorDecl
                  .make(mod, null, null, formalVec, emptyTypeNameVec, body, Location.NULL,
                        classLocation, classLocation, classLocation);
      routineDecl[i] = constructor;
      }
      else {
         
      }
      RoutineDecl otherMethod = (RoutineDecl) MethodDecl
                  .make(mod, null, null, formalVec, emptyTypeNameVec, body, Location.NULL,
                        classLocation, classLocation, classLocation, Identifier.intern(mname),
                        signature.getReturn(), classLocation);
      routineDecl[i] = otherMethod;
   }

    
 
   protected void set_method_attribute(int i, String aname, DataInput stream, int n)
         throws IOException, ClassFormatError {
      // look for the Exceptions attribute and modify the appropriate method, if
      // necessary

      if (aname.equals("Exceptions")) {
         routineDecl[i].raises = TypeNameVec.make(parseTypeNames()); // @ nowarn Null, Cast, IndexTooBig;
      } else if (aname.equals("Synthetic")) {
         synthetics.addElement(routineDecl[i]); // @ nowarn ;
      } else {
         stream.skipBytes(n);
      }
   }

   /* -- private instance variables ----------------------------------------- */

   /**
    * The input file being parsed.
    */
   /* @ non_null */GenericFile inputFile;

   /**
    * The constant pool of the class being parsed. Initialized by set_num_constants. Elements
    * initialized by set_const and set_const_ref. Dynamic element types according to constant
    * tag: UTF8 String String String Class TypeName Integer Integer Float Float Long Long
    * Double Double FieldRef null MethodRef null InterfaceMethodRef null
    */
   // @ private invariant constants != null;
   // @ private invariant \typeof(constants) == \type(Object[]);
   private Object[] constants;

   /**
    * The constant pool of the class being parsed. This array contains the constants as they
    * came out of the parser (versus translated by DescriptorParser). Initialized by set_const
    * and set_num_constants.
    */
   // @ private invariant rawConstants != null;
   // @ private invariant \typeof(rawConstants) == \type(Object[]);
   // @ private invariant constants.length == rawConstants.length;
   private Object[] rawConstants;

   /**
    * The modifiers of the class being parsed. Initialized by set_modifiers.
    */
   private int modifiers;

   /**
    * The contant pool index of this class. Initialized by set_this_class.
    */
   private int this_class_index;

   /**
    * The type name of the class being parsed. Initialized by set_this_class.
    */
   // private TypeName this_class;
   /**
    * The type name of the superclass of the class being parsed. Initialized by
    * set_super_class.
    */
   private TypeName super_class;

   /**
    * The type names of the interfaces implemented by the class being parsed. Initialized by
    * set_num_interfaces. Elements initialized by set_interface.
    */
   // @ private invariant interfaces != null;
   // @ private invariant \typeof(interfaces) == \type(TypeName[]);
   private TypeName[] typeNames;

   /**
    * The class members of the class being parsed. Intialized by set_field, set_method, and
    * set_class_attributes.
    */
   // @ invariant classMembers != null;
   TypeDeclElemVec classMembers = TypeDeclElemVec.make(0);

   /**
    * The fields of the class being parsed. Initialized by set_num_fields. Elements initialized
    * by set_field.
    */
   // @ invariant fields != null;
   // @ invariant \typeof(fields) == \type(FieldDecl[]);
   // @ spec_public
   private FieldDecl[] fieldDecl;

   /**
    * The methods and constructors of the class being parsed. Initialized by set_num_methods.
    * Elements initialized by set_method.
    */
   // @ invariant routines != null;
   // @ invariant \typeof(routines) == \type(RoutineDecl[]);
   // @ spec_public
   private RoutineDecl[] routineDecl;

   /**
    * The identifier of the class being parsed. Initialized by set_this_class.
    */
   // @ spec_public
   private Identifier classIdentifier;

   /* -- private instance methods ------------------------------------------- */

   /**
    * Parse a sequence of type names from BCEL
    * 
    * @return an array of type names
     */
   // @ requires stream != null;
   // @ ensures \nonnullelements(\result);
   // @ ensures \typeof(\result)==\type(TypeName[]);
   private TypeName[] parseTypeNames() throws ClassFormatError {
      int[] interfaces = javaClass.getInterfaces();
      int count = interfaces.length;
      TypeName[] names = new TypeName[count];

      for (int i = 0; i < count; i++) {
         int index = interfaces[i];

         if (index >= constants.length)
            throw new ClassFormatError("unknown constant");

         Object constant = constants[index];

         if (!(constant instanceof TypeName))
            throw new ClassFormatError("not a class constant");

         names[i] = (TypeName) constant;
      }

      return names;
   }

   /**
    * Construct a vector of formal parameters from a method signature.
    * 
    * @param signature
    *           the method signature to make the formal parameters from
    * @return the formal parameters
    */
   // @ requires signature != null;
   // @ ensures \nonnullelements(\result);
   // @ ensures \typeof(\result) == \type(FormalParaDecl[]);
   private FormalParaDecl[] makeFormals(MethodSignature signature) {
      int length = signature.countParameters();
      FormalParaDecl[] formals = new FormalParaDecl[length];

      for (int i = 0; i < length; i++) {
         Identifier id = Identifier.intern("arg" + i);
         formals[i] = FormalParaDecl
               .make(0, null, id, signature.parameterAt(i), classLocation);
      }

      return formals;
   }

   /* -- private class methods ---------------------------------------------- */

   /**
    * Return the package qualifier of a given name.
    * 
    * @param name
    *           the name to return the package qualifier of
    * @return the package qualifier of name
    */
   // @ requires name != null;
   private static Name getNameQualifier(Name name) {
      int size = name.size();

      return size > 1 ? name.prefix(size - 1) : null;
      // using null for the unnamed package ???
   }

   /**
    * Return the terminal identifier of a given name.
    * 
    * @param name
    *           the name to return the terminal identifier of
    * @return the terminal identifier of name
    */
   // @ requires name != null;
   private static Identifier getNameTerminal(Name name) {
      return name.identifierAt(name.size() - 1);
   }

   /* -- private class variables -------------------------------------------- */

   /**
    * An empty type name vector.
    */
   // @ invariant emptyTypeNameVec != null;
   // @ spec_public
   private static final TypeNameVec emptyTypeNameVec = TypeNameVec.make();

   /**
    * A null identifier.
    */
   /*
    * UNUSED //@ invariant nullIdentifier != null; private static final Identifier
    * nullIdentifier = Identifier.intern("");
    */
   
   /*******************************************************************************************
    * * Test methods: * *
    ******************************************************************************************/

   // @ requires \nonnullelements(args);
   public static void main(String[] args) {
      if (args.length != 1) {
         System.err.println("BCELAdaptor: <source filename>");
         System.exit(1);
      }

      GenericFile target = new NormalGenericFile(args[0]);
      BCELReader reader;
      try {
         reader = BCELReader.make(target,false);
         CompilationUnit cu = reader.read();
         if (cu != null)
            PrettyPrint.inst.print(System.out, cu);

      } catch (ClassFormatError e) {
         // TODO Auto-generated catch block
         e.printStackTrace();
      } catch (IOException e) {
         // TODO Auto-generated catch block
         e.printStackTrace();
      }

         }

   public CompilationUnit read(GenericFile target, boolean avoidSpec) {
      
      return null;
   }

}
