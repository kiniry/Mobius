/* Copyright 2000, 2001, Compaq Computer Corporation */

/* =========================================================================
 * ASTClassFileParser.java
 * ========================================================================= */

package javafe.reader;


import java.io.*;
import java.util.*;

import decsrc.util.*;

import javafe.ast.*;
import javafe.util.*;
import javafe.genericfile.GenericFile;


/* -------------------------------------------------------------------------
 * ASTClassFileParser
 * ------------------------------------------------------------------------- */

/**
 * Parses the contents of a class file into an AST for the purpose of type
 * checking.
 * Ignores components of the class file that have no relevance to type checking
 * (e.g. method bodies).
 */

class ASTClassFileParser extends ClassFileParser {

    /* -- package instance methods ------------------------------------------- */

    /**
     * The package name of the class being parsed.
     * Initialized by constructor (by way of set_this_class)
     */
    public Name classPackage;

    /**
     * The AST of the class parsed by this parser.
     * Initialized by constructor (by way of parse_file).
     */
    //@ invariant typeDecl != null;
    //@ invariant typeDecl.specOnly
    public TypeDecl typeDecl;

    /**
     * A dummy location representing the class being parsed.
     * Initialized by constructor.
     */
    //@ invariant classLocation!=Location.NULL
    public int classLocation;


    /**
     * Vector of methods and fields with Synthetic attributes.
     * Use this to weed out synthetic while constructing TypeDecl.
     */
    /*@ non_null */ private Vector synthetics = new Vector();
    
    /**
     * Flag indicating whether the class being parsed has the synthetic
     * attribute.
     */
    private boolean syntheticClass = false;

    /**
     * Parse a class into a new class parser.  Resulting class file is
     * stored in <code>typeDecl</code>; this will be a "spec only"
     * declaration.  Its package is stored in <code>classPackage</code>
     * and a location for it is stored in <code>classLocation</code>.
     * @param stream  the stream to parse the class from */
    ASTClassFileParser(/*@ non_null */ GenericFile inputFile)
	throws IOException, ClassFormatError
    {
	super();
	DataInputStream stream = null;
	try {
	    this.inputFile = inputFile;
	    this.classLocation = Location.createWholeFileLoc(inputFile);
	    stream = new DataInputStream(inputFile.getInputStream());
	    parse_file(stream);  //@ nowarn Invariant  // "parse_file" is a helper
	} finally {
	    if (stream != null) {
		try { stream.close(); }
		catch (IOException e) { }
	    }
	}
    }

    /* -- protected instance methods ----------------------------------------- */

    /**
     * Add only AST nodes that are not synthetic decls to v.
     * nodes should be an array of TypeDeclElems.  
     * A synthetic decl is one that had the synthetic attribute, 
     * or is a static method decl for an
     * interface.
     */
    protected void addNonSyntheticDecls(/*@ non_null */ TypeDeclElemVec v, 
	                                /*@ non_null */ TypeDeclElem elems[]) { 
	for (int i = 0; i < elems.length; i++) {
	    if (synthetics.contains(elems[i])) { //@ nowarn
		continue;
	    }
	    if ((modifiers & ACC_INTERFACE) != 0 &&
		elems[i] instanceof RoutineDecl) {
		RoutineDecl rd = (RoutineDecl)elems[i];
		if (Modifiers.isStatic(rd.modifiers)) {
		    continue;
		}
	    }
	    v.addElement(elems[i]);  //@ nowarn Pre
	}
    }

    /**
     * Parse the file and set <code>typeDecl</code>.
     */
    //@ also_ensures typeDecl != null
    protected void parse_file(DataInput stream)
	throws ClassFormatError, IOException
    {
	super.parse_file(stream);

	TypeNameVec interfaceVec =
	    TypeNameVec.make(interfaces); //@ nowarn Pre

	int predict = classMembers.size() + routines.length + fields.length;
	TypeDeclElemVec elementVec = TypeDeclElemVec.make(predict);

	elementVec.append(classMembers);

	// only add routines and fields that are not synthetic.
	this.addNonSyntheticDecls(elementVec, routines);
	this.addNonSyntheticDecls(elementVec, fields);
      
	//@ assume classIdentifier != null
	if ((modifiers & ACC_INTERFACE) != 0) {
	    typeDecl= (TypeDecl)InterfaceDecl.make(modifiers&~ACC_INTERFACE,
						   null, classIdentifier,
						   interfaceVec, null, elementVec,
						   classLocation, classLocation,
						   classLocation, classLocation);
	} else {
	    typeDecl= (TypeDecl)ClassDecl.make(modifiers,
					       null, classIdentifier, 
					       interfaceVec, null, elementVec,
					       classLocation, classLocation,
					       classLocation, classLocation,
					       super_class);
	}
	typeDecl.specOnly = true;
    }

    /**
     * Call back from ClassFileParser.
     */
    protected void set_version(int major, int minor)
	throws ClassFormatError
    {
	// don't need class file version
    }

    /**
     * Call back from ClassFileParser.
     */
    protected void set_num_constants(int cnum)
	throws ClassFormatError
    {
	constants = new Object[cnum];
	rawConstants = new Object[cnum];
    }

    /**
     * Call back from ClassFileParser.
     */
    protected void set_const(int i, int ctype, Object value)
	throws ClassFormatError
    {
	constants[i] = ctype==CONSTANT_Class ?	//@ nowarn IndexTooBig
	    DescriptorParser.parseClass((String)value) : value;
	rawConstants[i] = value;
    }

    /**
     * Call back from ClassFileParser.
     */
    protected void set_const_ref(int i, int ctype, int class_index,
				 String field_name, String type)
	throws ClassFormatError
    {
	// don't need ref constants
    }

    /**
     * Call back from ClassFileParser.
     */
    protected void set_class_attribute(String aname,
				       DataInput stream, int n)
	throws IOException, ClassFormatError
    {
	if (aname.equals("Synthetic")) {
	    syntheticClass = true;
	} else if (! aname.equals("InnerClasses")) {
	    super.set_class_attribute(aname, stream, n);
	} else {
	    int num_classes = stream.readUnsignedShort();
	    for (int j = 0; j < num_classes; j++) {
		int inner = stream.readUnsignedShort();
		//@ assume inner < constants.length;  // property of class files
		int outer = stream.readUnsignedShort();
		int name = stream.readUnsignedShort();
		//@ assume name < constants.length;  // property of class files
		int flags = stream.readUnsignedShort();
		//System.out.println("PPP" + Modifiers.toString(flags));
		if (outer == this_class_index && name != 0) {
		    // We've found a member that needs to be parsed...
		    if (! (rawConstants[name] instanceof String)) {
			throw new ClassFormatError("bad constant reference");
		    }
		    //@ assume rawConstants[inner] instanceof String;  // property of class files
		    String nm = (String)rawConstants[inner];
		    int i = nm.lastIndexOf("/");
		    String icfn = (i < 0 ? nm : nm.substring(i+1)) + ".class";
		    GenericFile icf = inputFile.getSibling(icfn);
		    if (icf == null) {
			throw new IOException(icfn + ": inner class not found");
		    }
		    ASTClassFileParser parser = new ASTClassFileParser(icf);
		    parser.typeDecl.modifiers |=
			(flags & ~ACC_SYNCHRONIZED & ~ACC_INTERFACE);
      
		    if (Modifiers.isPublic(parser.typeDecl.modifiers)) {
			parser.typeDecl.modifiers &= ~ACC_PROTECTED;
		    }

		    // Only add classes that are not synthetic and are not anonymous inner classes,
		    // which are identified by names that start with a number.
		    if (!parser.syntheticClass && !Character.isDigit(parser.typeDecl.id.toString().charAt(0))) {
			classMembers.addElement(parser.typeDecl);
		    }
		}
	    }
	}
    }

    /**
     * Call back from ClassFileParser.
     */
    protected void set_modifiers(int modifiers)
	throws ClassFormatError
    {
	// The synchronized bit for classes is used for other purposes:
	this.modifiers = modifiers & ~ACC_SYNCHRONIZED;
    }

    /**
     * Call back from ClassFileParser.
     */
    protected void set_this_class(int cindex)
	throws ClassFormatError
    {
	// record the class type and synthesize a location for the class binary

	TypeName   typeName  = (TypeName)constants[cindex];	//@ nowarn Cast, IndexTooBig
	//@ assume typeName!=null

	Name       qualifier = getNameQualifier(typeName.name);
	Identifier terminal  = getNameTerminal(typeName.name);

	this_class_index = cindex;
	this_class      = typeName;
	classPackage    = qualifier;
	classIdentifier = terminal;

	// This is not the correct location; it may be useful later, though.
	//    int        location  = Location.createWholeFileLoc(terminal+".java");
	//    classLocation   = location;

	DescriptorParser.classLocation = classLocation;
    }

    /**
     * Call back from ClassFileParser.
     */
    protected void set_super_class(int cindex)
	throws ClassFormatError
    {
	super_class = (TypeName)constants[cindex];	//@ nowarn Cast, IndexTooBig
    }

    /**
     * Call back from ClassFileParser.
     */
    protected void set_num_interfaces(int n)
	throws ClassFormatError
    {
	interfaces = new TypeName[n];
    }

    /**
     * Call back from ClassFileParser.
     */
    protected void set_interface(int index, int cindex)
	throws ClassFormatError
    {
	interfaces[index] = (TypeName)constants[cindex];	//@ nowarn Cast,IndexTooBig
    }

    /**
     * Call back from ClassFileParser.
     */
    protected void set_num_fields(int n)
	throws ClassFormatError
    {
	fields = new FieldDecl[n];
    }

    /**
     * Call back from ClassFileParser.
     */
    protected void set_field(int i, String fname, String type, int mod)
	throws ClassFormatError
    {
	fields[i] =			//@ nowarn IndexTooBig
	    FieldDecl.make(mod, null, Identifier.intern(fname),
			   DescriptorParser.parseField(type), classLocation,
			   null, classLocation);
    }

    /**
     * Call back from ClassFileParser.
     */
    protected void set_field_initializer(int i, Object value)
	throws ClassFormatError
    {
	// construct a literal expression for the initializer

	FieldDecl field = fields[i];		//@ nowarn IndexTooBig
	//@ assume field!=null	

	int       tag;
	Object    literal;

	switch (field.type.getTag())
	    {
	    case TagConstants.BOOLEANTYPE:
		tag     = TagConstants.BOOLEANLIT;
		literal = new Boolean(((Integer)value).intValue()!=0);	//@ nowarn Cast,Null
		break;

	    case TagConstants.INTTYPE:
	    case TagConstants.BYTETYPE:
	    case TagConstants.SHORTTYPE:
		tag     = TagConstants.INTLIT;
		literal = (Integer)value;     //@ nowarn Cast
		break;

	    case TagConstants.LONGTYPE:
		tag     = TagConstants.LONGLIT;
		literal = (Long)value;       //@ nowarn Cast
		break;

	    case TagConstants.CHARTYPE:
		tag     = TagConstants.CHARLIT;
		literal = (Integer)value;    //@ nowarn Cast
		break;

	    case TagConstants.FLOATTYPE:
		tag     = TagConstants.FLOATLIT;
		literal = (Float)value;     //@ nowarn Cast
		break;

	    case TagConstants.DOUBLETYPE:
		tag     = TagConstants.DOUBLELIT;
		literal = (Double)value;    //@ nowarn Cast
		break;

	    default:
		tag     = TagConstants.STRINGLIT;
		literal = (String)value;    //@ nowarn Cast
		break;
	    }

	field.init = LiteralExpr.make(tag, literal, classLocation);
    }

    /**
     * Call back from ClassFileParser.
     */
    protected void set_num_methods(int n)
	throws ClassFormatError
    {
	routines = new RoutineDecl[n];
    }

    /**
     * Call back from ClassFileParser.
     */
    protected void set_method(int i, String mname, String sig, int mod)
	throws ClassFormatError
    {
	MethodSignature signature =
	    DescriptorParser.parseMethod(sig);
	FormalParaDeclVec formalVec =
	    FormalParaDeclVec.make(makeFormals(signature));
	BlockStmt body = null;

	routines[i] =			//@ nowarn IndexTooBig
	    mname.equals("<init>") ?
	    (RoutineDecl)ConstructorDecl.make(
					      mod, null, null, formalVec, emptyTypeNameVec, body, Location.NULL,
					      classLocation, classLocation, classLocation) :
	    (RoutineDecl)MethodDecl.make(
					 mod, null, null, formalVec, emptyTypeNameVec, body, Location.NULL,
					 classLocation, classLocation, classLocation,
					 Identifier.intern(mname), signature.getReturn(), classLocation);
    }

    /**
     * Call back from ClassFileParser.
     */
    protected void set_method_body(int i, int max_stack, int max_local,
				   byte[] code, int num_handlers)
	throws ClassFormatError
    {
	// put in a dummy body
	routines[i].body =	//@ nowarn Null, IndexTooBig
	    BlockStmt.make(StmtVec.make(), classLocation, classLocation);
	routines[i].locOpenBrace = classLocation;
    }

    /**
     * Call back from ClassFileParser.
     */
    protected void set_method_handler(int i, int j, int start_pc, int end_pc,
				      int handler_pc, int catch_index)
	throws ClassFormatError
    {
	// don't need method handlers
    }

    /**
     * Call back from ClassFileParser.
     */
    protected void set_method_attribute(int i, String aname,
					DataInput stream, int n)
	throws IOException, ClassFormatError
    {
	// look for the Exceptions attribute and modify the appropriate method, if
	// necessary

	if (aname.equals("Exceptions")) {
	    routines[i].raises = TypeNameVec.make(parseTypeNames((DataInputStream)stream)); //@ nowarn Null, Cast, IndexTooBig
	} else if (aname.equals("Synthetic")) {
	    synthetics.addElement(routines[i]);  //@ nowarn 
	} else {
	    stream.skipBytes(n);
	}
    }

    /* -- private instance variables ----------------------------------------- */

    /**
     * The input file being parsed.
     */
    /*@ non_null */ GenericFile inputFile;

    /**
     * The constant pool of the class being parsed.
     * Initialized by set_num_constants.
     * Elements initialized by set_const and set_const_ref.
     *
     * Dynamic element types according to constant tag:
     * UTF8                String
     * String              String
     * Class               TypeName
     * Integer             Integer
     * Float               Float
     * Long                Long
     * Double              Double
     * FieldRef            null
     * MethodRef           null
     * InterfaceMethodRef  null
     */
    //@ invariant constants != null
    //@ invariant \typeof(constants) == \type(Object[])
    private Object[] constants;

    /**
     * The constant pool of the class being parsed.
     * This array contains the constants as they came out of the
     * parser (versus translated by DescriptorParser).  Initialized
     * by set_const and set_num_constants.
     */
    //@ invariant rawConstants != null
    //@ invariant \typeof(rawConstants) == \type(Object[])
    //@ invariant constants.length == rawConstants.length;
    private Object[] rawConstants;

    /**
     * The modifiers of the class being parsed.
     * Initialized by set_modifiers.
     */
    private int modifiers;

    /**
     * The contant pool index of this class.
     * Initialized by set_this_class.
     */
    private int this_class_index;

    /**
     * The type name of the class being parsed.
     * Initialized by set_this_class.
     */
    private TypeName this_class;

    /**
     * The type name of the superclass of the class being parsed.
     * Initialized by set_super_class.
     */
    private TypeName super_class;

    /**
     * The type names of the interfaces implemented by the class being parsed.
     * Initialized by set_num_interfaces.
     * Elements initialized by set_interface.
     */
    //@ invariant interfaces!=null
    //@ invariant \typeof(interfaces) == \type(TypeName[])
    private TypeName[] interfaces;

    /**
     * The class members of the class being parsed.
     * Intialized by set_field, set_method, and set_class_attributes.
     */
    //@ invariant classMembers != null
    TypeDeclElemVec classMembers = TypeDeclElemVec.make(0);

    /**
     * The fields of the class being parsed.
     * Initialized by set_num_fields.
     * Elements initialized by set_field.
     */
    //@ invariant fields!=null
    //@ invariant \typeof(fields) == \type(FieldDecl[])
    private FieldDecl[] fields;

    /**
     * The methods and constructors of the class being parsed.
     * Initialized by set_num_methods.
     * Elements initialized by set_method.
     */
    //@ invariant routines!=null
    //@ invariant \typeof(routines) == \type(RoutineDecl[])
    private RoutineDecl[] routines;

    /**
     * The identifier of the class being parsed.
     * Initialized by set_this_class.
     */
    private Identifier classIdentifier;

    /* -- private instance methods ------------------------------------------- */

    /**
     * Parse a sequence of type names from a given stream.
     * @param stream                the stream to parse the type names from
     * @return                      an array of type names
     * @exception ClassFormatError  if the type names are not class constants
     */
    //@ requires stream!=null
    //@ ensures \nonnullelements(\result)
    //@ ensures \typeof(\result)==\type(TypeName[])
    private TypeName[] parseTypeNames(DataInputStream stream)
	throws IOException, ClassFormatError
    {
	int        count = stream.readUnsignedShort();
	TypeName[] names = new TypeName[count];

	for (int i = 0; i<count; i++)
	    {
		int index = stream.readUnsignedShort();

		if (index>=constants.length)
		    throw new ClassFormatError("unknown constant");

		Object constant = constants[index];

		if (!(constant instanceof TypeName))
		    throw new ClassFormatError("not a class constant");

		names[i] = (TypeName)constant;
	    }

	return names;
    }

    /**
     * Construct a vector of formal parameters from a method signature.
     * @param signature  the method signature to make the formal parameters from
     * @return           the formal parameters
     */
    //@ requires signature!=null
    //@ ensures \nonnullelements(\result)
    //@ ensures \typeof(\result) == \type(FormalParaDecl[])
    private FormalParaDecl[] makeFormals(MethodSignature signature)
    {
	int              length  = signature.countParameters();
	FormalParaDecl[] formals = new FormalParaDecl[length];

	for (int i = 0; i<length; i++) {
	    Identifier id = Identifier.intern("arg" + i);
	    formals[i] =
		FormalParaDecl.make(0, null, id, signature.parameterAt(i),
				    classLocation);
	}

	return formals;
    }

    /* -- private class methods ---------------------------------------------- */

    /**
     * Return the package qualifier of a given name.
     * @param name  the name to return the package qualifier of
     * @return      the package qualifier of name
     */
    //@ requires name!=null
    private static Name getNameQualifier(Name name)
    {
	int size = name.size(); 

	return size>1 ? name.prefix(size-1) : null;
	// using null for the unnamed package ???
    }

    /**
     * Return the terminal identifier of a given name.
     * @param name  the name to return the terminal identifier of
     * @return      the terminal identifier of name
     */
    //@ requires name!=null
    private static Identifier getNameTerminal(Name name)
    {
	return name.identifierAt(name.size()-1);
    }

    /* -- private class variables -------------------------------------------- */

    /**
     * An empty type name vector.
     */
    //@ invariant emptyTypeNameVec!=null
    private static final TypeNameVec emptyTypeNameVec = TypeNameVec.make();

    /**
     * A null identifier.
     */
    //@ invariant nullIdentifier!=null
    private static final Identifier nullIdentifier = Identifier.intern("");

}

