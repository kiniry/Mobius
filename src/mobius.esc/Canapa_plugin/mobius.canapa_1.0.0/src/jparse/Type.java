/*
 * @(#)$Id: Type.java,v 1.7 2004/07/14 14:50:40 bdg534 Exp $
 *
 * JParse: a freely available Java parser
 * Copyright (C) 2000,2004 Jeremiah W. James
 *
 * This library is free software; you can redistribute it and/or modify it
 * under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation; either version 2.1 of the License, or (at
 * your option) any later version.
 *
 * This library is distributed in the hope that it will be useful, but
 * WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with this library; if not, write to the Free Software Foundation,
 * Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
 *
 * Author: Jerry James
 * Email: james@eecs.ku.edu, james@ittc.ku.edu, jamesj@acm.org
 * Address: EECS Department - University of Kansas
 *          Eaton Hall
 *          1520 W 15th St, Room 2001
 *          Lawrence, KS  66045-7621
 */
package jparse;

import antlr.RecognitionException;
import antlr.TokenStreamException;
import antlr.TokenStreamHiddenTokenFilter;
import java.io.*;
import java.lang.reflect.Array;
import java.util.ArrayList;
import java.util.HashMap;

/**
 * Information on a Java type. This is either a
 * {@link jparse.SourceType SourceType}object from the Java parser or a
 * {@link jparse.CompiledType CompiledType}object representing a compiled
 * class. The static members of this class provide a type caching and lookup
 * service.
 * 
 * @version $Revision: 1.7 $, $Date: 2004/07/14 14:50:40 $
 * @author Jerry James
 */
public abstract class Type {

	// ########################### The static part ###########################

	/**
	 * The boolean type
	 */
	public static final CompiledType booleanType = new CompiledType(
			boolean.class);

	/**
	 * The byte type
	 */
	public static final CompiledType byteType = new CompiledType(byte.class);

	/**
	 * The char type
	 */
	public static final CompiledType charType = new CompiledType(char.class);

	/**
	 * The double type
	 */
	public static final CompiledType doubleType = new CompiledType(double.class);

	/**
	 * The float type
	 */
	public static final CompiledType floatType = new CompiledType(float.class);

	/**
	 * The int type
	 */
	public static final CompiledType intType = new CompiledType(int.class);

	/**
	 * The long type
	 */
	public static final CompiledType longType = new CompiledType(long.class);

	/**
	 * The short type
	 */
	public static final CompiledType shortType = new CompiledType(short.class);

	/**
	 * The void type
	 */
	public static final CompiledType voidType = new CompiledType(void.class);

	/**
	 * The object type
	 */
	public static final CompiledType objectType = new CompiledType(Object.class);

	/**
	 * The string type
	 */
	public static final CompiledType stringType = new CompiledType(String.class);

	/**
	 * A mapping from fully qualified names to <code>Type</code> objects
	 */
	protected static final HashMap map = new HashMap();

	static {
		// Seed the map with the primitive data types, Object, and String
		map.put("boolean", booleanType);
		map.put("byte", byteType);
		map.put("char", charType);
		map.put("double", doubleType);
		map.put("float", floatType);
		map.put("int", intType);
		map.put("long", longType);
		map.put("short", shortType);
		map.put("void", voidType);
		map.put("java.lang.Object", objectType);
		map.put("java.lang.String", stringType);
	}

	/**
	 * A mapping from package names to <code>File</code> objects
	 */
	protected static final HashMap pkgMap = new HashMap();

	/**
	 * A mapping from <code>File</code> objects to <code>FileAST</code>
	 * objects
	 */
	private static HashMap parsedMap = new HashMap();

	/**
	 * The classpath to use for finding classes
	 */
	private static final String[] classPath;

	static {
		final ArrayList paths = new ArrayList();
		final char sep = File.pathSeparatorChar;

		// Get the user's classpath
		explodeString(System.getProperty("env.class.path"), sep, paths);

		// Get the system class path(s)
		explodeString(System.getProperty("sun.boot.class.path"), sep, paths);
		explodeString(System.getProperty("java.class.path"), sep, paths);

		// Get the extension classes
		explodeString(System.getProperty("java.ext.dirs"), sep, paths);

		// Make an array of strings
		classPath = new String[paths.size()];
		paths.toArray(classPath);
	}

	/**
	 * Break up a string by finding the location of a certain character, and add
	 * the constituent parts to a list, if they are not already there
	 * 
	 * @param s
	 *            the string to break up
	 * @param c
	 *            the delimiting character
	 * @param list
	 *            the list to add the parts to
	 */
	private static void explodeString(final String s, final char c,
			final ArrayList list) {
		// Is it trivial?
		if (s == null || s.length() == 0)
			return;

		int start, end;
		for (start = end = 0;; start = end + 1) {
			end = s.indexOf(c, start);
			if (end < 0)
				break;
			final String part = s.substring(start, end);
			if (!list.contains(part))
				list.add(part);
			start = end + 1; // Skip the delimiting character
		}
		final String part = s.substring(start);
		if (!list.contains(part))
			list.add(part);
	}

	/**
	 * Find a file in the classpath. This routine can find either a source or a
	 * compiled file. It returns <code>null</code> if the file cannot be
	 * found.
	 * 
	 * @param name
	 *            the fully qualified name of the class to find
	 * @param source
	 *            <code>true</code> to find a source file, <code>false</code>
	 *            to find a class file
	 * @return a <code>File</code> object representing the class, or
	 *         <code>null</code> if it could not be found
	 */
	private static File findFile(final String name, final boolean source) {
		// See if the package is in the package map already
		final int index = name.lastIndexOf('.');
		final String pkgName = (index == -1) ? "" : name.substring(0, index);
		final File pkg = (File) pkgMap.get(pkgName);
		if (pkg != null) {
			final File file = new File(pkg, name.substring(index + 1));
			return (file.exists()) ? file : null;
		}

		// It is not in the package map; search for it
		final String realName = File.separator
				+ name.replace('.', File.separatorChar)
				+ (source ? ".java" : ".class");
		for (int i = 0; i < classPath.length; i++) {
			final File file = new File(classPath[i] + realName);
			if (file.exists()) {
				pkgMap.put(pkgName, file.getParentFile());
				return file;
			}
		}
		return null;
	}

	/**
	 * Parse a Java input file and build an AST representing it
	 * 
	 * @param name
	 *            the full pathname of the file
	 * @return an AST representing the contents of the file
	 * @exception IOException
	 *                if anything goes wrong with reading the file
	 */
	public static FileAST parseFile(final String name) throws IOException {
		File file = new File(name);
		return parseFile(file);
	}

	/**
	 * Parse a Java input file and build an AST representing it
	 * 
	 * @param file
	 *            the file to parse
	 * @return an AST representing the contents of the file
	 * @exception IOException
	 *                if anything goes wrong with reading the file
	 */
	public static FileAST parseFile(final File file) throws IOException {
		// Have we parsed this file before?
		//FileAST ast = (FileAST) parsedMap.get(file);
		FileAST ast = null; //DX-modified
		parsedMap = new HashMap();
		if (ast != null)
			return ast;

		// Create a file input stream of data from the file
		final FileInputStream input = new FileInputStream(file);

		// Create a scanner that reads from the input stream
		final JavaLexer lexer = new JavaLexer(input);
		lexer.setTokenObjectClass("antlr.CommonHiddenStreamToken");

		// Create the stream filter; hide whitespace and comments
		final TokenStreamHiddenTokenFilter filter = new TokenStreamHiddenTokenFilter(
				lexer);
		filter.hide(JavaLexer.WS);
		filter.hide(JavaLexer.SL_COMMENT);
		filter.hide(JavaLexer.ML_COMMENT);

		// Create a parser that reads from the scanner
		final JavaParser parser = new JavaParser(filter);
		parser.setASTNodeClass("jparse.JavaAST");
		parser.setFile(file);
		parser.setFilename(file.getName());

		// start parsing at the compilationUnit rule
		try {
			parser.compilationUnit();
		} catch (RecognitionException recogEx) {
			System.err.print("Could not parse ");
			System.err.println(file.getName());
			recogEx.printStackTrace();
			return null;
		} catch (TokenStreamException tokenEx) {
			System.err.print("Could not tokenize ");
			System.err.println(file.getName());
			tokenEx.printStackTrace();
			return null;
		} finally {
			input.close();
		}

		// Get the parsed tree
		ast = (FileAST) parser.getAST();
		ast.setInitialHiddenToken(filter.getInitialHiddenToken());

		// Register parsed types in the type map
		final TypeAST[] types = ast.types;
		if (types.length > 0) { // Why wouldn't it be? Dunno, but be safe.
			//final Type aType = (Type) map.get(types[0].name);
			final Type aType = null; //JFU MODIFIED
			if (aType == null) {
				for (int i = 0; i < types.length; i++) {
					final TypeAST type = types[i];
					map.put(type.name, new SourceType(type));
				}
			} else if (aType instanceof SourceType) {
				return ((SourceType) aType).file;
			}
		}

		// Register the parsed file
		//parsedMap.put(file, ast); DX MODIFIED

		// Do any post-parse processing that is needed
		CompileContext oldContext = JavaAST.context;
		JavaAST.context = new CompileContext();
		ast.parseComplete();
		JavaAST.context = oldContext;

		return ast;
	}

	/**
	 * Find a type based on its name. If no such type exists, try to look up the
	 * class and create a <code>Type</code> object for it.
	 * 
	 * @param className
	 *            the name of the class to look up
	 * @return a <code>Type</code> object representing the class, if it was
	 *         found
	 * @exception ClassNotFoundException
	 *                if the given class cannot be found
	 */
	public static Type forName(final String className)
			throws ClassNotFoundException {

		// See if we have processed this type before
		Type type = (Type) map.get(className);
		if (type != null) {
			return type;
		}

		// If it's an array, just tack an array onto the base type
		if (className.endsWith("[]")) {
			final int index = className.indexOf('[');
			final int dims = (className.length() - index) / 2;
			final String baseName = className.substring(0, index);
			final Type baseType = forName(baseName);
			if (baseType instanceof CompiledType) {
				type = new CompiledType((CompiledType) baseType, dims);
			} else {
				type = new SourceType((SourceType) baseType, dims);
			}
		} else {
			// Find the class and source files (if any) for this type
			final File classFile = findFile(className, false);
			final File sourceFile = findFile(className, true);
			if (sourceFile != null
					&& (classFile == null || sourceFile.lastModified() > classFile
							.lastModified())) {
				try {
					final FileAST file = parseFile(sourceFile);
					for (int i = 0; i < file.types.length; i++) {
						if (file.types[i].name.endsWith(className))
							return file.types[i].retrieveType();
					}
				} catch (IOException ioEx) {
				}
			}
			try {
				type = new CompiledType(Class.forName(className, false,
						Type.class.getClassLoader()));
			} catch (NoClassDefFoundError classErr) {
				throw new ClassNotFoundException(className);
			} catch (ClassNotFoundException classEx) {
				// Is it a fully qualified inner class?
				final int index = className.lastIndexOf('.');
				if (index >= 0) {
					final String prefix = className.substring(0, index);
					final File pkg = (File) pkgMap.get(prefix);
					if (pkg == null) {
						try {
							final Type t = forName(prefix);
							type = t.getInner(className.substring(index + 1));
							if (type != null) {
								map.put(type.getName(), type); // $ conversion
								return type;
							}
						} catch (ClassNotFoundException classEx2) {
							// It has the wrong name, so throw the original one
						}
					}
				}
				throw classEx;
			}
		}
		map.put(className, type);
		return type;
	}

	/**
	 * Find a type based on a class. If no such type exists, create a
	 * <code>Type</code> object for it.
	 * 
	 * @param theClass
	 *            the class to look up
	 * @return a <code>Type</code> object representing the class
	 */
	public static Type forClass(final Class theClass) {
		if (theClass == null)
			return null;
		final String className = demangle(theClass.getName());
		Type type = (Type) map.get(className);
		if (type == null) {
			type = new CompiledType(theClass);
			map.put(className, type);
		}
		return type;
	}

	/**
	 * Demangle an internal JVM fully qualified name to a Java source fully
	 * qualified name
	 * 
	 * @param name
	 *            the internal JVM name
	 * @return the equivalent Java source name
	 */
	protected static String demangle(final String name) {
		/*
		 * NOTE: All Sun JDK 1.2 VMs up through and including JDK 1.2.2-001 give
		 * you a mangled name for arrays and an unmangled name otherwise. Sun
		 * says that this is not a bug. Go figure.
		 */
		if (name.charAt(0) != '[')
			return name;
		final StringBuffer buf = new StringBuffer(name.length() * 2);
		for (int i = 0; i < name.length(); i++) {
			switch (name.charAt(i)) {
			case '[':
				buf.append("[]");
				break;
			case 'B':
				buf.insert(0, "byte");
				break;
			case 'C':
				buf.insert(0, "char");
				break;
			case 'D':
				buf.insert(0, "double");
				break;
			case 'F':
				buf.insert(0, "float");
				break;
			case 'I':
				buf.insert(0, "int");
				break;
			case 'J':
				buf.insert(0, "long");
				break;
			case 'L':
				final int index = name.indexOf(';', i);
				buf.insert(0, name.substring(i + 1, index));
				i = index + 1;
				break;
			case 'S':
				buf.insert(0, "short");
				break;
			case 'Z':
				buf.insert(0, "boolean");
				break;
			default:
				System.err.print("Tried to demangle ");
				System.err.print(name);
				System.err.println(" unsuccessfully.");
			}
		}
		return buf.toString();
	}

	/**
	 * Mangle a Java source fully qualified name to an internal JVM fully
	 * qualified name.
	 * 
	 * @param name
	 *            the JVM source name
	 * @return the equivalent internal Java name
	 */
	protected static String mangle(String name) {
		final StringBuffer buf = new StringBuffer(name.length() + 2);
		final int index = name.indexOf('[');
		if (index >= 0) {
			for (int i = 0; i < (name.length() - index) / 2; i++)
				buf.append('[');
			name = name.substring(0, index);
		}
		if (name.equals("boolean"))
			buf.append('Z');
		else if (name.equals("byte"))
			buf.append('B');
		else if (name.equals("char"))
			buf.append('C');
		else if (name.equals("double"))
			buf.append('D');
		else if (name.equals("float"))
			buf.append('F');
		else if (name.equals("int"))
			buf.append('I');
		else if (name.equals("long"))
			buf.append('J');
		else if (name.equals("short"))
			buf.append('S');
		else if (name.equals("void"))
			buf.append('V');
		else {
			buf.append('L');
			buf.append(name);
			buf.append(';');
		}
		return buf.toString();
	}

	/**
	 * Determine whether a fully qualified name corresponds to a class
	 * 
	 * @param className
	 *            the name of the class to test
	 * @return <code>true</code> if the class exists
	 */
	public static boolean exists(final String className) {
		try {
			return forName(className) != null;
		} catch (ClassNotFoundException noClassEx) {
			return false;
		}
	}

	/**
	 * Determine the type of a variable in some class
	 * 
	 * @param className
	 *            the name of the class to look up
	 * @param varName
	 *            the name of the variable to look up
	 * @return the type of the variable
	 */
	public static Type varType(final String className, final String varName) {
		try {
			return forName(className).varType(varName);
		} catch (ClassNotFoundException classEx) {
			return null;
		}
	}

	/**
	 * Determine the type of the result of arithmetic on two types, using the
	 * rules for Java type promotion
	 * 
	 * @param t1
	 *            the first type involved in the arithmetic
	 * @param t2
	 *            the second type involved in the arithmetic
	 * @return the type of the result of arithmetic with <var>t1 </var> and
	 *         <var>t1 </var>
	 */
	public static Type arithType(final Type t1, final Type t2) {
		// This algorithm is from JLS 5.6.2
		if (t1 == doubleType || t2 == doubleType)
			return doubleType;
		if (t1 == floatType || t2 == floatType)
			return floatType;
		if (t1 == longType || t2 == longType)
			return longType;
		return intType;
	}

	/**
	 * Merge two lists of types, removing duplicates and subclasses
	 * 
	 * @param list1
	 *            the first list of types
	 * @param list2
	 *            the second list of types
	 * @return the merged list, with duplicates and exceptions that are
	 *         subclasses of other exceptions in the list removed
	 */
	public static final Type[] mergeTypeLists(final Type[] list1,
			final Type[] list2) {
		// First, check the common cases
		int length1 = list1.length;
		if (length1 == 0)
			return list2;
		final int length2 = list2.length;
		if (length2 == 0)
			return list1;

		// There are some in both lists. Make an array big enough to hold
		// them all.
		final int size = length1 + length2;
		final Type[] bigResult = new Type[size];
		System.arraycopy(list1, 0, bigResult, 0, length1);

		// Now check for duplicates and subclasses while we merge in list2

		// This is an O(n^2) algorithm. We can make this O(n) with hashing,
		// but is it worth the trouble (and the larger constant factor)? How
		// long do these lists tend to be, on average? Probably VERY short,
		// in which case this is fine.
		int index = length1;
		for (int i = 0; i < length2; i++) {
			final Type candidate = list2[i];
			int found = 0; // The number in list1 that list2[i] subsumes
			for (int j = 0; j < length1; j++) {
				if (bigResult[j].superClassOf(candidate) && found == 0) {
					found = 1; // Something in list1 subsumes list2[i]
				} else if (candidate.superClassOf(bigResult[j])) {
					bigResult[j] = (found == 0) ? candidate
							: bigResult[found - 1];
					found++;
				}
			}
			if (found == 0) {
				bigResult[index++] = candidate;
			} else if (--found > 0) {
				System.arraycopy(bigResult, found, bigResult, 0, length1
						- found);
				length1 -= found;
				index -= found;
			}
		}

		// Now make the array just the right size
		if (index == size)
			return bigResult;
		final Type[] result = new Type[index];
		System.arraycopy(bigResult, 0, result, 0, index);
		return result;
	}

	// ######################### The non-static part #########################

	/**
	 * Determine whether this type, as a formal parameter, can have a value of
	 * type <var>type </var> assigned to it as an actual parameter. Note that
	 * this differs from the version in {@link java.lang.Class java.lang.Class}
	 * when <var>type </var> is <code>null</code>. It throws a
	 * {@link java.lang.NullPointerException NullPointerException}, but this
	 * checks whether this type is not primitive (i.e., is able to hold a value
	 * of <code>null</code>).
	 * 
	 * @param type
	 *            the type to check against this type
	 * @return <code>true</code> if <var>type </var> can be the type of an
	 *         actual parameter passed into a method declared as taking this
	 *         type as a formal parameter; <code>false</code> otherwise
	 */
	public abstract boolean isAssignableFrom(Type type);

	/**
	 * Determine whether this type represents an interface
	 * 
	 * @return <code>true</code> if this type is an interface
	 */
	public abstract boolean isInterface();

	/**
	 * Determine whether this type represents an array type
	 * 
	 * @return <code>true</code> if this type is an array type
	 */
	public abstract boolean isArray();

	/**
	 * Determine whether this type represents a Java primitive type
	 * 
	 * @return <code>true</code> if this type is a Java primitive type
	 */
	public abstract boolean isPrimitive();

	/**
	 * Determine whether this type is an inner class
	 * 
	 * @return <code>true</code> if this type is an inner class
	 */
	public abstract boolean isInner();

	/**
	 * Get the fully qualified name of a type
	 * 
	 * @return the fully qualified name of this type
	 */
	public abstract String getName();

	/**
	 * Get the supertype of this <code>Type</code> object
	 * 
	 * @return the supertype of this <code>Type</code> object
	 * @exception ClassNotFoundException
	 *                if the superclass definition cannot be found
	 */
	public abstract Type getSuperclass() throws ClassNotFoundException;

	/**
	 * Get the package in which the type definition resides
	 * 
	 * @return the package name of this type
	 */
	public abstract String getPackage();

	/**
	 * Get the interfaces implemented by this type (if it is a class) or
	 * extended by this type (if it is an interface)
	 * 
	 * @return an array holding the interfaces
	 */
	public abstract Type[] getInterfaces();

	/**
	 * Get the component type of an array, or return <code>null</code> if this
	 * type does not represent an array
	 * 
	 * @return the component type of an array
	 */
	public abstract Type getComponentType();

	/**
	 * Get the modifiers for this class, encoded as per <em>The Java Virtual
	 * Machine Specification</em>,
	 * table 4.1.
	 * 
	 * @return the modifiers for this class
	 * @see java.lang.reflect.Modifier
	 */
	public abstract int getModifiers();

	/**
	 * If this is an inner class, return the outer class. Otherwise, return
	 * <code>null</code>
	 * 
	 * @return the outer class, or <code>null</code> if none
	 */
	public abstract Type getDeclaringClass();

	/**
	 * Returns an array containing <code>Type</code> objects representing all
	 * the classes and interfaces that are members of this type. This includes
	 * class and interface members inherited from superclasses and class and
	 * interface members declared by the class. This method returns an array of
	 * length 0 if this type has no member classes or interfaces. This method
	 * also returns an array of length 0 if this is a primitive type, an array
	 * class, or <code>void</code>.
	 * 
	 * @return an array of member classes and interfaces
	 */
	public abstract Type[] getClasses();

	/**
	 * Returns an array containing <code>Method</code> objects representing
	 * all the methods that are members of this type. This includes methods
	 * inherited from superclasses, abstract methods defined by interfaces (for
	 * abstract types only), and methods declared by this class. This method
	 * returns an array of length 0 if this is a primitive type, an array class,
	 * or <code>void</code>.
	 * 
	 * @return an array of member methods
	 */
	public abstract Method[] getMethods();

	/**
	 * Get an object representing a method in this class with the specified
	 * parameter types
	 * 
	 * @param methName
	 *            the name of the method to look up
	 * @param paramTypes
	 *            the types of the parameters
	 * @param caller
	 *            the type in which the method call is contained (used to check
	 *            visibility)
	 * @return a <code>Method</code> object representing the best-matching
	 *         method with those parameter types, or <code>null</code> if
	 *         there is none
	 */
	public abstract Method getMethod(String methName, Type[] paramTypes,
			Type caller);

	/**
	 * Get an object representing the constructor for this class with the
	 * specified parameter types
	 * 
	 * @param params
	 *            the types of the parameters
	 * @param caller
	 *            the type creating an instance of this object with
	 *            <code>new</code> (used to check visibility)
	 * @return a <code>Constructor</code> object representing the constructor
	 *         with those parameter types, or <code>null</code> if there is
	 *         none
	 */
	public abstract Constructor getConstructor(Type[] params, Type caller);

	/**
	 * Get an inner class with a specified name. This name must begin with a
	 * dollar sign ($) for this method to work properly.
	 * 
	 * @param name
	 *            the name of the inner class to lookup
	 * @return a type corresponding to the requested inner class, if it exists,
	 *         or <code>null</code> otherwise
	 */
	public abstract Type getInner(String name);

	/**
	 * Get the type that corresponds to an array of this type
	 * 
	 * @return an array type for this type
	 */
	public abstract Type getArrayType();

	/**
	 * Determine the type of a (static or instance) variable
	 * 
	 * @param varName
	 *            the name of the variable to look up
	 * @return the type of the variable
	 */
	public abstract Type varType(String varName);

	/**
	 * Retrieve matching methods
	 * 
	 * @param name
	 *            the name of the method to match
	 * @param params
	 *            the types of the parameters to the method
	 * @param caller
	 *            the type of the caller
	 * @return an array of matching methods. If there are no matching methods,
	 *         an array of length 0 will be returned.
	 */
	public abstract Method[] getMeths(String name, Type[] params, Type caller);

	/**
	 * Dump information about this type to standard error
	 */
	public abstract void dump();

	/**
	 * Determine whether this type is a superclass of another type
	 * 
	 * @param type
	 *            the potential subclass of this type
	 * @return <code>true</code> if this is a superclass of <var>type </var>
	 */
	public final boolean superClassOf(Type type) {
		try {
			for (; type != null; type = type.getSuperclass()) {
				if (this == type)
					return true;
			}
		} catch (ClassNotFoundException classEx) {
			// Do nothing
		}
		return false;
	}

	/**
	 * Determine whether this type is a superinterface of another type
	 * 
	 * @param type
	 *            the potential subinterface of this type
	 * @return <code>true</code> if this is a superinterface of <var>type
	 *         </var>
	 */
	public final boolean superInterfaceOf(final Type type) {
		if (this == type) {
			return true;
		}

		final Type[] interfaces = type.getInterfaces();
		for (int i = 0; i < interfaces.length; i++) {
			if (superInterfaceOf(interfaces[i])) {
				return true;
			}
		}
		return false;
	}

	/**
	 * Determine whether this type implements an interface
	 * 
	 * @param type
	 *            the potential interface for this type
	 * @return <code>true</code> if this type implements <var>type </var>
	 */
	public final boolean implementsInterface(final Type type) {
		final Type[] interfaces = getInterfaces();
		for (int i = 0; i < interfaces.length; i++) {
			if (type.superInterfaceOf(interfaces[i])) {
				return true;
			}
		}
		try {
			final Type superclass = getSuperclass();
			if (superclass != null)
				return superclass.implementsInterface(type);
		} catch (ClassNotFoundException classEx) {
		}
		return false;
	}
}
