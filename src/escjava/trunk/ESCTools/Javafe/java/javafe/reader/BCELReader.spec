/* Copyright 2007, Systems Research Group, University College Dublin, Ireland */

/*
 * ========================================================================= 
 * BCELReader.spec
 * =========================================================================
 *
 * @note This is a partial specification for the conversion of a BCEL JavaClass
 * format into an abstract syntax tree of a compilatiom unit.
 *
 */

package javafe.reader;

/**
 * 
 * @design Parses the contents of a class file into an AST for the purpose of
 *         type checking. Ignores components of the class file that have no
 *         relevance to type checking (e.g. method bodies).
 */

class BCELReader extends Reader { 

	/**
	 * The BCEL representation of the binary classfile.
	 */
	protected JavaClass javaClass;
	 
	/**
	 * The default constructor
	 */
	public BCELReader() {
	}

	/**
	 * Convert the BCEL JavaClass format into an abstract syntax tree of a
	 * compilation unit suitable for extended static checking.
	 * 
	 * normal_behavior
	 * @requires javaClass != null;
	 * 
	 * @ensures \result != null;
	 * 
	 * @TODO specify that everything needed is included 
	 *
	 * @author dermotcochran
	 * @return An abstract syntax tree of a compilation unit.
	 * 
	 * @throws ClassNotFoundException
	 */
	protected CompilationUnit getCompilationUnit() throws ClassNotFoundException;

	/**
	 * Convert from BCEL to JavaFE AST
	 *
	 * normal_behavior
	 * @ensures javaClass != null
	 * @ensures \result == getCompilationUnit()
	 */
	public CompilationUnit read(GenericFile target, boolean avoidSpec);

}
