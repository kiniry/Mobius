header {
/*
 * @(#)$Id: java.g,v 1.11 2004/07/14 14:50:40 bdg534 Exp $
 *
 * JParse: a freely available Java parser
 * Copyright (C) 2000,2004 Jeremiah W. James, except for portions derived
 * from the public domain Java grammar written by John Mitchell, Terence
 * Parr, John Lilley, Scott Stanchfield, Markus Mohnen, and Peter Williams.
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

import java.io.*;
import java.lang.reflect.Modifier;
import java.util.ArrayList;
import java.util.LinkedList;
import jparse.expr.*;
import jparse.stmt.*;
}

/**
 * A Java 1.4 parser.  This parser is based on, but differs significantly
 * from, version 1.22 of the public domain ANTLR parser written by:
 *
 *		John Mitchell		johnm@non.net
 *		Terence Parr		parrt@magelang.com
 *		John Lilley			jlilley@empathy.com
 *		Scott Stanchfield	thetick@magelang.com
 *		Markus Mohnen       mohnen@informatik.rwth-aachen.de
 *      Peter Williams      pete.williams@sun.com
 *      Allan Jacobs        Allan.Jacobs@eng.sun.com
 *      Steve Messick       messick@redhills.com
 *      John Pybus			john@pybus.org
 *
 * Note that this parser does not suffer from the bugs identified on the ANTLR
 * mailing list for the public domain parser.
 */
class JavaParser extends Parser;
options {
	ASTLabelType = "JavaAST";		// Change the default AST node type
	k = 2;							// two token lookahead
	exportVocab = Java;				// Call its vocabulary "Java"
	codeGenMakeSwitchThreshold = 2;	// Some optimizations
	codeGenBitsetTestThreshold = 3;
	defaultErrorHandler = true;		// Generate parser error handlers
	buildAST = true;
}

tokens {
	FILE; VARIABLE_DEFS; MODIFIERS; ARRAY_DECLARATOR; TYPE; EXTENDS_CLAUSE;
	OBJBLOCK; IMPLEMENTS_CLAUSE; CTOR_DEF; METHOD_DEF; INSTANCE_INIT;
	VARIABLE_DEF; ARRAY_INIT; PARAMETERS; PARAMETER_DEF; SLIST; TYPE_STAT;
	EXPRESSION_STAT; LABELED_STAT; EMPTY_STAT; CASE_GROUP; FOR_INIT;
	FOR_CONDITION; FOR_ITERATOR; ELIST; CONCAT_ASSIGN; CONCATENATION;
	UNARY_MINUS; UNARY_PLUS; TYPECAST; INDEX_OP; METHOD_CALL;
	CONSTRUCTOR_CALL; POST_INC; POST_DEC; PAREN_EXPR;
}

{
	/**
	 * The file to read from.
	 */
	private File file;

	/**
	 * Set file to read from, and the reader to use for fetching lines from
	 * that file
	 *
	 * @param f the file to read from 
	 * @param in the reader
	 */
	void setFile(final File f) {
		file = f;
	}

	/**
	 * Report an error to the user in the format used by Sun's javac
	 *
	 * @param ex an exception detailing the problem
	 */
	public void reportError(final RecognitionException ex) {
		// Report the error itself
		System.err.println(ex.toString());
		//open a new BufferedReader to search for error line
		final BufferedReader error;
        try {
            error =
                new BufferedReader(new InputStreamReader
                                   (new FileInputStream(file), "ISO8859-1"));
        } catch (FileNotFoundException brex) {
            /* This cannot happen; we know the file exists */
            return;
        } catch (UnsupportedEncodingException encex) {
            /* This cannot happen; we used this encoding for input */
            return;
        }

		// Now search through read buffer and print the line containing the error
		String line = null;
        try {
            for(int j = 0; j < ex.line; j++)
                line = error.readLine();
            if (line != null) {
                System.err.println(line);
                for (int i = 0; i < ex.column - 1; i++)
                    System.err.print(' ');
                System.err.println('^');
            }
            error.close();
        } catch (IOException ioex) {
            // Do nothing; this should not be possible
        }
	}

	/**
	 * Report an error to the user in the format used by Sun's javac
	 *
	 * @param msg the message to print
	 */
	public void reportError(final String msg) {
		final String filename = getFilename();
		if (filename != null) {
			System.err.print(filename);
			System.err.print(": ");
		}
		System.err.print(msg);
	}
}
	
// Compilation Unit: In Java, this is a single file.  This is the start rule
// for this parser
compilationUnit
{
	ArrayList imports = new ArrayList();
	ArrayList types = new ArrayList();
}
	:	{ FileAST.currFile = new FileAST(file); }

		// A compilation unit starts with an optional package definition
		( packageDefinition )?

		// Next we have a series of zero or more import statements
		( im:importDefinition
			{ imports.add(((IdentifierAST)#im.getFirstChild()).getName()); }
		)*
		{
			FileAST.currFile.imports = new String[imports.size()];
			imports.toArray(FileAST.currFile.imports);
			imports = null;  // Feed the garbage collector
		}

		// Finally, we have any number of class or interface definitions
		( typ:typeDefinition
			{ if (#typ.getType() != SEMI) types.add(#typ); } )*
		{
			FileAST.currFile.types = new jparse.TypeAST[types.size()];
			types.toArray(FileAST.currFile.types);
			types = null;  // Feed the garbage collector
		}

		EOF!

		{ #compilationUnit = #(FileAST.currFile, #compilationUnit); }
	;

// Package statement: "package" followed by an identifier.
protected
packageDefinition
	:	"package"^ id:identifier SEMI
		{ FileAST.currFile.pkg = ((IdentifierAST)#id).getName(); }
	;

// Import statement: import followed by a package or class name
protected
importDefinition
	:	"import"^ identifierStar SEMI
	;

// A (possibly-qualified) Java identifier.  We start with the first IDENT and
// expand its name by adding dots and following IDENTS
protected
identifier { StringBuffer buf = new StringBuffer(); }
	:	id:IDENT<AST=jparse.expr.IdentifierAST>
			{ buf.append(#id.getText()); }
		( d:DOT^<AST=jparse.expr.IdentifierAST> i:IDENT
			{ buf.append(#d.getText()); buf.append(#i.getText()); } )*
		{ ((IdentifierAST)#identifier).setName(buf.toString()); }
	;

// A (possibly-qualified) Java identifier that optionally has a STAR as its
// last component.
protected
identifierStar { StringBuffer buf = new StringBuffer(); }
	:	id:IDENT<AST=jparse.expr.IdentifierAST>
			{ buf.append(#id.getText()); }
		( d1:DOT^<AST=jparse.expr.IdentifierAST> i:IDENT
			{ buf.append(#d1.getText()); buf.append(#i.getText()); } )*
		( d2:DOT^<AST=jparse.expr.IdentifierAST> s:STAR
			{ buf.append(#d2.getText()); buf.append(#s.getText()); } )?
		{ ((IdentifierAST)#identifierStar).setName(buf.toString()); }
	;

// A type definition in a file is either a class or interface definition.
protected
typeDefinition
	:	m:modifiers!
		( classDefinition[(ModifierAST)#m]
		| interfaceDefinition[(ModifierAST)#m]
		)
	|	SEMI
	;

// A list of zero or more modifiers.
protected
modifiers { int m, mods = 0; }
	:	( m=modifier { mods |= m; } )*
		{
			AST mod = new ModifierAST(mods);
			#modifiers = #(mod, #modifiers);
		}
	;

// modifiers for Java classes, interfaces, class/instance vars and methods
protected
modifier returns [int value] { value = 0; }
	:	"public"		{ value = Modifier.PUBLIC;			}
	|	"private"		{ value = Modifier.PRIVATE;			}
	|	"protected"		{ value = Modifier.PROTECTED;		}
	|	"static"		{ value = Modifier.STATIC;			}
	|	"final"			{ value = Modifier.FINAL;			}
	|	"synchronized"	{ value = Modifier.SYNCHRONIZED;	}
	|	"volatile"		{ value = Modifier.VOLATILE;		}
	|	"transient"		{ value = Modifier.TRANSIENT;		}
	|	"native"		{ value = Modifier.NATIVE;			}
	|	"abstract"		{ value = Modifier.ABSTRACT;		}
	|	"strictfp"		{ value = Modifier.STRICT;			}
	;

// Definition of a Java class
protected
classDefinition[ModifierAST modifiers]
	{ jparse.TypeAST oldType = jparse.TypeAST.currType; }
	:	c:"class"!<AST=jparse.TypeAST>
		id:IDENT<AST=jparse.expr.IdentifierAST>
		{
			final String newName = (oldType == null)
				? #id.getText()
				: oldType.name + '$' + #id.getText();
			#c.setInfo(FileAST.currFile.pkg, newName, oldType, modifiers);
			jparse.TypeAST.currType = #c;
		}

		// it _might_ have a superclass...
		( superClassClause )?
		// it might implement some interfaces...
		implementsClause
		// now parse the body of the class
		classBlock
		{
			#classDefinition = #(#c, #modifiers, #classDefinition);
			if (oldType != null) {
				oldType.addInner(jparse.TypeAST.currType);
			}
			jparse.TypeAST.currType = oldType;
			JavaAST.currSymTable = JavaAST.currSymTable.parent;
		}
	;

protected
superClassClause
	:	"extends"^ id:identifier
		{ jparse.TypeAST.currType.superclass =
			((IdentifierAST)#id).getName(); }
	;

// A class can implement several interfaces...
protected
implementsClause { ArrayList idents = new ArrayList(); }
	:	( "implements"^
			id1:identifier { idents.add(((IdentifierAST)#id1).getName()); }
			( COMMA id2:identifier
				{ idents.add(((IdentifierAST)#id2).getName()); }
			)*
		)?
		{
			jparse.TypeAST.currType.interfaces = new String[idents.size()];
			idents.toArray(jparse.TypeAST.currType.interfaces);
		}
	;

// Definition of a Java Interface
protected
interfaceDefinition[ModifierAST modifiers]
	{ jparse.TypeAST oldType = jparse.TypeAST.currType; }
	:	i:"interface"!<AST=jparse.TypeAST>
		id:IDENT<AST=jparse.expr.IdentifierAST>
		{
			final String newName = (oldType == null)
				? #id.getText()
				: oldType.name + '$' + #id.getText();
			#i.setInfo(FileAST.currFile.pkg, newName, oldType, modifiers);
			jparse.TypeAST.currType = #i; // TODO: Can this ever be non-null??
		}

		// it might extend some other interfaces
		interfaceExtends
		// now parse the body of the interface (looks like a class...)
		classBlock
		{
			#modifiers.setInterface();
			#interfaceDefinition = #(#i, #modifiers, #interfaceDefinition);
			if (oldType != null) {
				oldType.addInner(jparse.TypeAST.currType);
			}
			jparse.TypeAST.currType = oldType;
			JavaAST.currSymTable = JavaAST.currSymTable.parent;
		}
	;

// An interface can extend several other interfaces...
protected
interfaceExtends { final ArrayList idents = new ArrayList(); }
	:	( "extends"^ id1:identifier
				{ idents.add(((IdentifierAST)#id1).getName()); }
			( COMMA id2:identifier
					{ idents.add(((IdentifierAST)#id2).getName()); }
			)*
		)?
		{
			final int size = idents.size();
			jparse.TypeAST.currType.interfaces = new String[size];
			if (size > 0)
				idents.toArray(jparse.TypeAST.currType.interfaces);
		}
	;

// This is the body of a class or interface.  You can have fields and extra
// semicolons, That's about it (until you see what a field is...)
protected
classBlock
	:	lc:LCURLY^ { #lc.setType(OBJBLOCK); } ( field )* RCURLY
	;

// Now the various things that can be defined inside a class or interface...
// Note that not all of these are really valid in an interface (constructors,
// for example), and if this grammar were used for a compiler there would need
// to be some semantic checks to make sure we're doing the right thing...
protected
field
	:	// method, constructor, or variable declaration
		mods:modifiers!
		(	{ JavaAST.currSymTable = new SymbolTable(); }
			IDENT<AST=jparse.expr.IdentifierAST>  // constructor name

			// parse the formal parameter declarations.
			LPAREN cparams:parameterDeclarationList RPAREN

			// the list of exceptions the constructor is declared to throw
			(cthrows:throwsClause)?

			// the body of the constructor
			cbody:compoundStatement
			{
				JavaAST.currSymTable = JavaAST.currSymTable.parent;
				final ConstrAST constr = 
					new ConstrAST((ModifierAST)#mods, #cparams, #cthrows,
						(CompoundAST)#cbody);
				#field = #(constr, #mods, #field);
			}
		|	classDefinition[(ModifierAST)#mods]       // inner class
		|	interfaceDefinition[(ModifierAST)#mods]   // inner interface
		|	t:typeSpec  // method or variable declaration(s)
			(	name:IDENT<AST=jparse.expr.IdentifierAST>  // method name
				{ JavaAST.currSymTable = new SymbolTable(); }

				// parse the formal parameter declarations.
				LPAREN mparams:parameterDeclarationList RPAREN

				d:declaratorBrackets

				// get the exceptions that this method is declared to throw
				(mthrows:throwsClause)?

				( mbody:compoundStatement | SEMI )
				{
					JavaAST.currSymTable = JavaAST.currSymTable.parent;
					final ModifierAST mod = (ModifierAST)#mods;
					if (jparse.TypeAST.currType.modifiers.isInterface())
						mod.setInterfaceMethod();
					final MethAST meth =
						new MethAST(mod, (jparse.expr.TypeAST)#t, #name,
							#mparams, #d, #mthrows, (CompoundAST)#mbody);
					#field = #(meth, mod, #field);
				}
			|	vars:variableDefinitions SEMI
				{
					final DeclarationAST decl =
						new DeclarationAST((ModifierAST)#mods,
										   (jparse.expr.TypeAST)#t, #vars);
					#field = #(decl, #mods, #field);
				}
			)
		)

    // "static { ... }" class initializer
	|	"static"^ compoundStatement

    // "{ ... }" instance initializer
	|	compoundStatement
		{ #field = #(#[INSTANCE_INIT,"INSTANCE_INIT"], #field); }

	// Empty declaration
	|	SEMI
	;

// This is a list of exception classes that the method is declared to throw
protected
throwsClause
	:	"throws"^ identifier ( COMMA identifier )*
	;

// A type specification is a type name with possible brackets afterwards
// (which would make it an array type).
protected
typeSpec
	: classTypeSpec
	| builtInTypeSpec
	;

// A class type specification is a class type with possible brackets
// afterwards (which would make it an array type).
protected
classTypeSpec
	:	identifier (lb:LBRACK^<AST=jparse.expr.IdentifierAST>
			{
				#lb.setType(ARRAY_DECLARATOR);
				#lb.setName(((IdentifierAST)#lb.getFirstChild()).getName() +
							"[]");
			}
			RBRACK)*
		{
			jparse.expr.TypeAST t =
				new jparse.expr.TypeAST(((IdentifierAST)#classTypeSpec)
										.getName());
			#classTypeSpec = #(t, #classTypeSpec);
		}
	;

// A builtin type specification is a builtin type with possible brackets
// afterwards (which would make it an array type).
protected
builtInTypeSpec
	:	builtInType (lb:LBRACK^<AST=jparse.expr.IdentifierAST>
			{
				#lb.setType(ARRAY_DECLARATOR);
				#lb.setName(((IdentifierAST)#lb.getFirstChild()).getName() +
							"[]");
			}
			RBRACK)*
		{
			jparse.expr.TypeAST t =
				new jparse.expr.TypeAST(((IdentifierAST)#builtInTypeSpec)
										.getName());
			#builtInTypeSpec = #(t, #builtInTypeSpec);
		}
	;

// A type name. which is either a (possibly qualified) class name or a
// primitive (builtin) type
protected
type
	:	identifier
	|	builtInType
	;

// The primitive types
protected
builtInType
	:	"void"<AST=jparse.expr.IdentifierAST>
	|	"boolean"<AST=jparse.expr.IdentifierAST>
	|	"byte"<AST=jparse.expr.IdentifierAST>
	|	"char"<AST=jparse.expr.IdentifierAST>
	|	"short"<AST=jparse.expr.IdentifierAST>
	|	"int"<AST=jparse.expr.IdentifierAST>
	|	"float"<AST=jparse.expr.IdentifierAST>
	|	"long"<AST=jparse.expr.IdentifierAST>
	|	"double"<AST=jparse.expr.IdentifierAST>
	;

protected
variableDefinitions
	:	variableDeclarator ( COMMA variableDeclarator )*
	;

// Declaration of a variable.  This can be a class/instance variable, or a
// local variable in a method.  It can also include possible initialization.
protected
variableDeclarator
	:	IDENT<AST=jparse.expr.VarAST> declaratorBrackets (varInitializer)?
		{ #variableDeclarator = #(#[VARIABLE_DEF,"VARIABLE_DEF"],
								  #variableDeclarator); }
	;

protected
declaratorBrackets
	:	(lb:LBRACK {#lb.setType(ARRAY_DECLARATOR);} RBRACK)*
	;

protected
varInitializer
	:	ASSIGN^<AST=jparse.expr.InitializerAST> initializer
	;

// The two "things" that can initialize an array element are an expression and
// another (nested) array initializer.
protected
initializer
	:	expression
	|	arrayInitializer
	;

// This is an initializer used to set up an array.
protected
arrayInitializer
	:	LCURLY^<AST=jparse.expr.ArrayInitAST>
		(initializer (commaInitializer)? )? RCURLY
	;

protected
commaInitializer
	:	COMMA^ (initializer (commaInitializer)? )?
	;

// A list of formal parameters
protected
parameterDeclarationList
	:	( parameterDeclaration ( COMMA parameterDeclaration )* )?
		{ #parameterDeclarationList = #(#[PARAMETERS,"PARAMETERS"],
										#parameterDeclarationList); }
	;

// A formal parameter.
protected
parameterDeclaration
	:	m:modifiers t:typeSpec v:IDENT<AST=jparse.expr.VarAST>
		declaratorBrackets
		{
			final ParameterAST param = new ParameterAST((ModifierAST)#m,
										(jparse.expr.TypeAST)#t, #v);
			#parameterDeclaration = #(param, #parameterDeclaration);
		}
	;

// Compound statement.  This is used in many contexts:
//   Inside a class definition prefixed with "static":
//      it is a class initializer
//   Inside a class definition without "static":
//      it is an instance initializer
//   As the body of a method
//   As a completely indepdent braced block of code inside a method
//      it starts a new scope for variable definitions

protected
compoundStatement
	:	LCURLY^<AST=jparse.stmt.CompoundAST>
			{ JavaAST.currSymTable = new SymbolTable(); }
			// include the (possibly-empty) list of statements
			(statement)*
			{ JavaAST.currSymTable = JavaAST.currSymTable.parent; }
		RCURLY
	;

protected
statement
	// A list of statements in curly braces -- start a new scope!
	:	compoundStatement

	// declarations are ambiguous with "ID DOT" relative to expression
	// statements.  Must backtrack to be sure.
	|	(modifiers typeSpec IDENT)=> declaration

	// class definition
	|	mods:modifiers! def:classDefinition[(ModifierAST)#mods]
		{
			final ClassAST type = new ClassAST((TypeAST)#def);
			#statement = #(type, #statement);
		}

	// An expression statement.  This could be a method call,
	// assignment statement, or any other expression evaluated for
	// side-effects.
	|	e:expression SEMI
		{
			final jparse.stmt.ExpressionAST expr =
				new jparse.stmt.ExpressionAST((jparse.expr.ExpressionAST)#e);
			#statement = #(expr, #statement);
		}

	// Attach a label to the front of a statement
	|	label:IDENT^<AST=jparse.stmt.LabelAST> COLON st:statement
		{ #label.symTable.addLabel(#label.getText(), #st); }

	// If-else statement
	|	"if"^<AST=jparse.stmt.IfElseAST> LPAREN expression RPAREN statement
		(
			// CONFLICT: the old "dangling-else" problem...
			//           ANTLR generates proper code matching
			//			 as soon as possible.  Match greedily.
			options { greedy = true; }
		:
			"else" statement
		)?

	// For statement
	|	"for"^<AST=jparse.stmt.ForAST>
		{ JavaAST.currSymTable = new SymbolTable(); }
			LPAREN
				forInit   // initializer
				forCond   // condition test
				forIter   // updater
			RPAREN
			statement                     // statement to loop over
		{ JavaAST.currSymTable = JavaAST.currSymTable.parent; }

	// While statement
	|	"while"^<AST=jparse.stmt.WhileAST> LPAREN expression RPAREN
		statement

	// do-while statement
	|	"do"^<AST=jparse.stmt.DoWhileAST> statement "while"
		LPAREN expression RPAREN SEMI

	// get out of a loop (or switch)
	|	"break"^<AST=jparse.stmt.BreakAST>
		(IDENT<AST=jparse.expr.IdentifierAST>)? SEMI

	// do next iteration of a loop
	|	"continue"^<AST=jparse.stmt.ContinueAST>
		(IDENT<AST=jparse.expr.IdentifierAST>)? SEMI

	// Return an expression
	|	"return"^<AST=jparse.stmt.ReturnAST> (expression)? SEMI

	// switch/case statement
	|	"switch"^<AST=jparse.stmt.SwitchAST> LPAREN expression RPAREN
		LCURLY
			( casesGroup )*
		RCURLY

	// exception try-catch block
	|	tryBlock

	// throw an exception
	|	"throw"^<AST=jparse.stmt.ThrowAST> expression SEMI

	// synchronize a statement
	|	"synchronized"^<AST=jparse.stmt.SynchronizedAST>
		LPAREN expression RPAREN compoundStatement

    // asserts (Java 1.4)
    |   "assert"^<AST=jparse.stmt.AssertAST>
        expression ( COLON expression )? SEMI

	// empty statement
	|	SEMI<AST=jparse.stmt.EmptyAST>

	;

// A declaration is the creation of a reference or primitive-type variable.
// Create a separate Type/Var tree for each var in the var list.
protected
declaration
	:	m:modifiers t:typeSpec v:variableDefinitions SEMI
		{
			final DeclarationAST decl =
				new DeclarationAST((ModifierAST)#m,(jparse.expr.TypeAST)#t,#v);
			#declaration = #(decl, #declaration);
		}
	;

protected
casesGroup
	:	(	// CONFLICT: to which case group do the statements bind?
			//           ANTLR generates proper code: it groups the
			//           many "case"/"default" labels together then
			//           follows them with the statements
			options { greedy = true; }
		:
			("case" expression | "default") COLON
		)+
		(statement)*
		{
			final CaseGroupAST group = new CaseGroupAST();
			#casesGroup = #(group, #casesGroup);
		}
	;

// The initializer for a for loop
protected
forInit
		// if it looks like a declaration, it is
	:	(	(modifiers typeSpec IDENT)=> declaration
		// otherwise it is an expression list...
		|	expressionList SEMI
		)
		{#forInit = #(#[FOR_INIT,"FOR_INIT"],#forInit);}
	;

protected
forCond
	:	(expression)? SEMI
		{#forCond = #(#[FOR_CONDITION,"FOR_CONDITION"],#forCond);}
	;

protected
forIter
	:	expressionList
		{#forIter = #(#[FOR_ITERATOR,"FOR_ITERATOR"],#forIter);}
	;

// an exception handler try/catch block
protected
tryBlock
	:	"try"^<AST=jparse.stmt.TryAST> compoundStatement
		(	// CONFLICT: to which try do the catch handlers bind?
			options { greedy = true; }
		:
			handler
		)*
		(	// CONFLICT: to which try does the finally bind?
			options { greedy = true; }
		:
			"finally" compoundStatement
		)?
	;

// an exception handler
protected
handler
	:	"catch"^<AST=jparse.stmt.CatchAST>
		{ JavaAST.currSymTable = new SymbolTable(); }
		LPAREN parameterDeclaration RPAREN compoundStatement
		{ JavaAST.currSymTable = JavaAST.currSymTable.parent; }
	;

// expressions
// Note that most of these expressions follow the pattern
//   thisLevelExpression :
//       nextHigherPrecedenceExpression
//           (OPERATOR nextHigherPrecedenceExpression)*
// which is a standard recursive definition for a parsing an expression.
// The operators in java have the following precedences:
//    lowest  (13)  = *= /= %= += -= <<= >>= >>>= &= ^= |=
//            (12)  ?:
//            (11)  ||
//            (10)  &&
//            ( 9)  |
//            ( 8)  ^
//            ( 7)  &
//            ( 6)  == !=
//            ( 5)  < <= > >=
//            ( 4)  << >>
//            ( 3)  +(binary) -(binary)
//            ( 2)  * / %
//            ( 1)  ++ -- +(unary) -(unary)  ~  !  (type)
//                  []   () (method call)  . (dot -- identifier qualification)
//                  new   ()  (explicit parenthesis)
//
// the last two are not usually on a precedence chart; I put them in
// to point out that new has a higher precedence than '.', so you
// can validy use
//     new Frame().show()
// 
// Note that the above precedence levels map to the rules below...
// Once you have a precedence chart, writing the appropriate rules as below
//   is usually very straightfoward

// the mother of all expressions
protected
expression
	:	assignmentExpression
	;

// This is a list of expressions.
protected
expressionList
	:	( expression (COMMA expression)* )?
		{
			final ListAST list = new ListAST(#expressionList);
			#expressionList = #(list, #expressionList);
		}
	;

// assignment expression (level 13)
protected
assignmentExpression
	:	conditionalExpression
		(	( ASSIGN^<AST=jparse.expr.AssignAST>
			| PLUS_ASSIGN^<AST=jparse.expr.AssignAST>
			| MINUS_ASSIGN^<AST=jparse.expr.AssignAST>
			| STAR_ASSIGN^<AST=jparse.expr.AssignAST>
			| DIV_ASSIGN^<AST=jparse.expr.AssignAST>
			| MOD_ASSIGN^<AST=jparse.expr.AssignAST>
			| SR_ASSIGN^<AST=jparse.expr.AssignAST>
			| BSR_ASSIGN^<AST=jparse.expr.AssignAST>
			| SL_ASSIGN^<AST=jparse.expr.AssignAST>
			| BAND_ASSIGN^<AST=jparse.expr.AssignAST>
			| BXOR_ASSIGN^<AST=jparse.expr.AssignAST>
			| BOR_ASSIGN^<AST=jparse.expr.AssignAST>
			)
			assignmentExpression )?
	;

// conditional test (level 12)
protected
conditionalExpression
	:	logicalOrExpression
		(	QUESTION^<AST=jparse.expr.ConditionalAST> assignmentExpression
			COLON conditionalExpression )?
	;

// logical or (||)  (level 11)
protected
logicalOrExpression
	:	logicalAndExpression
		(LOR^<AST=jparse.expr.BooleanAST> logicalAndExpression)*
	;

// logical and (&&)  (level 10)
protected
logicalAndExpression
	:	inclusiveOrExpression
		(LAND^<AST=jparse.expr.BooleanAST> inclusiveOrExpression)*
	;

// bitwise or non-short-circuiting or (|)  (level 9)
protected
inclusiveOrExpression
	:	exclusiveOrExpression
		(BOR^<AST=jparse.expr.BitwiseAST> exclusiveOrExpression)*
	;

// exclusive or (^)  (level 8)
protected
exclusiveOrExpression
	:	andExpression (BXOR^<AST=jparse.expr.BitwiseAST> andExpression)*
	;

// bitwise or non-short-circuiting and (&)  (level 7)
protected
andExpression
	:	equalityExpression
		(BAND^<AST=jparse.expr.BitwiseAST> equalityExpression)*
	;

// equality/inequality (==/!=) (level 6)
protected
equalityExpression
	:	relationalExpression
		(	( NOT_EQUAL^<AST=jparse.expr.BooleanAST>
			| EQUAL^<AST=jparse.expr.BooleanAST>
			)
			relationalExpression
		)*
	;

// boolean relational expressions (level 5)
protected
relationalExpression
	:	shiftExpression
		(	(	( LT^<AST=jparse.expr.BooleanAST>
				| GT^<AST=jparse.expr.BooleanAST>
				| LE^<AST=jparse.expr.BooleanAST>
				| GE^<AST=jparse.expr.BooleanAST>
				) shiftExpression
			)*
		|	"instanceof"^<AST=jparse.expr.BooleanAST> typeSpec
		)
	;

// bit shift expressions (level 4)
protected
shiftExpression
	:	additiveExpression
		(	( SL^<AST=jparse.expr.ShiftAST>
			| SR^<AST=jparse.expr.ShiftAST>
			| BSR^<AST=jparse.expr.ShiftAST>
			) additiveExpression
		)*
	;

// binary addition/subtraction (level 3)
protected
additiveExpression
	:	multiplicativeExpression
		(	( PLUS^<AST=jparse.expr.ArithmeticAST>
			| MINUS^<AST=jparse.expr.ArithmeticAST>
			) multiplicativeExpression
		)*
	;

// multiplication/division/modulo (level 2)
protected
multiplicativeExpression
	:	unaryExpression
		(	( STAR^<AST=jparse.expr.ArithmeticAST>
			| DIV^<AST=jparse.expr.ArithmeticAST>
			| MOD^<AST=jparse.expr.ArithmeticAST>
			) unaryExpression
		)*
	;

protected
unaryExpression
	:	INC^<AST=jparse.expr.UnaryArithAST> unaryExpression
	|	DEC^<AST=jparse.expr.UnaryArithAST> unaryExpression
	|	MINUS^<AST=jparse.expr.UnaryArithAST>
		{#MINUS.setType(UNARY_MINUS);} unaryExpression
	|	PLUS^<AST=jparse.expr.UnaryArithAST> {#PLUS.setType(UNARY_PLUS);}
		unaryExpression
	|	unaryExpressionNotPlusMinus
	;

protected
unaryExpressionNotPlusMinus
	:	BNOT^<AST=jparse.expr.UnaryArithAST> unaryExpression
	|	LNOT^<AST=jparse.expr.BooleanAST> unaryExpression

		// use predicate to skip cases like: (int.class)
    |   (LPAREN builtInTypeSpec RPAREN) =>
        LPAREN^<AST=jparse.expr.TypecastAST> builtInTypeSpec RPAREN
        unaryExpression

        // Have to backtrack to see if operator follows.  If no operator
        // follows, it's a typecast.  No semantic checking needed to parse.
        // if it _looks_ like a cast, it _is_ a cast; else it's a "(expr)"
    |	(LPAREN classTypeSpec RPAREN unaryExpressionNotPlusMinus)=>
        LPAREN^<AST=jparse.expr.TypecastAST> classTypeSpec RPAREN
        unaryExpressionNotPlusMinus

    |	postfixExpression
	;

// qualified names, array expressions, method invocation, post inc/dec
protected
postfixExpression { String name = null; }
	:	primaryExpression // start with a primary

		(	// qualified id (id.id.id.id...) -- build the name
			dot1:DOT^<AST=jparse.expr.IdentifierAST>
			{
				final AST child = #dot1.getFirstChild();
				name = ((child instanceof IdentifierAST)
						? ((IdentifierAST)child).getName() : "") +
					   #dot1.getText();
			}
			(	id:IDENT<AST=jparse.expr.IdentifierAST>
				{ #dot1.setName(name + #id.getText()); }
			|	th:"this"   { #dot1.setName(name + #th.getText()); }
			|	cl1:"class" { #dot1.setName(name + #cl1.getText()); }
			|	newExpression
                // FIXME: Check the new ANTLR parser for this part
			|	su:"super"<AST=jparse.expr.IdentifierAST>
				LPAREN^<AST=jparse.expr.MethodCallAST> expressionList RPAREN
				{
					#dot1.setName(name + #su.getText());
					#dot1.setMethod();
				}
			)

			// allow ClassName[].class
		|	( lbc:LBRACK^<AST=jparse.expr.IdentifierAST>
				{
					#lbc.setType(ARRAY_DECLARATOR);
					final AST child = #lbc.getFirstChild();
					name = ((child instanceof IdentifierAST)
						? ((IdentifierAST)child).getName() : "") + "[]";
					#lbc.setName(name);
				}
				RBRACK )+
            { 
                jparse.expr.TypeAST t =
                    new jparse.expr.TypeAST(#lbc.getName());
                #postfixExpression = #(t, #postfixExpression);
            }
			dot2:DOT^<AST=jparse.expr.IdentifierAST> cl2:"class"
			{
				name += #dot2.getText() + #cl2.getText();
				#dot2.setName(name);
			}

			// an array indexing operation
		|	LBRACK^<AST=jparse.expr.IndexAST> expression RBRACK

			// method invocation
			// The next line is not strictly proper; it allows x(3)(4) or
			//  x[2](4) which are not valid in Java.  If this grammar were used
			//  to validate a Java program a semantic check would be needed, or
			//   this rule would get really ugly...
		|	lp2:LPAREN^<AST=jparse.expr.MethodCallAST> expressionList
			RPAREN
			{ ((IdentifierAST)#lp2.getFirstChild()).setMethod(); }
		)*

		// possibly add on a post-increment or post-decrement.
		// allows INC/DEC on too much, but semantics can check
		(	in:INC^<AST=jparse.expr.UnaryArithAST> {#in.setType(POST_INC);}
	 	|	de:DEC^<AST=jparse.expr.UnaryArithAST> {#de.setType(POST_DEC);}
		)?
	;

// the basic element of an expression
protected
primaryExpression
// FIXME: New grammar has identPrimary here; do we need it?
	:	IDENT<AST=jparse.expr.IdentifierAST>
	|	constant
	|	"true"<AST=jparse.expr.BooleanLiteralAST>
	|	"false"<AST=jparse.expr.BooleanLiteralAST>
	|	"null"<AST=jparse.expr.NullLiteralAST>
	|	newExpression
	|	"this"<AST=jparse.expr.ThisLiteralAST>
	|	"super"<AST=jparse.expr.IdentifierAST>
	|	LPAREN^<AST=jparse.expr.ParenthesizedAST> assignmentExpression
		RPAREN
	|	builtInType 
	;

/*  object instantiation.
 *  Trees are built as illustrated by the following input/tree pairs:
 *  
 *  new T()
 *  
 *  new
 *   |
 *   T --  ELIST
 *           |
 *          arg1 -- arg2 -- .. -- argn
 *  
 *  new int[]
 *
 *  new
 *   |
 *  int -- ARRAY_DECLARATOR
 *  
 *  new int[] {1,2}
 *
 *  new
 *   |
 *  int -- ARRAY_DECLARATOR -- ARRAY_INIT
 *                                  |
 *                                EXPR -- EXPR
 *                                  |      |
 *                                  1      2
 *  
 *  new int[3]
 *  new
 *   |
 *  int -- ARRAY_DECLARATOR
 *                |
 *              EXPR
 *                |
 *                3
 *  
 *  new int[1][2]
 *  
 *  new
 *   |
 *  int -- ARRAY_DECLARATOR
 *               |
 *         ARRAY_DECLARATOR -- EXPR
 *               |              |
 *             EXPR             1
 *               |
 *               2
 *  
 */
protected
newExpression
	:	"new"^<AST=jparse.expr.NewAST> typ:type
		(	LPAREN expressionList RPAREN
			(anonymousClassBlock[(IdentifierAST)#typ])?

			//java 1.1
			// Note: This will allow bad constructs like
			//    new int[4][][3] {exp,exp}.
			//    There needs to be a semantic check here...
			// to make sure:
			//   a) [ expr ] and [ ] are not mixed
			//   b) [ expr ] and an init are not used together

		|	newArrayDeclarator (arrayInitializer)?
		)
	;

protected
anonymousClassBlock![IdentifierAST superclass]
	{ jparse.TypeAST type = null, oldType = jparse.TypeAST.currType; }
	:	{
			type = new jparse.TypeAST(superclass.getName());
			oldType.addAnonymous(FileAST.currFile.pkg, type);
			jparse.TypeAST.currType = type;
		}
		blk:classBlock
		{
			JavaAST.currSymTable = JavaAST.currSymTable.parent;
			#anonymousClassBlock = #(type, #blk);
			jparse.TypeAST.currType = oldType;
		}
	;

protected
newArrayDeclarator
	:	(
			// CONFLICT:
			// newExpression is a primaryExpression which can be
			// followed by an array index reference.  This is ok,
			// as the generated code will stay in this loop as
			// long as it sees an LBRACK (proper behavior)
			options { greedy = true; }
		:
			lb:LBRACK^ {#lb.setType(ARRAY_DECLARATOR);} (expression)? RBRACK
		)+
	;

protected
constant
	:	NUM_INT<AST=jparse.expr.NumLiteralAST>
	|	CHAR_LITERAL<AST=jparse.expr.CharLiteralAST>
	|	STRING_LITERAL<AST=jparse.expr.StringLiteralAST>
	|	NUM_FLOAT<AST=jparse.expr.FloatLiteralAST>
	;


//----------------------------------------------------------------------------
// The Java scanner
//----------------------------------------------------------------------------
class JavaLexer extends Lexer;
options {
	exportVocab=Java;      // call the vocabulary "Java"
	testLiterals=false;    // don't automatically test for literals
	k=4;                   // four characters of lookahead
	charVocabulary='\u0003'..'\u7FFE';
	// without inlining some bitset tests, couldn't do unicode;
	// I need to make ANTLR generate smaller bitsets; see
	// bottom of JavaLexer.java
	codeGenBitsetTestThreshold=20;
}

// Reserved words.
tokens {
	CONST = "const";
	GOTO = "goto";
}

// OPERATORS
QUESTION		:	'?'		;
LPAREN			:	'('		;
RPAREN			:	')'		;
LBRACK			:	'['		;
RBRACK			:	']'		;
LCURLY			:	'{'		;
RCURLY			:	'}'		;
COLON			:	':'		;
COMMA			:	','		;
ASSIGN			:	'='		;
EQUAL			:	"=="	;
LNOT			:	'!'		;
BNOT			:	'~'		;
NOT_EQUAL		:	"!="	;
DIV				:	'/'		;
DIV_ASSIGN		:	"/="	;
PLUS			:	'+'		;
PLUS_ASSIGN		:	"+="	;
INC				:	"++"	;
MINUS			:	'-'		;
MINUS_ASSIGN	:	"-="	;
DEC				:	"--"	;
STAR			:	'*'		;
STAR_ASSIGN		:	"*="	;
MOD				:	'%'		;
MOD_ASSIGN		:	"%="	;
SR				:	">>"	;
SR_ASSIGN		:	">>="	;
BSR				:	">>>"	;
BSR_ASSIGN		:	">>>="	;
GE				:	">="	;
GT				:	">"		;
SL				:	"<<"	;
SL_ASSIGN		:	"<<="	;
LE				:	"<="	;
LT				:	'<'		;
BXOR			:	'^'		;
BXOR_ASSIGN		:	"^="	;
BOR				:	'|'		;
BOR_ASSIGN		:	"|="	;
LOR				:	"||"	;
BAND			:	'&'		;
BAND_ASSIGN		:	"&="	;
LAND			:	"&&"	;
SEMI			:	';'		;

// Whitespace
WS	:	(	' '
		|	'\t'
		|	'\f'
            // handle newlines
		|	(	options {generateAmbigWarnings=false;}
			:	"\r\n"  // Evil DOS
			|	'\r'    // Macintosh
			|	'\n'    // Unix (the right way)
			)
			{ newline(); }
		)+
	;

// Single-line comments
SL_COMMENT
	:	"//"
		(~('\n'|'\r'))* ('\n'|'\r'('\n')?)?
		{ newline(); }
	;

// multiple-line comments
ML_COMMENT
	:	"/*"
		(	/*	'\r' '\n' can be matched in one alternative or by matching
				'\r' in one iteration and '\n' in another.  I am trying to
				handle any flavor of newline that comes in, but the language
				that allows both "\r\n" and "\r" and "\n" to all be valid
				newline is ambiguous.  Consequently, the resulting grammar
				must be ambiguous.  I'm shutting this warning off.
			 */
			options {
				generateAmbigWarnings=false;
			}
		:
			{ LA(2)!='/' }? '*'
		|	'\r' '\n'		{newline();}
		|	'\r'			{newline();}
		|	'\n'			{newline();}
		|	~('*'|'\n'|'\r')
		)*
		"*/"
	;

// character literals
CHAR_LITERAL
	:	'\'' ( ESC | ~('\''|'\n'|'\r'|'\\') ) '\''
	;

// string literals
STRING_LITERAL
	:	'"' (ESC|~('"'|'\\'|'\n'|'\r'))* '"'
	;

// escape sequence -- note that this is protected; it can only be called
//   from another lexer rule -- it will not ever directly return a token to
//   the parser
// There are various ambiguities hushed in this rule.  The optional
// '0'...'9' digit matches should be matched here rather than letting
// them go back to STRING_LITERAL to be matched.  ANTLR does the
// right thing by matching immediately; hence, it's ok to shut off
// the FOLLOW ambig warnings.
protected
ESC
	:	'\\'
		(	'n'
		|	'r'
		|	't'
		|	'b'
		|	'f'
		|	'"'
		|	'\''
		|	'\\'
		|	('u')+ HEX_DIGIT HEX_DIGIT HEX_DIGIT HEX_DIGIT
		|	'0'..'3'
			(
				options {
					warnWhenFollowAmbig = false;
				}
			:	'0'..'7'
				(
					options {
						warnWhenFollowAmbig = false;
					}
				:	'0'..'7'
				)?
			)?
		|	'4'..'7'
			(
				options {
					warnWhenFollowAmbig = false;
				}
			:	'0'..'7'
			)?
		)
	;

// hexadecimal digit (again, note it's protected!)
protected
HEX_DIGIT
	:	('0'..'9'|'A'..'F'|'a'..'f')
	;

// an identifier.  Note that testLiterals is set to true!  This means
// that after we match the rule, we look in the literals table to see
// if it's a literal or really an identifer
IDENT
	options {testLiterals=true;}
	:	('a'..'z'|'A'..'Z'|'_'|'$') ('a'..'z'|'A'..'Z'|'_'|'0'..'9'|'$')*
	;

// a numeric literal
NUM_INT
	{boolean isDecimal=false;}
	:	'.' {_ttype = DOT;}
			(('0'..'9')+ (EXPONENT)? (FLOAT_SUFFIX)? { _ttype = NUM_FLOAT; })?
	|	(	'0' {isDecimal = true;} // special case for just '0'
			(	('x'|'X')
				(											// hex
					// the 'e'|'E' and float suffix stuff look
					// like hex digits, hence the (...)+ doesn't
					// know when to stop: ambig.  ANTLR resolves
					// it correctly by matching immediately.  It
					// is therefor ok to hush warning.
					options {
						warnWhenFollowAmbig=false;
					}
				:	HEX_DIGIT
				)+
			|	//float or double with leading zero
				(('0'..'9')+ ('.'|EXPONENT|FLOAT_SUFFIX)) => ('0'..'9')+

			|	('0'..'7')+									// octal
			)?
		|	('1'..'9') ('0'..'9')*  {isDecimal=true;}		// non-zero decimal
		)
		(	('l'|'L')
		
		// only check to see if it's a float if looks like decimal so far
		|	{isDecimal}?
			(	'.' ('0'..'9')* (EXPONENT)? (FLOAT_SUFFIX)?
			|	EXPONENT (FLOAT_SUFFIX)?
			|	FLOAT_SUFFIX
			)
			{ _ttype = NUM_FLOAT; }
		)?
	;

// a couple protected methods to assist in matching floating point numbers
protected
EXPONENT
	:	('e'|'E') ('+'|'-')? ('0'..'9')+
	;

protected
FLOAT_SUFFIX
	:	'f'|'F'|'d'|'D'
	;
