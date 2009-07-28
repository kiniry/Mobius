/* Copyright 2000, 2001, Compaq Computer Corporation */

package javafe.parser;

import javafe.ast.*;
import javafe.util.StackVector;
import javafe.util.ErrorSet;

import javafe.util.CorrelatedReader;	// For test harness only
import javafe.util.Location;

/**
 * Parses java source.
 * 
 * <p> Uses the static <code>make*()</code> methods of the classes of
 * the <code>javafe.ast</code> package to create AST nodes.
 * 
 * <p> The main entry point is the method
 * {@link parseStream(CorrelatedReader, boolean)}.
 * 
 * <P>Each parsing method for a particular syntactic unit is
 * documented with appropriate grammar production rules for that
 * syntactic unit.  These grammar rules follow the conventions
 * described in "The Java Language Specification", with the addition
 * of the symbols '(', ')', '[', ']', '*', '+', and '|', which have
 * their usual meaning. When necessary, we denote the corresponding
 * concrete tokens using LPAREN, RPAREN, LSQBRACKET, RSQBRACKET, STAR,
 * PLUS and BITOR.
 * 
 * @see javafe.ast.ASTNode
 * @see javafe.ast.ParseStmt
 */

public class Parse extends ParseStmt
{
    public Parse() {
	//@ set seqTypeName.elementType = \type(TypeName)
	//@ set seqTypeName.owner = this

	//@ set seqFormalParaDecl.elementType = \type(FormalParaDecl)
	//@ set seqFormalParaDecl.owner = this

	//@ set seqImportDecl.elementType = \type(ImportDecl)
	//@ set seqImportDecl.owner = this

	//@ set seqTypeDecl.elementType = \type(TypeDecl)
	//@ set seqTypeDecl.owner = this
    }

    /**
     * Internal working storage for many Parse functions.
     */
    //@ invariant seqTypeName.elementType == \type(TypeName)
    //@ invariant seqTypeName.owner == this
    protected final /*@non_null*/ StackVector seqTypeName
	= new StackVector();

    /**
     * Internal working storage for many Parse functions.
     */
    //@ invariant seqFormalParaDecl.elementType == \type(FormalParaDecl)
    //@ invariant seqFormalParaDecl.owner == this
    protected final /*@non_null*/ StackVector seqFormalParaDecl
	= new StackVector();

    /**
     * Internal working storage for many Parse functions.
     */
    //@ invariant seqImportDecl.elementType == \type(ImportDecl)
    //@ invariant seqImportDecl.owner == this
    protected final /*@non_null*/ StackVector seqImportDecl
	= new StackVector();

    /**
     * Internal working storage for many Parse functions.
     */
    //@ invariant seqTypeDecl.elementType == \type(TypeDecl)
    //@ invariant seqTypeDecl.owner == this
    protected final /*@non_null*/ StackVector seqTypeDecl
	= new StackVector();


  /** Parse a <TT>CompilationUnit</TT> from an input stream.

    <P> Requires: prefix of <TT>in</TT> contains text from which the
    <TT>CompilationUnit</TT> non-terminal can be derrived.

    <P> Ensures: parses a <TT>CompilationUnit</TT> from the input
    stream, generating a syntax tree for it.  All errors are treated
    as fatal errors and are reporting through <code>ErrorSet</code>.

    @see javafe.util.ErrorSet
    */

  //@ requires in != null
  public CompilationUnit parseStream(CorrelatedReader in, boolean specOnly) {
    if (parseStreamLexer == null) parseStreamLexer = new Lex(null, true);
    parseStreamLexer.restart(in);
    return parseCompilationUnit(parseStreamLexer, specOnly);
  }


  private Lex parseStreamLexer;

  /** Parse a <TT>CompilationUnit</TT>.
      <PRE>
      CompilationUnit:
         [Package name ;] ImportDeclaration* TypeDeclaration*
      </PRE>
      To handle pragmas, call this method directly 
      with an appropriate <TT>Lex</TT> object.
    */
  // specOnly means parse without keeping the bodies of methods/constructors/..

  //@ requires l != null && l.m_in != null
  //@ ensures \result != null
  public CompilationUnit parseCompilationUnit(Lex l, boolean specOnly) {
    Name pkgName = null;
    int loc = l.startingLoc;


    /* Optional PackageDeclaration: package name ; */
    if( l.ttype == TagConstants.PACKAGE ) {
      l.getNextToken();
      pkgName = parseName(l);
      expect( l, TagConstants.SEMICOLON );
    } 

    /* Import Declarations */
    seqImportDecl.push();
    while( l.ttype == TagConstants.IMPORT ) { 
      seqImportDecl.addElement( parseImportDeclaration( l ) );
    }
    ImportDeclVec imports = ImportDeclVec.popFromStackVector(seqImportDecl);

    /* Type Declarations */
    seqTypeDecl.push();
    while( l.ttype != TagConstants.EOF ) {
      if( l.ttype == TagConstants.SEMICOLON )
        l.getNextToken();
      else
	seqTypeDecl.addElement( parseTypeDeclaration(l, specOnly) );
    }
    TypeDeclVec elems = TypeDeclVec.popFromStackVector( seqTypeDecl );

    LexicalPragmaVec lexicalPragmas = l.getLexicalPragmas();

    return CompilationUnit.make(pkgName, lexicalPragmas, 
				imports, elems, loc );
  }

  /** Parse an <TT>ImportDeclaration</TT>.
    <PRE>
    ImportDeclaration:
      import Name ; 
      import Name . STAR ;
    </PRE>
   */
        
  //@ requires l != null && l.m_in != null
  //@ ensures \result != null
  protected ImportDecl parseImportDeclaration(Lex l) {
    int loc = l.startingLoc;
    l.getNextToken();                // swallow import keyword
    Name name = parseName(l);
    if( l.ttype == TagConstants.SEMICOLON ) {
      l.getNextToken();              // swallow semicolon
      TypeName typename = TypeName.make( name );
      return SingleTypeImportDecl.make( loc, typename );
    } else {
      expect( l, TagConstants.FIELD );
      expect( l, TagConstants.STAR );
      expect( l, TagConstants.SEMICOLON );
      return OnDemandImportDecl.make( loc, name );
    }
  }


  /**********************************************************************
    Parse a <TT>TypeDeclaration</TT> (ie a class or interface declaration).
    <PRE>
      TypeDeclaration:
        ClassDeclaration
        InterfaceDeclaration  
        ;

      ClassDeclaration:
        TypeDeclElemPragma* Modifiers class Identifier [extends TypeName] [implements TypeNameList]
          { TypeDeclElem* }
	TypeDeclElemPragma* Modifiers interface Identifier [extends TypeNameList]
          { TypeDeclElem* }
     </PRE>
   */

  //@ requires l != null && l.m_in != null
  //@ ensures \result != null
  TypeDecl parseTypeDeclaration(Lex l, boolean specOnly) {
    TypeDeclElemVec extras = null;
    if (l.ttype == TagConstants.TYPEDECLELEMPRAGMA) {
      seqTypeDeclElem.push();
      while (l.ttype == TagConstants.TYPEDECLELEMPRAGMA) {
	TypeDeclElemPragma pragma = (TypeDeclElemPragma)l.auxVal;
	seqTypeDeclElem.addElement( pragma );
	l.getNextToken();
      }
      extras = TypeDeclElemVec.popFromStackVector(seqTypeDeclElem);
    }
    int loc = l.startingLoc;
    int modifiers = parseModifiers(l);
    ModifierPragmaVec modifierPragmas = this.modifierPragmas;
    TypeDecl result =
	parseTypeDeclTail(l, specOnly, loc, modifiers, modifierPragmas);
    if (extras != null) {
	for (int i = 0; i < extras.size(); i++) {
	  extras.elementAt(i).setParent(result);
	}
	extras.append(result.elems);
	result.elems = extras;
    }
    return result;
  }

  /**********************************************************************
    Parse a <TT>TypeDeclTail</TT> (ie a class or interface declaration
    starting at the keyword 'class' or 'interface').
    <PRE>
      TypeDeclTail:
        class Identifier [TypeModifierPragma]* [extends TypeName] [implements TypeNameList]
          { TypeDeclElem* }
        interface Identifier [TypeModifierPragma]* [extends TypeNameList] { TypeDeclElem* }
     </PRE> */

  TypeDecl parseTypeDeclTail(Lex l, boolean specOnly, int loc, 
			     int modifiers, ModifierPragmaVec modifierPragmas){
    int keyword = l.ttype;
   
    if( keyword != TagConstants.CLASS && keyword != TagConstants.INTERFACE )
      fail(l.startingLoc, "expected 'class' or 'interface'");

    l.getNextToken();              // swallow keyword

    int locId = l.startingLoc;
    Identifier id = parseIdentifier(l);
    TypeModifierPragmaVec tmodifiers = parseTypeModifierPragmas(l);
    
    /* Parse superclass, if any */
    TypeName superClass = null;
    if( keyword == TagConstants.CLASS && l.ttype == TagConstants.EXTENDS ) {
      l.getNextToken();            // swallow "extends" keyword
      superClass = parseTypeName(l);
    }

    /* Parse super interfaces, if any */
    TypeNameVec superInterfaces =
      parseTypeNames( l, (keyword == TagConstants.CLASS ? 
			  TagConstants.IMPLEMENTS : TagConstants.EXTENDS ) );

    /* Now parse class body */
    int locOpenBrace = l.startingLoc;
    expect( l, TagConstants.LBRACE );
    
    /* Build up Vec of TypeDeclElems in class or interface */
    seqTypeDeclElem.push();
    while( l.ttype != TagConstants.RBRACE ) {
      parseTypeDeclElemIntoSeqTDE( l, keyword, id, specOnly );
    }
    TypeDeclElemVec elems =
	TypeDeclElemVec.popFromStackVector( seqTypeDeclElem );

    int locCloseBrace = l.startingLoc;
    expect( l, TagConstants.RBRACE );

    TypeDecl result;
    if (keyword == TagConstants.CLASS) {
      addDefaultConstructor(elems, locOpenBrace);
      result = ClassDecl.make(modifiers, modifierPragmas, id, 
			      superInterfaces, tmodifiers, elems,
			      loc, locId, locOpenBrace, locCloseBrace,
			      superClass);
    } else {
      result = InterfaceDecl.make(modifiers, modifierPragmas, id,
				  superInterfaces, tmodifiers, elems,
				  loc, locId, 
				  locOpenBrace, locCloseBrace );
    }
    result.specOnly = specOnly;
    return result;
  }
    

  /** checks for           X TypeModifierPragma* (
      in the input stream. 
      Use this to match the beginning of a constructor or method declration
      versus the beginning of a field declaration.
  */
    //@ requires l != null && l.m_in != null
    private boolean atStartOfConstructorOrMethod(Lex l) {
	int i = 1;
	while ((l.lookahead(i) == TagConstants.TYPEMODIFIERPRAGMA)) {
	    i++;
	}
	return l.lookahead(i) == TagConstants.LPAREN;
    }




  /** If no constructors are found in "elems", adds a default one to it.
    If a default constructor is created, the "loc" and "locId" fields of
    the default constructor will be set to "loc". */
  void addDefaultConstructor(TypeDeclElemVec elems, int loc) {
      // Return if a constructor is already present:
      for (int i=0; i<elems.size(); i++) {
	  if (elems.elementAt(i) instanceof ConstructorDecl)
	      return;
      }

      /*
       * No constructor found, add one:
       *  name() { super(); }
       *
       * Don't put super constructor invocation in --  it is added by
       * the type checker.
       */
      BlockStmt blk = BlockStmt.make(StmtVec.make(), loc, loc);
      TypeNameVec raises = TypeNameVec.make();
      FormalParaDeclVec formals = FormalParaDeclVec.make();
      ConstructorDecl cd
	  = ConstructorDecl.make(Modifiers.ACC_PUBLIC, null, null, 
				 formals, raises, blk, loc, loc, loc,
				 Location.NULL );
      cd.implicit = true;
      elems.addElement(cd);
  }

  /** Parse a keyword, 
      followed by a comma-separated list of <TT>TypeName</TT>s.

      Used to parse throws clauses, and super-interface clauses.
      <PRE>
      TypeNames:
         keyword TypeNameList
         empty

      TypeNameList:
        TypeName ( , TypeName )*
      </PRE>
   */

  //@ requires l != null && l.m_in != null
  //@ ensures \result != null
  protected TypeNameVec parseTypeNames(Lex l, int keyword)
  {
    if( l.ttype != keyword ) 
      return TypeNameVec.make();

    /* Have type names */
    seqTypeName.push();
    do {
      // Skip keyword or ',' .
      l.getNextToken();
      seqTypeName.addElement( parseTypeName(l) );
    } while( l.ttype == TagConstants.COMMA );
    return TypeNameVec.popFromStackVector( seqTypeName );
  }
  
/************************************************************************ 

Parse a <TT>TypeDeclElem</TT>, which is either a field, method, or
constructor declaration, a static block, or a TypeDecl [1.1].  

<p> A field declaration may define many fields.  Since returning
multiple declared entities is cumbersome, this method simply adds all
the declared entities onto the StackVector seqTypeDeclElem.  The
<TT>keyword</TT> argument is either CLASS or INTERFACE.  The argument
containerId is the name of the enclosing class, which is necessary for
checking constructor declarations.

<PRE>
TypeDeclElem: 
   FieldDeclaration 
   MethodDeclaration
   ConstructorDeclaration 
   InitBlock
   TypeDeclElemPragma
   TypeDeclaration              [1.1]
   ;

FieldDeclaration:
   Modifiers Type VariableDeclarator (, VariableDeclarator)* ;

MethodDeclaration:
   Modifiers Type Identifier FormalParameterList BracketPair*
      [throws TypeNameList]
      ( ; | Block )

ConstructorDeclaration:
   Modifiers Identifier FormalParameterList Block

InitBlock:
   Modifiers Block

VariableDeclarator:
   Identifier BRACKET_PAIR* [ = VariableInitializer ]

</PRE>

@see javafe.parser.TagConstants

*/

  void parseTypeDeclElemIntoSeqTDE(Lex l, int keyword, Identifier containerId,
				   boolean specOnly)			
  {
    int loc = l.startingLoc;
    int modifiers = parseModifiers(l);
    ModifierPragmaVec modifierPragmas = this.modifierPragmas;

    if( l.ttype == TagConstants.SEMICOLON 
       && modifiers == Modifiers.NONE
       && modifierPragmas == null ) {
      // Semicolons are not in JLS, 
      // but accepted by javac and in many java progs
      // so allow them and do nothing
      l.getNextToken();
      return;
    } 
    else if( l.ttype == TagConstants.CLASS 
	  || l.ttype == TagConstants.INTERFACE) {
      /* Nested class/interface */
      TypeDecl nested = parseTypeDeclaration(l, specOnly);
      nested.modifiers = modifiers;
      nested.pmodifiers = modifierPragmas;
      seqTypeDeclElem.addElement(nested);
      return;
    } 
    else if( l.ttype == TagConstants.LBRACE ) {
      /* Initialization block */
      if( keyword == TagConstants.INTERFACE ) 
        fail(l.startingLoc, 
	     "Cannot have initializer blocks in an interface");
      if (specOnly)
	parseBlock(l, true);
      else
	seqTypeDeclElem.addElement( InitBlock.make( modifiers, modifierPragmas,
						    parseBlock(l,false) ) );
      return;
    } 
    else if( atStartOfConstructorOrMethod(l) ) {
      // Constructor declaration 
      if( keyword == TagConstants.INTERFACE ) 
        fail(l.startingLoc, "Cannot declare constructors in an interface");
      int locId = l.startingLoc;
      Identifier id = parseIdentifier(l);
      TypeModifierPragmaVec tmodifiers = parseTypeModifierPragmas(l);
      if (id != containerId) {
	  if (containerId.toString().startsWith("$anon_"))
	      fail(l.startingLoc,
		   "Anonymous classes may not have constructors");
	  else
	      fail(l.startingLoc, 
		   "Invalid name '"+id+"' for constructor;"
		   +" expected '"+containerId+"'");
      }

      FormalParaDeclVec args = parseFormalParameterList(l);
      int locThrowsKeyword;
      if (l.ttype == TagConstants.THROWS) {
	locThrowsKeyword = l.startingLoc;
      } else {
	locThrowsKeyword = Location.NULL;
      }
      TypeNameVec raises = parseTypeNames( l, TagConstants.THROWS );

      // allow more modifier pragmas
      modifierPragmas = parseMoreModifierPragmas( l, modifierPragmas );
      BlockStmt body = null;
      int locOpenBrace = Location.NULL;
      if ( l.ttype == TagConstants.SEMICOLON ) {
          l.getNextToken();   // swallow semicolon
      } else {
	  locOpenBrace = l.startingLoc;
	  // specOnly means do not keep any bodies of methods/constructors/etc.
	  body = specOnly ? parseBlock(l, true)
				    : parseConstructorBody(l);

      }
      seqTypeDeclElem.addElement( ConstructorDecl.make( modifiers,
							modifierPragmas,
							tmodifiers,
							args, 
							raises, body,
							locOpenBrace,
							loc, locId, 
							locThrowsKeyword ) );
      return;
    } 
    else if( l.ttype == TagConstants.TYPEDECLELEMPRAGMA ) {
      // TypeDeclElemPragma
// Model methods have modifiers, so this cannot be forbidden
//      if( modifiers != Modifiers.NONE || modifierPragmas != null )
//	fail(l.startingLoc, 
//	     "Cannot have modifiers on a TypeDeclElem pragma");
      TypeDeclElemPragma pragma = (TypeDeclElemPragma)l.auxVal;
      pragma.decorate(modifierPragmas);
      seqTypeDeclElem.addElement( pragma );
      l.getNextToken();
    }
    else {
      /* Is field or method declaration */
      int locType = l.startingLoc;
      Type type = parseType(l);
      if(  atStartOfConstructorOrMethod(l) ) {
        // Method declaration 
        
        int locId              = l.startingLoc;
        Identifier id          = parseIdentifier(l);
	TypeModifierPragmaVec tmodifiers = parseTypeModifierPragmas(l);
        FormalParaDeclVec args = parseFormalParameterList(l);
        type = parseBracketPairs( l, type );
	int locThrowsKeyword;
	if (l.ttype == TagConstants.THROWS) {
	  locThrowsKeyword = l.startingLoc;
	} else {
	  locThrowsKeyword = Location.NULL;
	}
        TypeNameVec raises     = parseTypeNames(l, TagConstants.THROWS );
	int locOpenBrace;
        BlockStmt body;

	// Allow some more modifier pragmas here
	modifierPragmas = parseMoreModifierPragmas( l, modifierPragmas );

        if ( l.ttype == TagConstants.SEMICOLON ) {
          l.getNextToken();   // swallow semicolon
	  locOpenBrace = Location.NULL;
          body = null;
// FIXME - check that this is specOnly for no body ?
        } else {
          if( keyword == TagConstants.INTERFACE ) 
            fail(l.startingLoc, 
		 "Cannot define a method body inside an interface");
	  locOpenBrace = l.startingLoc;
          body = parseBlock(l, specOnly);
        }
        MethodDecl md = MethodDecl.make(modifiers, modifierPragmas, tmodifiers,
					args, 
					raises, body, locOpenBrace,
                                        loc, locId, locThrowsKeyword,
					id, type, locType);
        seqTypeDeclElem.addElement( md );
        return;

      } else {

        // Field declaration. 
        
        // Have modifiers and type. 
        // May need to loop over many VariableDeclarators 

	// make modifierPragmas non-null, so can retroactively extend
	if( modifierPragmas == null )
	  modifierPragmas = ModifierPragmaVec.make();

        for(;;) {
          int locId     = l.startingLoc;
          Identifier id = parseIdentifier(l);
          Type vartype = parseBracketPairs(l, type);

          VarInit init = null;
	  int locAssignOp = Location.NULL;
          if( l.ttype == TagConstants.ASSIGN ) {
	    locAssignOp = l.startingLoc;
            l.getNextToken();
            init = parseVariableInitializer(l, specOnly);
          }
          FieldDecl fielddecl
	    = FieldDecl.make(modifiers, modifierPragmas, 
			     id, vartype, locId, init, locAssignOp );
          seqTypeDeclElem.addElement( fielddecl );

          if(l.ttype == TagConstants.MODIFIERPRAGMA
		    || l.ttype == TagConstants.SEMICOLON ) 
	  {
	    // if modifier pragma, retroactively add to modifierPragmas
	    parseMoreModifierPragmas( l, modifierPragmas );

	    // End of Declaration 
            l.getNextToken();
            return;
          } else {
            expect( l, TagConstants.COMMA );
            /* And go around loop again */
          }
        } /* loop thru field declarations */
      } /* is field declarations */
    } /* field or method declarations */
  } /* parseTypeDeclElemIntoSeqTDE */

  /**********************************************************************
    Parse a <TT>FormalParameterList</TT>, which includes enclosing parens.
    Note: this definition differs from JLS, where it does not include the
    parens

    <PRE>
      FormalParameterList:
        LPAREN FormalParameter (, FormalParameter)* RPAREN

      FormalParameter:
        [Modifiers] Type Identifier BracketPair* ModifierPragma*     [1.1]
    <PRE>       
   */

  //@ requires l != null && l.m_in != null
  //@ ensures \result != null
  public FormalParaDeclVec parseFormalParameterList(Lex l) 
  {
    /* Should be on LPAREN */
    if( l.ttype != TagConstants.LPAREN ) 
      fail(l.startingLoc, "Expected open paren");
    if( l.lookahead(1) == TagConstants.RPAREN ) {
      // Empty parameter list
      expect( l, TagConstants.LPAREN );
      expect( l, TagConstants.RPAREN );
      return FormalParaDeclVec.make();
    } else {
      seqFormalParaDecl.push();
      while( l.ttype != TagConstants.RPAREN ) {
        l.getNextToken();                // swallow open paren or comma
	int modifiers = parseModifiers(l);
	ModifierPragmaVec modifierPragmas = this.modifierPragmas;
        Type type = parseType(l);
        int locId = l.startingLoc;
        Identifier id = parseIdentifier(l);
        type = parseBracketPairs(l, type);
	modifierPragmas = parseMoreModifierPragmas(l, modifierPragmas);
        seqFormalParaDecl.addElement( FormalParaDecl.make(modifiers,
							  modifierPragmas, 
							  id, type, locId ) );
        if( l.ttype != TagConstants.RPAREN && l.ttype != TagConstants.COMMA )
          fail(l.startingLoc, "Expected comma or close paren");
      }
      expect( l, TagConstants.RPAREN );
      return FormalParaDeclVec.popFromStackVector( seqFormalParaDecl );
    }
  }
}
