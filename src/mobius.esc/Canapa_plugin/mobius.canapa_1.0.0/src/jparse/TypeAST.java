/*
 * @(#)$Id: TypeAST.java,v 1.2 2004/04/02 05:48:47 james Exp $
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

import antlr.Token;
import antlr.collections.AST;
import java.lang.reflect.Modifier;
import java.util.ArrayList;

/**
 * An AST node that represents a type.
 *
 * @version $Revision: 1.2 $, $Date: 2004/04/02 05:48:47 $
 * @author Jerry James
 */
public final class TypeAST extends JavaAST implements JavaTokenTypes {

    /**
     * The type currently being parsed
     */
    static TypeAST currType;

    /**
     * The type object corresponding to this AST
     */
    SourceType type;

    /**
     * The fully qualified name of this type
     */
    String name;

    /**
     * The outer class for this type
     */
    TypeAST outer;

    /**
     * The inner classes of this class
     */
    TypeAST[] inner = new TypeAST[0];

    /**
     * The modifiers for this type
     */
    ModifierAST modifiers;

    /**
     * The superclass of this class
     */
    String superclass;

    /**
     * The interfaces implemented by this class or the superinterfaces of this
     * interface
     */
    String[] interfaces;

    /**
     * The constructors for this type
     */
    ConstrAST[] constructors;

    /**
     * The count of anonymous inner classes
     */
    private int anon = 0;

    /**
     * Create a new Type AST
     */
    public TypeAST() {
	this("java.lang.Object");
    }

    /**
     * Create a new Type AST
     *
     * @param name the name of the superclass
     */
    protected TypeAST(final String name) {
	super(new SymbolTable());
	setType(LITERAL_class);
	symTable.setEnclosingType(this);
	superclass = name;
    }

    /**
     * Create a new Type AST
     *
     * @param token the token represented by this AST node
     */
    protected TypeAST(final Token token) {
	super(token, new SymbolTable());
	symTable.setEnclosingType(this);
	superclass = "java.lang.Object";
    }

    /**
     * Set the name and outer class for this type
     *
     * @param pkg the name of the package for this type
     * @param typeName the name of this type
     * @param out the outer class or interface for this type
     * @param mods the modifiers for this class
     */
    protected void setInfo(final String pkg, final String typeName,
			   final TypeAST out, final ModifierAST mods) {
	name = (out != null || pkg == null) ? typeName : pkg + '.' + typeName;
	outer = out;
	modifiers = mods;
    }

    public void parseComplete() {
	final boolean oldIsField = context.isField;
	context.isField = true;
	for (JavaAST ast = (JavaAST)getFirstChild(); ast != null;
	     ast = (JavaAST)ast.getNextSibling()) {
	    context.nextStmt = null;
	    ast.parseComplete();
	}
	context.isField = oldIsField;
    }

    /**
     * Add a constructor to the list for this type
     *
     * @param cons the constructor to add to the list
     */
    protected void addConstructor(final ConstrAST cons) {
	// Make a bigger array, and add one to the end
	if (constructors != null) {
	    final ConstrAST[] newConstr =
		new ConstrAST[constructors.length + 1];
	    System.arraycopy(constructors, 0, newConstr, 0,
			     constructors.length);
	    newConstr[constructors.length] = cons;
	    constructors = newConstr;
	} else {
	    constructors = new ConstrAST[] { cons };
	}
    }

    /**
     * Add an anonymous inner class to the list
     *
     * @param pkg the name of the package for this type
     * @param type the anonymous inner class to add
     */
    void addAnonymous(final String pkg, final TypeAST type) {
	type.setInfo(pkg, name + '$' + ++anon, this,
		     new ModifierAST(Modifier.FINAL)); // See JLS 15.9.5
	addInner(type);
    }

    /**
     * Add an inner class to the list
     *
     * @param type the inner class to add
     */
    void addInner(final TypeAST type) {
	final int length = inner.length;
	final TypeAST[] newInner = new TypeAST[length + 1];
	System.arraycopy(inner, 0, newInner, 0, length);
	newInner[length] = type;
	inner = newInner;
	if (type.interfaces == null)
	    type.interfaces = new String[0];
	final Type t = new SourceType(type);
	Type.map.put(type.name, t);
    }

    /**
     * Get the name of the superclass of this class
     *
     * @return the name of the superclass of this class
     */
    public String getSuperclass() {
	return superclass;
    }

    /**
     * Get the members of this type
     *
     * @return an array containing the members (static and instance variables,
     * methods, and initializers) of this type
     */
    public JavaAST[] getMembers() {
	// Find the objblock
	AST ast;
	for (ast = getFirstChild(); ast != null && ast.getType() != OBJBLOCK;
	     ast = ast.getNextSibling());

	// Now make a list of the objblock's members
	final ArrayList list = new ArrayList();
	for (ast = ast.getFirstChild(); ast != null; ast=ast.getNextSibling()){
	    list.add(ast);
	}
	final JavaAST[] members = new JavaAST[list.size()];
	list.toArray(members);
	return members;
    }

    /**
     * Retrieve the type represented by this AST node
     *
     * @return the type of this AST node
     */
    public Type retrieveType() {
	return type;
    }

    public String toString() {
	return (modifiers.isInterface() ? "interface " : "class ") + name;
    }
}
