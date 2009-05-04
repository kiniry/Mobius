/*
 * @title "Jml2Bml" @description "JML to BML Compiler" @copyright "(c)
 * 2008-01-06 University of Warsaw" @license "All rights reserved. This program
 * and the accompanying materials are made available under the terms of the LGPL
 * licence see LICENCE.txt file"
 */
package jml2bml.rules;

import javax.lang.model.element.ElementKind;

import jml2bml.bytecode.TypeSignature;
import jml2bml.exceptions.Jml2BmlException;
import jml2bml.symbols.Symbols;

import org.apache.bcel.generic.Type;
import org.jmlspecs.openjml.JmlTree.JmlVariableDecl;

import annot.bcclass.BCClass;
import annot.bcclass.BCField;
import annot.bcclass.BMLModifiersFlags;

import com.sun.source.tree.AnnotationTree;
import com.sun.source.tree.ModifiersTree;
import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.util.Context;

/**
 * Rule for translating modifiers.
 * @author kjk    (kjk@mimuw.edu.pl)
 *
 * @version 0-0.1
 */
public class ModifiersRule extends TranslationRule < String, Symbols > {
  private class ModifiersBuilder extends TranslationRule < String, Symbols > {
    public int modifiers = 0;
    @Override
    public String visitModifiers(final ModifiersTree node, final Symbols symb) {

      for(AnnotationTree annot: node.getAnnotations()){
        String annotation = annot.getAnnotationType().toString();
        if (annotation.equals("org.jmlspecs.annotations.NonNull")){
          modifiers = modifiers | BMLModifiersFlags.BML_NON_NULL;
        } else if (annotation.equals("org.jmlspecs.annotations.SpecPublic")){
          modifiers = modifiers | BMLModifiersFlags.BML_SPEC_PUBLIC;
        } else
          throw new Jml2BmlException("Unknown annotation:"+annotation);
      }
      return "";
    }
  }
  /**
   * Application context.
   */
  private final Context myContext;

  /**
   * Creates new instance of the AssertRule.
   * @param context application context
   */
  public ModifiersRule(final Context context) {
    super();
    this.myContext = context;
  }

  @Override
  public String visitJmlVariableDecl(final JmlVariableDecl node, final Symbols symb) {
    ModifiersBuilder builder = new ModifiersBuilder();
    node.mods.accept(builder, new Symbols(symb));
    if (builder.modifiers != 0){
      final Symbol varSymbol = node.sym;      
      final BCClass bcClazz = symb.findClass();
      String name = node.getName().toString();
      if (varSymbol.getKind() == ElementKind.FIELD){
        BCField field = new BCField(bcClazz);
        field.setName(name);
        field.setBMLFlags(builder.modifiers);
        String typeSignature = TypeSignature.getSignature(varSymbol.asType());
        field.setType(Type.getType(typeSignature));
        bcClazz.updateFields(field);
      } else {
        throw new Jml2BmlException("Unknown variable kind:" + node.sym.kind);
      }
    }    
    return "";
  }
}
