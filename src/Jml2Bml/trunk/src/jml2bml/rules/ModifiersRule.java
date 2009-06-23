/*
 * @title "Jml2Bml" @description "JML to BML Compiler" @copyright "(c)
 * 2008-01-06 University of Warsaw" @license "All rights reserved. This program
 * and the accompanying materials are made available under the terms of the LGPL
 * licence see LICENCE.txt file"
 */
package jml2bml.rules;

import java.util.Set;

import javax.lang.model.element.ElementKind;
import javax.lang.model.element.Modifier;

import jml2bml.bytecode.TypeSignature;
import jml2bml.exceptions.Jml2BmlException;
import jml2bml.symbols.Symbols;

import org.apache.bcel.generic.Type;
import org.jmlspecs.openjml.JmlTree.JmlVariableDecl;

import annot.bcclass.BCClass;
import annot.bcclass.BCField;
import annot.bcclass.BMLModifiersFlags;

import com.sun.org.apache.bcel.internal.Constants;
import com.sun.source.tree.AnnotationTree;
import com.sun.source.tree.ModifiersTree;
import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.tree.JCTree.JCModifiers;
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
    public int jmodifiers = 0;
    public int kind = BCField.JAVA_FIELD;
    @Override
    public String visitModifiers(final ModifiersTree node, final Symbols symb) {

      for(AnnotationTree annot: node.getAnnotations()){
        String annotation = annot.getAnnotationType().toString();
        if (annotation.equals("org.jmlspecs.annotations.NonNull")){
          modifiers = modifiers | BMLModifiersFlags.BML_NON_NULL;
        } else if (annotation.equals("org.jmlspecs.annotations.SpecPublic")){
          modifiers = modifiers | BMLModifiersFlags.BML_SPEC_PUBLIC;
        } else if (annotation.equals("org.jmlspecs.annotations.Ghost")){
          kind = BCField.GHOST_FIELD;
        } else if (annotation.equals("org.jmlspecs.annotations.Model")){
          kind = BCField.MODEL_FIELD;
        } else
          throw new Jml2BmlException("Unknown annotation:"+annotation);
      }
      for (Modifier modif: node.getFlags()){
        if (modif.equals(Modifier.ABSTRACT)){
          jmodifiers = jmodifiers | Constants.ACC_ABSTRACT;
        } else if (modif.equals(Modifier.FINAL)){
          jmodifiers = jmodifiers | Constants.ACC_FINAL;
        } else if (modif.equals(Modifier.NATIVE)){
          jmodifiers = jmodifiers | Constants.ACC_NATIVE;
        } else if (modif.equals(Modifier.PRIVATE)){
          jmodifiers = jmodifiers | Constants.ACC_PRIVATE;
        } else if (modif.equals(Modifier.PROTECTED)){
          jmodifiers = jmodifiers | Constants.ACC_PROTECTED;
        } else if (modif.equals(Modifier.PUBLIC)){
          jmodifiers = jmodifiers | Constants.ACC_PUBLIC;
        } else if (modif.equals(Modifier.STATIC)){
          jmodifiers = jmodifiers | Constants.ACC_STATIC;
        } else if (modif.equals(Modifier.STRICTFP)){
          jmodifiers = jmodifiers | Constants.ACC_STRICT;
        } else if (modif.equals(Modifier.SYNCHRONIZED)){
          jmodifiers = jmodifiers | Constants.ACC_SYNCHRONIZED;
        } else if (modif.equals(Modifier.TRANSIENT)){
          jmodifiers = jmodifiers | Constants.ACC_TRANSIENT;
        } else if (modif.equals(Modifier.VOLATILE)){
          jmodifiers = jmodifiers | Constants.ACC_VOLATILE;
        } else
          throw new Jml2BmlException("Unknown Java flag:"+modif);
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
        field.setAccessFlags(builder.jmodifiers);
        bcClazz.updateFields(field);
      } else {
        throw new Jml2BmlException("Unknown variable kind:" + node.sym.kind);
      }
    }
    return "";
  }
}
