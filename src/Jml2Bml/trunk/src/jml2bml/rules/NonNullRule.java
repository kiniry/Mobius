package jml2bml.rules;

import jml2bml.bytecode.BytecodeUtils;
import jml2bml.engine.BmlKeywords;
import jml2bml.engine.JmlTokens;
import jml2bml.engine.Symbols;

import com.sun.source.tree.AnnotationTree;
import com.sun.tools.javac.util.Context;

/**
 * Translates non_null annotations
 * 
 * @author Jedrek
 * 
 */
public class NonNullRule extends TranslationRule<String, Symbols> {
  private BytecodeUtils bytecodeUtils;

  public NonNullRule(Context context) {
    bytecodeUtils = context.get(BytecodeUtils.class);
  }

  @Override
  public String visitAnnotation(AnnotationTree node, Symbols p) {
    if (JmlTokens.NON_NULL.equals(node.getAnnotationType().toString())) {
      return BmlKeywords.NON_NULL;
    }
    return null;

  };
}
