package jml2bml.rules;

import jml2bml.bytecode.BytecodeUtils;
import jml2bml.engine.BmlKeywords;
import jml2bml.engine.JmlTokens;

import annot.bcclass.BCClass;

import com.sun.source.tree.AnnotationTree;
import com.sun.tools.javac.util.Context;

/**
 * Translates non_null annotations
 * 
 * @author Jedrek
 * 
 */
public class NonNullRule extends TranslationRule{
	private BytecodeUtils bytecodeUtils;
	private BCClass bclass;

	
	public NonNullRule(Context context) {
		bytecodeUtils = context.get(BytecodeUtils.class);
		bclass = context.get(BCClass.class);
	}

	@Override
	public String visitAnnotation(AnnotationTree node, Void p) {
		if (JmlTokens.NON_NULL.equals(node.getAnnotationType().toString()))
			return BmlKeywords.NON_NULL;
		return null;
		
	};
}
