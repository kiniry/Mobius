package jml2bml.engine;

import java.util.LinkedList;
import java.util.List;

import jml2bml.bytecode.BmlAnnotation;
import jml2bml.bytecode.BytecodeUtils;
import jml2bml.bytecode.Location;
import jml2bml.rules.TranslationRule;

import com.sun.source.tree.Tree;
import com.sun.tools.javac.comp.JmlEnter;
import com.sun.tools.javac.util.Context;

import experiments.ExtendedJmlTreeScanner;

/**
 * This visitor traverses the Tree and generates bml for jml annotations. All
 * the work is done in the preVisit method for the appropriate nodes. It tries
 * to apply all the defined rules. After an applicable rule (returned annotation
 * was not null) was found, next rules are not applied. User can define his own
 * translation rules. They have to extend the TranslationRule class and
 * overwrite appropriate visitXYZ methods. If such an rule is not applicable to
 * a node type, visit method for this node type should not be overwritten.
 * 
 * @author Jedrek
 * 
 */

public class Jml2BmlTranslator extends ExtendedJmlTreeScanner<Void, Boolean> {
	private List<TranslationRule> rules;
	private BytecodeUtils bytecodeUtils;
	private JmlEnter jmlEnter;

	public Jml2BmlTranslator(Context context) {
		this.rules = new LinkedList<TranslationRule>();
		this.bytecodeUtils = context.get(BytecodeUtils.class);
		this.jmlEnter = context.get(JmlEnter.class);
	}

	/**
	 * This method invokes the rule - tries to apply it to the given node.
	 * 
	 * @param node -
	 *            visited node
	 * @param v -
	 *            true, if we should try to apply the rule (we shouldn't if the
	 *            scanned node is a descendant of a node that we have already
	 *            translated
	 */
	@Override
	protected Boolean preVisit(Tree node, Boolean v) {
		super.preVisit(node, v);
		if (Boolean.FALSE.equals(v))
			return v;
		for (Class<?> cl : JmlNodes.JML_CLASSES)
			if (cl.equals(node.getClass())) {
				for (TranslationRule rule : rules) {
					// try to apply the rule
					String annotation = node.accept(rule, null);
					if (annotation != null) {
						// succeeded
						Location location = bytecodeUtils.findLocation(node);
						BmlAnnotation bml = new BmlAnnotation(annotation,
								location);
						bytecodeUtils.insertAnnotation(bml);
						return Boolean.FALSE;
					}
				}
				return v;
			}
		return v;
	}

	/**
	 * All user defined rules should be registered using this method. Not
	 * registered rules will not be applied.
	 * 
	 * @param rule -
	 *            rule to register.
	 */
	public void registerTranslationRule(TranslationRule rule) {
		rules.add(rule);
	}

}
