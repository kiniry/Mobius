/*
    This library is free software; you can redistribute it and/or
    modify it under the terms of the GNU General Public
    License as published by the Free Software Foundation; either
    version 2 of the license, or (at your option) any later version.
*/

package org.gjt.jclasslib.browser.detail;

import java.awt.BorderLayout;
import java.awt.CardLayout;
import java.util.HashMap;

import javax.swing.BorderFactory;
import javax.swing.JPanel;
import javax.swing.border.Border;
import javax.swing.tree.TreePath;

import org.gjt.jclasslib.browser.AbstractDetailPane;
import org.gjt.jclasslib.browser.BrowserServices;
import org.gjt.jclasslib.browser.detail.attributes.CodeAttributeDetailPane;
import org.gjt.jclasslib.browser.detail.attributes.ConstantValueAttributeDetailPane;
import org.gjt.jclasslib.browser.detail.attributes.ExceptionsAttributeDetailPane;
import org.gjt.jclasslib.browser.detail.attributes.GenericAttributeDetailPane;
import org.gjt.jclasslib.browser.detail.attributes.InnerClassesAttributeDetailPane;
import org.gjt.jclasslib.browser.detail.attributes.LineNumberTableAttributeDetailPane;
import org.gjt.jclasslib.browser.detail.attributes.LocalVariableTableAttributeDetailPane;
import org.gjt.jclasslib.browser.detail.attributes.SourceFileAttributeDetailPane;
import org.gjt.jclasslib.browser.detail.jmlattributes.AssertAttributeDetailPane;
import org.gjt.jclasslib.browser.detail.jmlattributes.BlockSpecificationAttributeDetailPane;
import org.gjt.jclasslib.browser.detail.jmlattributes.ClassInvariantDetailPane;
import org.gjt.jclasslib.browser.detail.jmlattributes.ConstraintDetailPane;
import org.gjt.jclasslib.browser.detail.jmlattributes.LoopSpecificationAttributeDetailPane;
import org.gjt.jclasslib.browser.detail.jmlattributes.MethodSpecificationAttributeDetailPane;
import org.gjt.jclasslib.browser.detail.jmlattributes.ModelFieldAttributeDetailPane;
import org.gjt.jclasslib.structures.AttributeInfo;
import org.gjt.jclasslib.structures.attributes.CodeAttribute;
import org.gjt.jclasslib.structures.attributes.ConstantValueAttribute;
import org.gjt.jclasslib.structures.attributes.ExceptionsAttribute;
import org.gjt.jclasslib.structures.attributes.InnerClassesAttribute;
import org.gjt.jclasslib.structures.attributes.LineNumberTableAttribute;
import org.gjt.jclasslib.structures.attributes.LocalVariableTableAttribute;
import org.gjt.jclasslib.structures.attributes.SourceFileAttribute;
import org.gjt.jclasslib.structures.jmlattributes.AssertAttribute;
import org.gjt.jclasslib.structures.jmlattributes.BlockSpecificationAttribute;
import org.gjt.jclasslib.structures.jmlattributes.ClassInvariantAttribute;
import org.gjt.jclasslib.structures.jmlattributes.ConstraintAttribute;
import org.gjt.jclasslib.structures.jmlattributes.LoopSpecificationAttribute;
import org.gjt.jclasslib.structures.jmlattributes.MethodSpecificationAttribute;
import org.gjt.jclasslib.structures.jmlattributes.ModelFieldAttribute;

/**
    Detail pane for an attribute of class <tt>org.gjt.jclasslib.structures.AttributeInfo</tt>.
    This class is a container for the classes defined in the <tt>attributes</tt> 
    subpackage and switches between the contained panes as required.
 
    @author <a href="mailto:jclasslib@ej-technologies.com">Ingo Kegel</a>
    @version $Revision: 1.2 $ $Date: 2004/06/07 09:01:21 $
*/
public class AttributeDetailPane extends AbstractDetailPane {

	private static final String SCREEN_UNKNOWN = "Unknown";
	private static final String SCREEN_CONSTANT_VALUE = "ConstantValue";
	private static final String SCREEN_CODE = "Code";
	private static final String SCREEN_EXCEPTIONS = "Exceptions";
	private static final String SCREEN_INNER_CLASSES = "InnerClasses";
	private static final String SCREEN_SOURCE_FILE = "SourceFile";
	private static final String SCREEN_LINE_NUMBER_TABLE = "LineNumberTable";
	private static final String SCREEN_LOCAL_VARIABLE_TABLE =
		"LocalVariableTable";

	//Added for JML
	private static final String SCREEN_METHOD_SPECIFICATION =
		"MethodSpecification";
	private static final String SCREEN_ASSERT = "Assert";
	private static final String SCREEN_LOOP_SPECIFICATION = "LoopSpecification";
	private static final String SCREEN_BLOCK_SPECIFICATION = "BlockSpecification";
	private static final String SCREEN_MODEL_FIELD = "ModelField";
	private static final String SCREEN_CLASS_INVARIANT = "ClassInvariant";
	private static final String SCREEN_CONSTRAINT = "Constraint";

	private HashMap attributeTypeToDetailPane;

	// Visual components

	private JPanel specificInfoPane;
	private GenericAttributeDetailPane genericInfoPane;

	/**
	    Constructor.
	    @param services the associated browser services.
	 */
	public AttributeDetailPane(BrowserServices services) {
		super(services);
	}

	protected void setupComponent() {

		buildGenericInfoPane();
		buildSpecificInfoPane();

		setLayout(new BorderLayout());

		add(genericInfoPane, BorderLayout.NORTH);
		add(specificInfoPane, BorderLayout.CENTER);

	}

	public void show(TreePath treePath) {

		AttributeInfo attribute = findAttribute(treePath);

		String paneName = null;
		if (attribute instanceof ConstantValueAttribute) {
			paneName = SCREEN_CONSTANT_VALUE;
		} else if (attribute instanceof CodeAttribute) {
			paneName = SCREEN_CODE;
		} else if (attribute instanceof ExceptionsAttribute) {
			paneName = SCREEN_EXCEPTIONS;
		} else if (attribute instanceof InnerClassesAttribute) {
			paneName = SCREEN_INNER_CLASSES;
		} else if (attribute instanceof SourceFileAttribute) {
			paneName = SCREEN_SOURCE_FILE;
		} else if (attribute instanceof LineNumberTableAttribute) {
			paneName = SCREEN_LINE_NUMBER_TABLE;
		} else if (attribute instanceof LocalVariableTableAttribute) {
			paneName = SCREEN_LOCAL_VARIABLE_TABLE;
		} else if (attribute instanceof MethodSpecificationAttribute) {
			paneName = SCREEN_METHOD_SPECIFICATION;
		} else if (attribute instanceof AssertAttribute) {
			paneName = SCREEN_ASSERT;
		} else if (attribute instanceof LoopSpecificationAttribute) {
			paneName = SCREEN_LOOP_SPECIFICATION;
		} else if (attribute instanceof BlockSpecificationAttribute) {
			paneName = SCREEN_BLOCK_SPECIFICATION;
		} else if (attribute instanceof ModelFieldAttribute) {
			paneName = SCREEN_MODEL_FIELD;
		} else if (attribute instanceof ClassInvariantAttribute) {
			paneName = SCREEN_CLASS_INVARIANT;
		} else if (attribute instanceof ConstraintAttribute) {
			paneName = SCREEN_CONSTRAINT;			
		}

		CardLayout layout = (CardLayout) specificInfoPane.getLayout();
		if (paneName == null) {
			layout.show(specificInfoPane, SCREEN_UNKNOWN);
		} else {
			AbstractDetailPane pane =
				(AbstractDetailPane) attributeTypeToDetailPane.get(paneName);
			pane.show(treePath);
			layout.show(specificInfoPane, paneName);
		}

		genericInfoPane.show(treePath);
	}

	/**
	    Get the <tt>CodeAttributeDetailPane</tt> showing the details of a
	    <tt>Code</tt> attribute.
	    @return the <tt>CodeAttributeDetailPane</tt>
	 */
	public CodeAttributeDetailPane getCodeAttributeDetailPane() {
		return (CodeAttributeDetailPane) attributeTypeToDetailPane.get(
			SCREEN_CODE);
	}

	private void buildGenericInfoPane() {

		genericInfoPane = new GenericAttributeDetailPane(services);
		genericInfoPane.setBorder(createTitledBorder("Generic info:"));
	}

	private void buildSpecificInfoPane() {

		specificInfoPane = new JPanel();
		specificInfoPane.setBorder(createTitledBorder("Specific info:"));

		specificInfoPane.setLayout(new CardLayout());
		attributeTypeToDetailPane = new HashMap();
		JPanel pane;

		pane = new JPanel();
		specificInfoPane.add(pane, SCREEN_UNKNOWN);

		addScreen(
			new ConstantValueAttributeDetailPane(services),
			SCREEN_CONSTANT_VALUE);

		addScreen(new CodeAttributeDetailPane(services), SCREEN_CODE);

		addScreen(
			new ExceptionsAttributeDetailPane(services),
			SCREEN_EXCEPTIONS);

		addScreen(
			new InnerClassesAttributeDetailPane(services),
			SCREEN_INNER_CLASSES);

		addScreen(
			new SourceFileAttributeDetailPane(services),
			SCREEN_SOURCE_FILE);

		addScreen(
			new LineNumberTableAttributeDetailPane(services),
			SCREEN_LINE_NUMBER_TABLE);

		addScreen(
			new LocalVariableTableAttributeDetailPane(services),
			SCREEN_LOCAL_VARIABLE_TABLE);

		//Added for JML
		addScreen(
			new MethodSpecificationAttributeDetailPane(services),
			SCREEN_METHOD_SPECIFICATION);
		addScreen(new AssertAttributeDetailPane(services), SCREEN_ASSERT);
		addScreen(
			new LoopSpecificationAttributeDetailPane(services),
			SCREEN_LOOP_SPECIFICATION);
		addScreen(
			new BlockSpecificationAttributeDetailPane(services),
			SCREEN_BLOCK_SPECIFICATION);
		addScreen(
			new ModelFieldAttributeDetailPane(services),
			SCREEN_MODEL_FIELD);
		addScreen(
			new ClassInvariantDetailPane(services),
			SCREEN_CLASS_INVARIANT);
		addScreen(
			new ConstraintDetailPane(services),
			SCREEN_CONSTRAINT);
	}

	private void addScreen(AbstractDetailPane detailPane, String name) {

		if (detailPane instanceof FixedListDetailPane) {
			specificInfoPane.add(
				((FixedListDetailPane) detailPane).getScrollPane(),
				name);
		} else {
			specificInfoPane.add(detailPane, name);
		}
		attributeTypeToDetailPane.put(name, detailPane);
	}

	private Border createTitledBorder(String title) {
		Border simpleBorder = BorderFactory.createEtchedBorder();
		Border titledBorder =
			BorderFactory.createTitledBorder(simpleBorder, title);

		return titledBorder;
	}
}
