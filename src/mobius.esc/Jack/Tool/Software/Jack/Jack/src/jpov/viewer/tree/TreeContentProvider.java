//******************************************************************************
/* Copyright (c) 2002, 2003 GEMPLUS Software Research Labs. All Rights Reserved.
/* Copyright (c) 2003, 2004 INRIA. All Rights Reserved.
/*------------------------------------------------------------------------------
/* Name: TreeContentProvider.java
/*
/*******************************************************************************
/* Warnings/Remarks:
/******************************************************************************/
package jpov.viewer.tree;

import jack.plugin.perspective.ICaseExplorer;
import jpov.structure.Class;
import jpov.structure.JmlFile;
import jpov.structure.Lemma;
import jpov.structure.LemmaHierarchy;
import jpov.structure.Method;
import jpov.structure.Proofs;
import jpov.structure.TreeObject;

import org.eclipse.jface.viewers.ITreeContentProvider;
import org.eclipse.jface.viewers.Viewer;

/**
 * This class implements a content provider for the tree
 * @author L.Burdy
 **/
public class TreeContentProvider implements ITreeContentProvider {

	ICaseExplorer caseExp;

	/**
	 * @param explorer
	 */
	public TreeContentProvider(ICaseExplorer explorer) {
		caseExp = explorer;
	}

	/**
	 * Returns the children of a node, that is:
	 * <UL>
	 * <li> its classes for a JML file
	 * <li> its static initialization, constructors and methods for a class
	 * <li> its lemmas for a method
	 * <li> its goals for a lemma
	 * </UL>
	 **/
	public Object[] getChildren(Object parentElement) {
		if (parentElement instanceof JmlFile) {
			return ((JmlFile) parentElement).getClasses();
		} else if (parentElement instanceof Class) {
			Class c = (Class) parentElement;
			int wellDef = 0;
			if (c.getWellDefInvLemmas().getNbPo() > 0)
				wellDef = 1;
			Object[] res =
				new Object[c.getMethods().length
					+ c.getConstructors().length
					+ 1
					+ wellDef];
			// the first child is the static initialization lemmas
			res[0] = c.getStaticInitLemmas();
			if (wellDef == 1)
				res[1] = c.getWellDefInvLemmas();
			// then the constructors
			for (int i = 1 + wellDef;
				i < c.getConstructors().length + 1 + wellDef;
				i++)
				res[i] = c.getConstructors()[i - (1 + wellDef)];
			// then the methods    
			for (int i = c.getConstructors().length + 1 + wellDef;
				i
					< c.getConstructors().length
						+ c.getMethods().length
						+ 1
						+ wellDef;
				i++)
				res[i] =
					c.getMethods()[i
						- (c.getConstructors().length + 1 + wellDef)];
			return res;
		} else if (parentElement instanceof Method) {
			int i;
			Method m = (Method) parentElement;
			int wellDef = 0;
			if (m.getWellDefinednessLemmas().getNbPo() > 0)
				wellDef = 1;
			Object[] res =
				new Object[m.getLemmas().getLemmasWithPo(
					caseExp.getLayout()).length
					+ wellDef];
			for (i = 0;
				i < m.getLemmas().getLemmasWithPo(caseExp.getLayout()).length;
				i++)
				res[i] = m.getLemmas().getLemmasWithPo(caseExp.getLayout())[i];
			if (wellDef == 1)
				res[i] = m.getWellDefinednessLemmas();
			return res;
		} else if (parentElement instanceof Proofs) {
			return ((Proofs) parentElement).getLemmasWithPo(
				caseExp.getLayout());
		} else if (parentElement instanceof LemmaHierarchy) {
			return ((LemmaHierarchy) parentElement).getLemmasWithPo();
		} else if (parentElement instanceof Lemma) {
			return ((Lemma) parentElement).getGoals();
		}
		return new Object[0];
	}

	public Object[] getElements(Object inputElement) {
		return getChildren(inputElement);
	}

	public Object getParent(Object element) {
		if (element instanceof TreeObject) {
			return ((TreeObject) element).getParent();
		} else
			return null;
	}

	public boolean hasChildren(Object element) {
		if (element instanceof JmlFile) {
			return ((JmlFile) element).getClasses().length > 0;
		} else if (element instanceof Class) {
			return true;
		} else if (element instanceof Method) {
			Method m = (Method) element;
			if (m.getWellDefinednessLemmas().getNbPo() > 0)
				return true;
			else
				return m.getNbPo() > 0;
		} else if (element instanceof Proofs) {
			return ((Proofs) element).getLemmasWithPo(
				caseExp.getLayout()).length
				> 0;
		} else if (element instanceof LemmaHierarchy) {
			return ((LemmaHierarchy) element).getLemmasWithPo().length > 0;
		} else if (element instanceof Lemma) {
			return ((Lemma) element).getGoals().length > 0;
		} else
			return false;
	}

	public void inputChanged(Viewer viewer, Object oldInput, Object newInput) {
		// this.viewer = (TreeViewer) viewer;
		if (oldInput != null) {
			// removeListenerFrom((Class) oldInput);
		}
		if (newInput != null) {
			// addListenerTo((Class) newInput);
		}
	}

	public void dispose() {
	}

}
