package prover.gui.editor.outline;


import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.views.contentoutline.ContentOutlinePage;

import prover.gui.editor.ProverEditor;
import prover.gui.editor.outline.types.FileType;
import prover.gui.editor.outline.types.ProverType;

public class BasicContentOutline extends ContentOutlinePage {
    private TreeViewer tree;
	private ProverEditor fEditor;

	public BasicContentOutline(ProverEditor editor) {
		fEditor = editor;
	}

	public void createControl(Composite parent) {
    	super.createControl(parent);
    	tree = this.getTreeViewer();
    	tree.setContentProvider(new TypeContentProvider());
    	tree.setLabelProvider(new TypeLabelProvider());
    	tree.setInput(getInitalInput());
    	tree.expandAll();
    	
    }

	private Object getInitalInput() {
		ProverType root = new ProverType();
		root.add(new FileType(fEditor.getTitle(), fEditor.getTitleImage()));
		return root;
	}

}
