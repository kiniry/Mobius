package prover.gui.editor.outline;


import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.jface.viewers.StructuredSelection;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.views.contentoutline.ContentOutlinePage;

import prover.Prover;
import prover.gui.ProverFileContext;
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
    	tree.addPostSelectionChangedListener(new ISelectionChangedListener() {

			public void selectionChanged(SelectionChangedEvent event) {
				ISelection sel = event.getSelection();
				if(sel instanceof StructuredSelection) {
					StructuredSelection s  = (StructuredSelection) sel;
					ProverType pt = (ProverType)s.getFirstElement();
					pt.selectAndReveal();
				}
				
			}
    		
    	});
    	
    }

	private Object getInitalInput() {
		ProverType root = new ProverType(fEditor);
		FileType ft = new FileType(fEditor, fEditor.getTitle(), fEditor.getTitleImage()); 
		root.add(ft);
		ProverFileContext ctxt = new ProverFileContext(fEditor);
		
		Prover p = Prover.findProverFromFile(fEditor.getTitle());
		p.getTranslator().getFileOutline(fEditor, ctxt.doc, ft);
		return root;
	}

}
