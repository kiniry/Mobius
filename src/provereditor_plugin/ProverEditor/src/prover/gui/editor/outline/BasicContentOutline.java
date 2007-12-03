package prover.gui.editor.outline;




import mobius.prover.Prover;

import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.jface.viewers.StructuredSelection;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.IPropertyListener;
import org.eclipse.ui.views.contentoutline.ContentOutlinePage;

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
    	tree.setInput(getInitialInput());
    	tree.expandAll();
    	tree.addPostSelectionChangedListener(new ISelectionChangedListener() {
			public void selectionChanged(SelectionChangedEvent event) {
				ISelection sel = event.getSelection();
				if(sel instanceof StructuredSelection) {
					StructuredSelection s  = (StructuredSelection) sel;
					ProverType pt = (ProverType)s.getFirstElement();
					if(pt != null)
						pt.selectAndReveal();
				}
				
			}
    		
    	});
    	
    	fEditor.addPropertyListener(new IPropertyListener() {

			public void propertyChanged(Object source, int propId) {
				if(propId == ProverEditor.PROP_DIRTY) {
					ProverEditor pe = (ProverEditor) source;
					if(pe.isDirty())
						return;
					StructuredSelection s  = (StructuredSelection) tree.getSelection();
					ProverType pt = (ProverType)s.getFirstElement();
					String path = "";
					if(pt != null)
						path = pt.getPath();
					ProverType init = (ProverType)getInitialInput(pe); 
					tree.setInput(init);
					tree.expandAll();
					ProverType selection = init.findFromPath(path);
					if(selection != null) {
						tree.setSelection(new StructuredSelection(selection));
					}
					
				}
				
			}
    		
    	});
    }

	private Object getInitialInput() {
		return getInitialInput(fEditor);
	}
	public static Object getInitialInput(ProverEditor editor) {
		ProverType root = new ProverType(editor);
		FileType ft = new FileType(editor, editor.getTitle(), editor.getTitleImage()); 
		root.add(ft);
		ProverFileContext ctxt = new ProverFileContext(editor);
		
		Prover p = Prover.findProverFromFile(editor.getTitle());
		p.getTranslator().getFileOutline(editor, ctxt.doc, ft);
		return root;
	}

}
