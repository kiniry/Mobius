package mobius.prover.gui.editor.outline;




import mobius.prover.Prover;
import mobius.prover.gui.ProverFileContext;
import mobius.prover.gui.editor.ProverEditor;
import mobius.prover.gui.editor.outline.types.FileType;
import mobius.prover.gui.editor.outline.types.ProverType;

import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.jface.viewers.StructuredSelection;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.IPropertyListener;
import org.eclipse.ui.views.contentoutline.ContentOutlinePage;


public class BasicContentOutline extends ContentOutlinePage {
  private TreeViewer fTree;
  private ProverEditor fEditor;

  public BasicContentOutline(final ProverEditor editor) {
    fEditor = editor;
  }

  public void createControl(final Composite parent) {
    super.createControl(parent);
    fTree = this.getTreeViewer();
    fTree.setContentProvider(new TypeContentProvider());
    fTree.setLabelProvider(new TypeLabelProvider());
    fTree.setInput(getInitialInput());
    fTree.expandAll();
    fTree.addPostSelectionChangedListener(new ISelectionChangedListener() {
      public void selectionChanged(final SelectionChangedEvent event) {
        final ISelection sel = event.getSelection();
        if (sel instanceof StructuredSelection) {
          final StructuredSelection s  = (StructuredSelection) sel;
          final ProverType pt = (ProverType)s.getFirstElement();
          if (pt != null) {
            pt.selectAndReveal();
          }
        }
        
      }
      
    });
    
    fEditor.addPropertyListener(new IPropertyListener() {
      public void propertyChanged(final Object source, final int propId) {
        if (propId == ProverEditor.PROP_DIRTY) {
          final ProverEditor pe = (ProverEditor) source;
          if (pe.isDirty()) {
            return;
          }
          final StructuredSelection s  = (StructuredSelection) fTree.getSelection();
          final ProverType pt = (ProverType)s.getFirstElement();
          String path = "";
          if (pt != null) {
            path = pt.getPath();
          }
          final ProverType init = (ProverType)getInitialInput(pe); 
          fTree.setInput(init);
          fTree.expandAll();
          final ProverType selection = init.findFromPath(path);
          if (selection != null) {
            fTree.setSelection(new StructuredSelection(selection));
          }
          
        }
        
      }
      
    });
  }

  private Object getInitialInput() {
    return getInitialInput(fEditor);
  }
  public static Object getInitialInput(final ProverEditor editor) {
    final ProverType root = new ProverType(editor);
    final FileType ft = new FileType(editor, editor.getTitle(), editor.getTitleImage()); 
    root.add(ft);
    final ProverFileContext ctxt = new ProverFileContext(editor);
    
    final Prover p = Prover.findProverFromFile(editor.getTitle());
    p.getTranslator().getFileOutline(editor, ctxt.doc, ft);
    return root;
  }

}
