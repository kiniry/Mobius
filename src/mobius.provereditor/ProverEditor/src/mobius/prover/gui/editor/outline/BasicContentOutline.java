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

/**
 * The implementation of the content outline. 
 * @author J. Charles (julien.charles@inria.fr)
 */
public class BasicContentOutline extends ContentOutlinePage {
  /** the tree that is associated with the content. */
  private TreeViewer fTree;
  /** the current parent editor instance. */
  private ProverEditor fEditor;

  /**
   * Initialize it, and associate it to an editor.
   * @param editor the editor to associate the outline to
   */
  public BasicContentOutline(final ProverEditor editor) {
    fEditor = editor;
  }

  /** {@inheritDoc} */
  @Override
  public void createControl(final Composite parent) {
    super.createControl(parent);
    fTree = this.getTreeViewer();
    
    fTree.setContentProvider(new TypeContentProvider());
    fTree.setLabelProvider(new TypeLabelProvider());
    fTree.setInput(getInitialInput());
    fTree.expandAll();
    final ContentListener cl = new ContentListener(fTree);
    fEditor.addPropertyListener(cl);
  }

  /**
   * Returns the initial input associated with the current
   *  editor.
   * @return a node, corresponding to the initial input.
   */
  private ProverType getInitialInput() {
    return getInitialInput(fEditor);
  }
  
  /**
   * Returns the initial input associated with a specific editor.
   * @param editor the editor to get the initial input for
   * @return a root node, the initial input
   */
  public static ProverType getInitialInput(final ProverEditor editor) {
    final ProverType root = new ProverType(editor);
    final FileType ft = new FileType(editor, editor.getTitle(), editor.getTitleImage()); 
    root.add(ft);
    final ProverFileContext ctxt = new ProverFileContext(editor);
    final Prover p = Prover.findProverFromFile(editor.getTitle());
    p.getTranslator().getFileOutline(editor, ctxt.getDocument(), ft);
    return root;
  }
  
  /**
   * A listener used to listen to the tree changes and the changes made in
   * the editor to update the outline.
   * @author J. Charles (julien.charles@inria.fr)
   */
  private static class ContentListener implements IPropertyListener, 
                                                  ISelectionChangedListener {
    /** the current tree which is being listened. */
    private final TreeViewer fTree;
    
    /**
     * Initialize the constent listener from a tree, and listens
     * to it.
     * @param tree should be a valid treeviewer
     */
    public ContentListener(final TreeViewer tree) {
      fTree = tree;
      fTree.addPostSelectionChangedListener(this);
    }

    /** {@inheritDoc} */
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
    
    /** {@inheritDoc} */
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
  }
}
