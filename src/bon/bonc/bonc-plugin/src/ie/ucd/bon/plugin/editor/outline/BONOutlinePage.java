package ie.ucd.bon.plugin.editor.outline;

import ie.ucd.bon.API;
import ie.ucd.bon.ast.AstNode;
import ie.ucd.bon.ast.Clazz;
import ie.ucd.bon.ast.Cluster;
import ie.ucd.bon.ast.StaticDiagram;
import ie.ucd.bon.parser.tracker.ParseResult;
import ie.ucd.bon.plugin.editor.BONEditor;
import ie.ucd.bon.source.SourceLocation;

import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.TextViewer;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.jface.viewers.StructuredSelection;
import org.eclipse.jface.viewers.TreeNode;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IPropertyListener;
import org.eclipse.ui.views.contentoutline.ContentOutlinePage;

public class BONOutlinePage extends ContentOutlinePage {

  private final BONEditor editor;
  private ChangeListener cl;
  private TreeNode[] roots;

  public BONOutlinePage(BONEditor editor) {
    this.editor = editor;
  }

  @Override
  public void createControl(Composite parent) {
    super.createControl(parent);
    TreeViewer viewer = getTreeViewer();
    viewer.setContentProvider(new BONOutlineContentProvider());
    viewer.setLabelProvider(new BONOutlineLabelProvider());
    viewer.addSelectionChangedListener(this);
    viewer.setUseHashlookup(true);
    
    cl = new ChangeListener();
    viewer.addPostSelectionChangedListener(cl);
    editor.addPropertyListener(cl);
    editor.addPostSelectionChangedListener(cl);
    
    updateOutline();
    viewer.collapseAll();
    setInitialExpanded(viewer, roots);
    cl.changeIgnores = 0;
    cl.updateTreeSelectionUsingEditorPosition(false);
  }
  
  public void updateOutline() {
    IDocument document = editor.getDocumentProvider().getDocument(editor.getEditorInput());
    ParseResult result = API.parse(document.get());
    if (result.isValidParse()) {
      roots = BONDocumentOutlineNode.elementsToTreeNodes(null, result.getParse().bonSpecification);
      getTreeViewer().setInput(roots);
      cl.updateTreeSelectionUsingEditorPosition(true);
    }
  }

  @Override
  public void dispose() {
    editor.removePropertyListener(cl);
    editor.removePostSelectionChangedListener(cl);
    super.dispose();
  }

  private static boolean EXPAND_STATIC_DIAGRAMS = true;
  private static boolean EXPAND_CLUSTERS = true;
  private static boolean EXPAND_CLASSES = false;

  private static void setInitialExpanded(TreeViewer viewer, TreeNode[] roots) {
    if (roots != null) {
      for (TreeNode node : roots) {
        BONDocumentOutlineNode bNode = (BONDocumentOutlineNode)node;
        AstNode aNode = bNode.getValue();

        if (   (EXPAND_STATIC_DIAGRAMS && aNode instanceof StaticDiagram)
            || (EXPAND_CLUSTERS && aNode instanceof Cluster)
            || (EXPAND_CLASSES && aNode instanceof Clazz)
        ) {
          viewer.setExpandedState(node, true);
          setInitialExpanded(viewer, node.getChildren());
        }
      }
    }
  }

  private class ChangeListener implements ISelectionChangedListener, IPropertyListener {

    
    private int changeIgnores = 0; //Used to avoid event triggering loop
    
    public void selectionChanged(SelectionChangedEvent event) {
      if (event.getSource() instanceof TextViewer) {
        updateTreeSelectionUsingEditorPosition(false);
      } else if (event.getSource() == getTreeViewer()) {
        if (changeIgnores > 0) {
          changeIgnores--;
          return;
        }
        ISelection selection = event.getSelection();
        if (selection instanceof IStructuredSelection) {
          IStructuredSelection ss = (IStructuredSelection)selection;
          Object o = ss.getFirstElement();
          if (o instanceof BONDocumentOutlineNode) {
            AstNode node = ((BONDocumentOutlineNode)o).getValue();
            editor.selectAndReveal(node);
          }
        }
      }
    }

    public void propertyChanged(Object source, int propId) {
      if (propId == IEditorPart.PROP_DIRTY) {
        BONEditor editor = (BONEditor)source;
        if (!editor.isDirty()) {
          updateOutline();
        }
      }
    }

    private void updateTreeSelectionUsingEditorPosition(boolean afterOutlineUpdate) {
      updateTreeSelectionUsingPosition(editor.getCaretPosition(), afterOutlineUpdate);
    }
    
    private void updateTreeSelectionUsingPosition(int position, boolean afterOutlineUpdate) {
      TreeNode found = find(roots, position);
      if (found != null) {
        StructuredSelection selection = new StructuredSelection(found);
        changeIgnores++;
        if (afterOutlineUpdate) {
          changeIgnores++;
        }
        if (found.getParent() != null) {
          getTreeViewer().setExpandedState(found.getParent(), true);
        }
        getTreeViewer().setSelection(selection);
      }
    }

    private TreeNode find(final TreeNode[] nodes, final int offset) {
      if (nodes == null) {
        return null;
      }
      for (TreeNode node : nodes) {
        BONDocumentOutlineNode bNode = (BONDocumentOutlineNode)node;
        AstNode aNode = bNode.getValue();
        SourceLocation loc = aNode.getLocation();
        //TODO adjust from eclipse char position?
        if (loc.getAbsoluteCharPositionStart() <= offset && loc.getAbsoluteCharPositionEnd() >= offset) {
          TreeNode[] children = node.getChildren();
          //See if a child node is more exact
          TreeNode found = find(children, offset);
          if (found != null) {
            return found;
          } else {
            return node;
          }
        }
      }
      return null; //Not found
    }

  }

}
