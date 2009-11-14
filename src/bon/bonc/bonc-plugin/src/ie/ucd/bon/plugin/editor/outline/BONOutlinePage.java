package ie.ucd.bon.plugin.editor.outline;

import ie.ucd.bon.API;
import ie.ucd.bon.ast.AstNode;
import ie.ucd.bon.ast.Clazz;
import ie.ucd.bon.ast.Cluster;
import ie.ucd.bon.ast.StaticDiagram;
import ie.ucd.bon.parser.tracker.ParseResult;
import ie.ucd.bon.plugin.editor.BONEditor;

import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.jface.viewers.TreeNode;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.IPropertyListener;
import org.eclipse.ui.views.contentoutline.ContentOutlinePage;

public class BONOutlinePage extends ContentOutlinePage {

  private final BONEditor editor;

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

    ChangeListener cl = new ChangeListener();
    viewer.addPostSelectionChangedListener(cl);
    editor.addPropertyListener(cl);

    //viewer.addP
    IDocument document = editor.getDocumentProvider().getDocument(editor.getEditorInput());
    ParseResult result = API.parse(document.get());
    TreeNode[] roots = BONDocumentOutlineNode.elementsToTreeNodes(null, result.getParse().bonSpecification);
    viewer.setUseHashlookup(true);
    viewer.setInput(roots);
    viewer.collapseAll();
    setExpanded(viewer, roots);
  }

  private static boolean EXPAND_STATIC_DIAGRAMS = true;
  private static boolean EXPAND_CLUSTERS = true;
  private static boolean EXPAND_CLASSES = false;

  private static void setExpanded(TreeViewer viewer, TreeNode[] roots) {
    if (roots != null) {
      for (TreeNode node : roots) {
        BONDocumentOutlineNode bNode = (BONDocumentOutlineNode)node;
        AstNode aNode = bNode.getValue();

        if (   (EXPAND_STATIC_DIAGRAMS && aNode instanceof StaticDiagram)
            || (EXPAND_CLUSTERS && aNode instanceof Cluster)
            || (EXPAND_CLASSES && aNode instanceof Clazz)
        ) {
          viewer.setExpandedState(node, true);
          setExpanded(viewer, node.getChildren());
        }
      }
    }
  }

  private class ChangeListener implements ISelectionChangedListener, IPropertyListener {

    public void selectionChanged(SelectionChangedEvent event) {
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

    public void propertyChanged(Object source, int propId) {
      // TODO Auto-generated method stub

    }

  }

}
