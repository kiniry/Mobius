package ie.ucd.bon.plugin.editor.outline;

import ie.ucd.bon.API;
import ie.ucd.bon.parser.tracker.ParseResult;
import ie.ucd.bon.plugin.editor.BONEditor;

import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.swt.widgets.Composite;
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
    
    //viewer.addP
    IDocument document = editor.getDocumentProvider().getDocument(editor.getEditorInput());
    ParseResult result = API.parse(document.get());
    viewer.setInput(BONDocumentOutlineNode.elementsToTreeNodes(null, result.getParse().bonSpecification));
    viewer.expandAll();
  }

}
