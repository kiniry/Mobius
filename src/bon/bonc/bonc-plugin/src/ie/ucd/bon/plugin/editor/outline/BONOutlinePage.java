package ie.ucd.bon.plugin.editor.outline;

import ie.ucd.bon.API;
import ie.ucd.bon.parser.tracker.ParseResult;

import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.views.contentoutline.ContentOutlinePage;
import org.eclipse.ui.views.contentoutline.IContentOutlinePage;

public class BONOutlinePage extends ContentOutlinePage implements IContentOutlinePage {

  private final IDocument input;
  
  public BONOutlinePage(IDocument input) {
    this.input = input;
  }
  
  @Override
  public void createControl(Composite parent) {
    super.createControl(parent);
    TreeViewer viewer = getTreeViewer();
    viewer.setContentProvider(new BONOutlineContentProvider());
    viewer.setLabelProvider(new BONOutlineLabelProvider());
    viewer.addSelectionChangedListener(this);
    
    ParseResult result = API.parse(input.get());
    viewer.setInput(new BONDocumentOutlineNode(result.getParse()));
  }

}
