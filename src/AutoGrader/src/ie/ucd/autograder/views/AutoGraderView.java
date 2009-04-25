package ie.ucd.autograder.views;


import ie.ucd.autograder.builder.DataStore;
import ie.ucd.autograder.grading.AggregateData;
import ie.ucd.autograder.grading.InputData;
import ie.ucd.autograder.util.Pair;
import ie.ucd.autograder.util.Pair.NameProjectDataPair;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredContentProvider;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.ITableLabelProvider;
import org.eclipse.jface.viewers.LabelProvider;
import org.eclipse.jface.viewers.TableViewer;
import org.eclipse.jface.viewers.Viewer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Table;
import org.eclipse.swt.widgets.TableColumn;
import org.eclipse.swt.widgets.TableItem;
import org.eclipse.ui.ISelectionListener;
import org.eclipse.ui.ISelectionService;
import org.eclipse.ui.ISharedImages;
import org.eclipse.ui.IWorkbenchPart;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.part.ViewPart;


public class AutoGraderView extends ViewPart {
  private TableViewer viewer;

  /**
   * The constructor.
   */
  public AutoGraderView() {
  }

  private void updateView(ISelection selection) {
    //System.out.println("Updating view");
    Object actual = selection;
    //Get the first element if more than one are selected.
    if (selection instanceof IStructuredSelection) {
      actual = ((IStructuredSelection)selection).getFirstElement();
    }

    if (actual instanceof IJavaElement) {
      IJavaProject javaProject = ((IJavaElement)actual).getJavaProject();
      updateSelectedProject(javaProject.getProject());
    } else if (actual instanceof IResource) {
      IProject project = ((IResource)actual).getProject();
      updateSelectedProject(project);
    } else {
      //System.out.println("Not IJavaElement or IResource");
    }
  }

  private void updateSelectedProject(IProject project) {
    List<AggregateData> projectData = DataStore.getInstance(project).getDataForProject(project);
    if (projectData == null) {
      displayNoProjectData(project.getName());
    } else {
      displayData(project.getName(), projectData);
    }
  }

  private void displayNoProjectData(String name) {
    viewer.setInput("No data for project " + name);
  }

  private void displayData(String projectName, List<AggregateData> projectData) {
    // TODO display items.
    viewer.setInput(projectData);
  }

  /**
   * This is a callback that will allow us
   * to create the viewer and initialise it.
   */
  public void createPartControl(Composite parent) {
    viewer = new TableViewer(parent, SWT.MULTI | SWT.H_SCROLL | SWT.V_SCROLL);
    viewer.setContentProvider(new ViewContentProvider());
    viewer.setLabelProvider(new ViewLabelProvider());

    //Register this view to receive selection changes.
    ISelectionService service = getSite().getWorkbenchWindow().getSelectionService();
    service.addSelectionListener(new ISelectionListener() {
      public void selectionChanged(IWorkbenchPart part, ISelection selection) {
        updateView(selection);
      }
    });

    // Create the help context id for the viewer's control
    PlatformUI.getWorkbench().getHelpSystem().setHelp(viewer.getControl(), "AutoGrader.viewer");
    viewer.getTable().setHeaderVisible(true);
  }

  /**
   * @param columnName
   * @param table 
   */
  protected TableColumn createColumn(String columnName, Table table, int index) {
    TableColumn column = new TableColumn(table, SWT.NULL, index);	       
    column.setText(columnName);
    column.pack();
    return column;
  }
  
  private void createColumns(List<AggregateData> datas) {
    int index = 0;
    for (AggregateData data : datas) {
      createColumn(data.getName(), viewer.getTable(), index++);
    }
  }
  
  private void packColumns() {
    for (TableColumn column : viewer.getTable().getColumns()) {
      column.pack();
    }
  }

  /**
   * Passing the focus request to the viewer's control.
   */
  public void setFocus() {
    viewer.getControl().setFocus();
  }
  
  private void clearTable() {
    viewer.getTable().removeAll();
    for (TableColumn column : viewer.getTable().getColumns()) {
      column.dispose();
    }
//    List<AggregateData> projectData = pair.getSecond();
//    for (int i=0; i < projectData.size(); i++) {
//      
//    }
  }

  class ViewContentProvider implements IStructuredContentProvider {

    private Object content;
    private final List<TableItem> items;
    public ViewContentProvider() {
      items = new ArrayList<TableItem>(10);
    }

    public void inputChanged(Viewer v, Object oldInput, Object newInput) {
      this.content = newInput;
      if (oldInput == newInput) {
        //Do nothing
        System.out.println("No change to inputs");
      } else {
        clearTable();
        if (newInput instanceof String) { 
          //TODO display String somewhere...
        } else if (newInput instanceof List) {
          createColumns((List<AggregateData>)newInput);
          updateItems((List<AggregateData>)newInput);
          packColumns();
        }
      }
    }
    public void updateItems(List<AggregateData> actualData) {
      items.clear();
      Table table = viewer.getTable();
      
      int numItems = 0;
      for (AggregateData data : actualData) {
        if (data.getData().size() > numItems) {
          numItems = data.getData().size(); 
        }
      }
      
      for (int itemIndex=0; itemIndex < numItems; itemIndex++) {
        TableItem item = new TableItem(table, SWT.NULL);
        TableItem item2 = new TableItem(table, SWT.NULL);
        TableItem item3 = new TableItem(table, SWT.NULL);
        for (int columnIndex=0; columnIndex < actualData.size(); columnIndex++) {
          AggregateData agData = actualData.get(columnIndex);
          List<Pair<InputData,Double>> agDataData = agData.getData();
          if (agDataData.size() > itemIndex) {
            item.setText(columnIndex, agDataData.get(itemIndex).getFirst().getName() + ":");
            item2.setText(columnIndex, agDataData.get(itemIndex).getFirst().getMeasureAsString());
            item3.setText(columnIndex, "Grade: " + agDataData.get(itemIndex).getFirst().getGrade());
          } else {
            item.setText(columnIndex, "");
            item2.setText(columnIndex, "");
            item3.setText(columnIndex, "");
          }            
        }
        items.add(item);
      }
      
      TableItem summaries = new TableItem(table, SWT.NULL);
      int index = 0;
      for (AggregateData data : actualData) {
        summaries.setText(index++, data.getName() + " Grade: " + data.getGrade());
      }
    }
    
    public void dispose() {
      content = null;
    }
    public Object[] getElements(Object parent) {
      
      if (content instanceof List) {
        return items.toArray();
      } else {
        if (content instanceof String) {
          return new String[] { (String)content };
        } else {
          return new String[] { "No data for the selected project."};
        }
      }
    }
  }

  class ViewLabelProvider extends LabelProvider implements ITableLabelProvider {
    public String getColumnText(Object obj, int index) {
      return getText(obj);
    }
    public Image getColumnImage(Object obj, int index) {
      return getImage(obj);
    }
    public Image getImage(Object obj) {
      return PlatformUI.getWorkbench().getSharedImages().getImage(ISharedImages.IMG_OBJ_ELEMENT);
    }
  }
}