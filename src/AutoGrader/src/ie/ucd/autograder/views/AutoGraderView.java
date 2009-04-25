package ie.ucd.autograder.views;


import ie.ucd.autograder.builder.DataStore;
import ie.ucd.autograder.builder.GraderBuilder;
import ie.ucd.autograder.grading.AggregateData;
import ie.ucd.autograder.grading.Grade;
import ie.ucd.autograder.grading.InputData;
import ie.ucd.autograder.util.Pair;

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
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.graphics.RGB;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Display;
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

  private static final Display display = Display.getCurrent();
  public static final Color ENTRY_TITLE_COLOR = display.getSystemColor(SWT.COLOR_INFO_BACKGROUND);
  public static final Color SUB_GRADE_COLOR = display.getSystemColor(SWT.COLOR_LIST_SELECTION);
  public static final Color GRADE_COLOR = display.getSystemColor(SWT.COLOR_GREEN);
  public static final Color EMPTY_COLOR = display.getSystemColor(SWT.COLOR_WHITE);
  public static final Color TOTAL_GRADE_COLOR = display.getSystemColor(SWT.COLOR_WHITE);

  public static final Color GRADE_ERROR = display.getSystemColor(SWT.COLOR_RED);
  public static final Color GRADE_WARNING = new Color(display, new RGB(255,165,0)); //Orange
  public static final Color GRADE_OK = new Color(display, new RGB(124,252,0)); //Green

  private TableViewer viewer;
  private IProject selectedProject;


  /**
   * The constructor.
   */
  public AutoGraderView() {
    instance = this;
  }

  private static AutoGraderView instance;
  public static AutoGraderView getInstance() {
    return instance;
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
      //      System.out.println("Not IJavaElement or IResource " + actual.getClass());

    }
  }

  public void update() {
    if (selectedProject != null) {
      System.out.println("Updating for " + selectedProject);
      updateSelectedProject(selectedProject);
    }
  }

  private void updateSelectedProject(IProject project) {
    selectedProject = project;
    List<AggregateData> projectData = DataStore.getInstance(project, true).getDataForProject(project);
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
    service.addSelectionListener("org.eclipse.jdt.ui.PackageExplorer",
        new ISelectionListener() {
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
  }

  class ViewContentProvider implements IStructuredContentProvider {

    private Object content;
    private final List<TableItem> items;
    public ViewContentProvider() {
      items = new ArrayList<TableItem>(10);
    }

    @SuppressWarnings("unchecked")
    public void inputChanged(Viewer v, Object oldInput, Object newInput) {
      this.content = newInput;
      if (oldInput == newInput) {
        //Do nothing
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

      int numRows = 0;
      for (AggregateData data : actualData) {
        int size = data.getData().size();
        size *= data.getName().equals(GraderBuilder.TOTAL_NAME) ? 2 : 3; 
        if (size > numRows) {
          numRows = size; 
        }
      }
      int numItems = (int)Math.ceil(numRows/3d);

      for (int itemIndex=0; itemIndex < numItems; itemIndex++) {
        TableItem item = new TableItem(table, SWT.NULL);
        TableItem item2 = new TableItem(table, SWT.NULL);
        TableItem item3 = new TableItem(table, SWT.NULL);
        for (int columnIndex=0; columnIndex < actualData.size(); columnIndex++) {
          AggregateData agData = actualData.get(columnIndex);
          List<Pair<InputData,Double>> agDataData = agData.getData();

          if (agDataData.size() > itemIndex && !agData.getName().equals(GraderBuilder.TOTAL_NAME)) {
            item.setText(columnIndex, agDataData.get(itemIndex).getFirst().getName() + ":");
            item.setBackground(columnIndex, ENTRY_TITLE_COLOR);
            item2.setText(columnIndex, agDataData.get(itemIndex).getFirst().getMeasureAsString());
            item3.setText(columnIndex, "Grade: " + agDataData.get(itemIndex).getFirst().getGrade());
            item3.setBackground(columnIndex, SUB_GRADE_COLOR);
          } else {
            item.setText(columnIndex, "");
            item.setBackground(columnIndex, EMPTY_COLOR);
            item2.setText(columnIndex, "");
            item2.setBackground(columnIndex, EMPTY_COLOR);
            item3.setText(columnIndex, "");
            item3.setBackground(columnIndex, EMPTY_COLOR);
          }       

        }
        items.add(item);
        items.add(item2);
        items.add(item3);
      }

      int lastIndex = actualData.size()-1;
      if (actualData.get(lastIndex).getName().equals(GraderBuilder.TOTAL_NAME)) {
        //Redo final column
        AggregateData totals = actualData.get(actualData.size()-1);
        for (int i=0; i < totals.getData().size(); i++) {
          items.get(i*2).setText(lastIndex, totals.getData().get(i).getFirst().getName() + ":");
          items.get(i*2).setBackground(lastIndex, ENTRY_TITLE_COLOR);
          Grade grade = totals.getData().get(i).getFirst().getGrade();
          items.get((i*2)+1).setText(lastIndex, "Grade: " + grade);
          items.get((i*2)+1).setBackground(lastIndex, gradeToColour(grade));
        }

        //Remove blank items
        for (int i=(totals.getData().size()*2); i < items.size(); i++) {
          TableItem item = items.get(i);
          boolean empty = true;
          for (int j=0; j < actualData.size(); j++) {
            if (!item.getText(j).equals("")) {
              empty = false;
            }
          }
          if (empty) {
            table.remove(i);
            items.remove(i);
            i--;
          }
        }
      }


      TableItem summaries = new TableItem(table, SWT.NULL);
      int index = 0;
      for (AggregateData data : actualData) {
        summaries.setText(index, data.getName() + " Grade: " + data.getGrade());
        summaries.setBackground(index, gradeToColour(data.getGrade()));
        index++;
      }
      items.add(summaries);
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

  public static Color gradeToColour(Grade grade) {
    switch (grade) {
    case A_PLUS: 
    case A:
    case A_MINUS:
    case B_PLUS:
    case B:
      return GRADE_OK;
    case B_MINUS:
    case C_PLUS:
    case C:
    case C_MINUS:
      return GRADE_WARNING;
    case D_PLUS:
    case D:
    case D_MINUS:
    case E_PLUS:
    case E:
    case E_MINUS:
    case F_PLUS:
    case F:
    case F_MINUS:
    case G:
    case NG:
    case NA:
    default:
      return GRADE_ERROR;
    }
  }
}