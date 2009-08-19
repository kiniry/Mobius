package ie.ucd.autograder.views;

import net.sourceforge.nattable.NatTable;
import net.sourceforge.nattable.data.IDataProvider;
import net.sourceforge.nattable.grid.layer.DefaultColumnHeaderDataLayer;
import net.sourceforge.nattable.grid.layer.DefaultGridLayer;
import net.sourceforge.nattable.grid.layer.DefaultRowHeaderDataLayer;
import net.sourceforge.nattable.layer.DataLayer;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Display;
import org.eclipse.ui.ISelectionListener;
import org.eclipse.ui.ISelectionService;
import org.eclipse.ui.IWorkbenchPart;
import org.eclipse.ui.part.ViewPart;

public class AutoGraderView extends ViewPart {

  private NatTable table;

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
      //System.out.println("Not IJavaElement or IResource " + actual.getClass());
    }
  }

  public void update() {
    AutoGraderDataProvider.getInstance().updateData();
    if (!table.isDisposed()) {
      Display.getDefault().asyncExec(new Runnable() {
        public void run() {
          table.updateResize();
        }
      });
    }
  }

  private void updateSelectedProject(IProject project) {
    AutoGraderDataProvider.getInstance().setSelectedProject(project);
    updateTable();
    table.updateResize();
  }

  private void updateTable() {
    AutoGraderDataProvider data = AutoGraderDataProvider.getInstance();
    IDataProvider bodyProvider = new AutoGraderBodyDataProvider(data);
    IDataProvider columnHeaderProvider = new AutoGraderColumnHeaderDataProvider(data);
    IDataProvider rowHeaderProvider = new EmptyDataProvider();
    IDataProvider cornerProvider = new EmptyDataProvider();

    DataLayer bodyLayer = new DataLayer(bodyProvider);
    DataLayer columnHeaderLayer = new DefaultColumnHeaderDataLayer(columnHeaderProvider);
    DataLayer rowHeaderLayer = new DefaultRowHeaderDataLayer(rowHeaderProvider);
    DataLayer cornerLayer = new DataLayer(cornerProvider);
    
    bodyLayer.setDefaultColumnWidth(150);
    
    DefaultGridLayer grid = new DefaultGridLayer(bodyLayer, columnHeaderLayer, rowHeaderLayer, cornerLayer, false);
    table.setLayer(grid);

    grid.getBodyLayer().setConfigLabelAccumulator(data);
    
    configureTable(table);
    //AutoGraderStyleConfig.applyStylings(table.getConfigRegistry());
  }

  /**
   * This is a callback that will allow us
   * to create the viewer and initialise it.
   */
  public void createPartControl(Composite parent) {
    table = new NatTable(parent, false);
    updateTable();

    //Register this view to receive selection changes.
    ISelectionService service = getSite().getWorkbenchWindow().getSelectionService();
    service.addSelectionListener("org.eclipse.jdt.ui.PackageExplorer",
        new ISelectionListener() {
      public void selectionChanged(IWorkbenchPart part, ISelection selection) {
        updateView(selection);
      }
    });
    //    System.out.println("Registered selection listener");
  }

  /**
   * Passing the focus request to the viewer's control.
   */
  public void setFocus() {
    table.setFocus();
  }

  private void configureTable(NatTable table) {
    table.addConfiguration(new AutoGraderStyleConfig());
    table.configure();
  }
}