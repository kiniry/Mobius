package ie.ucd.autograder.views;


import net.sourceforge.nattable.NatTable;
import net.sourceforge.nattable.config.DefaultBodyConfig;
import net.sourceforge.nattable.config.DefaultColumnHeaderConfig;
import net.sourceforge.nattable.config.SizeConfig;
import net.sourceforge.nattable.data.IDataProvider;
import net.sourceforge.nattable.model.DefaultNatTableModel;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.swt.SWT;
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.graphics.RGB;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Display;
import org.eclipse.ui.ISelectionListener;
import org.eclipse.ui.ISelectionService;
import org.eclipse.ui.IWorkbenchPart;
import org.eclipse.ui.part.ViewPart;

public class AutoGraderView extends ViewPart {

  private static final Display display = Display.getCurrent();
  public static final Color ENTRY_TITLE_COLOR = display.getSystemColor(SWT.COLOR_INFO_BACKGROUND);
  public static final Color SUB_GRADE_COLOR = display.getSystemColor(SWT.COLOR_LIST_SELECTION);
  public static final Color GRADE_COLOR = display.getSystemColor(SWT.COLOR_GREEN);
  public static final Color EMPTY_COLOR = display.getSystemColor(SWT.COLOR_WHITE);
  public static final Color MEASURE_COLOR = new Color(display, new RGB(255,240,245)); //pale lavender
  
  
  public static final Color GRADE_ERROR = display.getSystemColor(SWT.COLOR_RED);
  public static final Color GRADE_WARNING = new Color(display, new RGB(255,165,0)); //Orange
  public static final Color GRADE_OK = new Color(display, new RGB(124,252,0)); //Green

  private NatTable table;
  private DefaultBodyConfig bodyConfig;
  private DefaultNatTableModel model;

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
    AutoGraderDataProvider.getInstance().updateData();
    if (!table.isDisposed()) {
      display.asyncExec(new Runnable() {
        public void run() {
          table.updateResize();
        }
      });
    }
  }

  private void updateSelectedProject(IProject project) {
    AutoGraderDataProvider.getInstance().setSelectedProject(project);
    table.updateResize();
  }

  /**
   * This is a callback that will allow us
   * to create the viewer and initialise it.
   */
  public void createPartControl(Composite parent) {
    model = new DefaultNatTableModel();
    bodyConfig = new AutoGraderBodyConfig(AutoGraderDataProvider.getInstance());
    bodyConfig.setCellRenderer(new AutoGraderCellRenderer(AutoGraderDataProvider.getInstance()));
    model.setBodyConfig(bodyConfig);
    model.setColumnHeaderConfig(new AutoGraderColumnHeaderConfig());
    table = new NatTable(parent, SWT.H_SCROLL | SWT.V_SCROLL, model);

    //Register this view to receive selection changes.
    ISelectionService service = getSite().getWorkbenchWindow().getSelectionService();
    service.addSelectionListener("org.eclipse.jdt.ui.PackageExplorer",
        new ISelectionListener() {
      public void selectionChanged(IWorkbenchPart part, ISelection selection) {
        updateView(selection);
      }
    });
    
    
  }

  /**
   * Passing the focus request to the viewer's control.
   */
  public void setFocus() {
    table.setFocus();
  }

  private static final class AutoGraderColumnHeaderConfig extends DefaultColumnHeaderConfig {
    private final SizeConfig sizeConfig;
    public AutoGraderColumnHeaderConfig() {
      super(AutoGraderDataProvider.getInstance());
      this.sizeConfig = new SizeConfig(20);
    }
    @Override
    public int getColumnHeaderRowCount() {
      return AutoGraderDataProvider.getInstance().shouldShowColumnHeader() ? 1 : 0;
    }
    @Override
    public SizeConfig getColumnHeaderRowHeightConfig() {
      return sizeConfig;
    }    
  }
  private static final class AutoGraderBodyConfig extends DefaultBodyConfig {
    private final SizeConfig width;
    private final SizeConfig height;
    public AutoGraderBodyConfig(IDataProvider dataProvider) {
      super(dataProvider);
      this.width = new SizeConfig(150);
      this.height = new SizeConfig(20);
    }
    @Override
    public SizeConfig getColumnWidthConfig() {
      return width;
    }
    @Override
    public SizeConfig getRowHeightConfig() {
      return height;
    }
    
    
  }
}