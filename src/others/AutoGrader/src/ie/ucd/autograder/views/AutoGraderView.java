package ie.ucd.autograder.views;

import net.sourceforge.nattable.NatTable;
import net.sourceforge.nattable.config.DefaultNatTableStyleConfiguration;
import net.sourceforge.nattable.data.IDataProvider;
import net.sourceforge.nattable.grid.layer.DefaultGridLayer;
import net.sourceforge.nattable.grid.layer.config.DefaultRowStyleConfiguration;
import net.sourceforge.nattable.painter.cell.TextPainter;
import net.sourceforge.nattable.painter.cell.decorator.PaddingDecorator;
import net.sourceforge.nattable.style.HorizontalAlignmentEnum;
import net.sourceforge.nattable.style.VerticalAlignmentEnum;
import net.sourceforge.nattable.util.GUIHelper;

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

  private static final Display display = Display.getDefault();
  public static final Color ENTRY_TITLE_COLOR = display.getSystemColor(SWT.COLOR_INFO_BACKGROUND);
  public static final Color SUB_GRADE_COLOR = display.getSystemColor(SWT.COLOR_LIST_SELECTION);
  public static final Color GRADE_COLOR = display.getSystemColor(SWT.COLOR_GREEN);
  public static final Color EMPTY_COLOR = display.getSystemColor(SWT.COLOR_WHITE);
  public static final Color MEASURE_COLOR = new Color(display, new RGB(255,240,245)); //pale lavender


  public static final Color GRADE_ERROR = display.getSystemColor(SWT.COLOR_RED);
  public static final Color GRADE_WARNING = new Color(display, new RGB(255,165,0)); //Orange
  public static final Color GRADE_OK = new Color(display, new RGB(124,252,0)); //Green

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
//        System.out.println("Updating view");
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
      display.asyncExec(new Runnable() {
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
    
    DefaultGridLayer grid = new DefaultGridLayer(bodyProvider, columnHeaderProvider, rowHeaderProvider, cornerProvider);
    table.setLayer(grid);
    
    grid.getBodyLayer().setConfigLabelAccumulator(data);
    configureTable(table);
//    AutoGraderStyleConfig.applyStylings(table.getConfigRegistry());
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
    DefaultNatTableStyleConfiguration natTableConfiguration = new DefaultNatTableStyleConfiguration();
    natTableConfiguration.bgColor = GUIHelper.COLOR_WHITE;
    natTableConfiguration.fgColor = GUIHelper.COLOR_BLACK;
    natTableConfiguration.hAlign = HorizontalAlignmentEnum.LEFT;
    natTableConfiguration.vAlign = VerticalAlignmentEnum.TOP;
    natTableConfiguration.cellPainter = new PaddingDecorator(new TextPainter(), 1);

    // Setup even odd row colors - row colors override the NatTable default colors
//    DefaultRowStyleConfiguration rowStyleConfiguration = new DefaultRowStyleConfiguration();
//    rowStyleConfiguration.oddRowBgColor = GUIHelper.getColor(254, 251, 243);
//    rowStyleConfiguration.evenRowBgColor = GUIHelper.COLOR_WHITE;

    table.addConfiguration(natTableConfiguration);
//    table.addConfiguration(rowStyleConfiguration);
    table.addConfiguration(new AutoGraderStyleConfig());
    table.configure();
  }
}