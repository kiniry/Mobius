package mobius.prover.gui.actions;

import java.util.HashSet;
import java.util.Set;

import mobius.prover.gui.TopLevelManager;
import mobius.prover.gui.editor.ProverEditor;

import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.HandlerEvent;
import org.eclipse.core.commands.IHandler;
import org.eclipse.core.commands.IHandlerListener;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.IWorkbenchWindowActionDelegate;
import org.eclipse.ui.PlatformUI;


/**
 * Action used for the toolbar buttons provided by ProverEditor.
 */
public abstract class AProverAction implements IWorkbenchWindowActionDelegate,  IHandler{
  /** The set of all the actions of type {@link AProverAction} */
  private static Set<IAction> fSet = new HashSet<IAction>();
  /** the set of the handler listener for this handler */
  private Set<IHandlerListener> fHandlerSet = new HashSet<IHandlerListener>();
  
  /**
   * Returns the current active editor of the workbench.
   * It has the same result as {@link PlatformUI#getWorkbench()#getActiveWorkbenchWindow()#getActivePage()#getActiveEditor()}
   * @return The active editor
   */
  protected static IEditorPart getActiveEditor() {
    return PlatformUI.getWorkbench().getActiveWorkbenchWindow().getActivePage().getActiveEditor();
  }
  
  
  /*
   *  (non-Javadoc)
   * @see org.eclipse.ui.IWorkbenchWindowActionDelegate#init(org.eclipse.ui.IWorkbenchWindow)
   */
  public void init(IWorkbenchWindow window) {}
  /*
   *  (non-Javadoc)
   * @see org.eclipse.ui.IWorkbenchWindowActionDelegate#dispose()
   */
  public void dispose() {}
  
  /*
   *  (non-Javadoc)
   * @see org.eclipse.ui.IActionDelegate#selectionChanged(org.eclipse.jface.action.IAction, org.eclipse.jface.viewers.ISelection)
   */
  public void selectionChanged(IAction action, ISelection selection) {
    fSet.add(action);
    action.setEnabled(isEnabled());
  }
  
  
  /**
   * Call on all actions implementing AProverAction the method
   * {@link IAction#setEnabled(boolean)}. With the value of
   * <code>b</code> as parameter.
   * @param b Whether or not it the actions shall be enabled
   */
  public static void setAllEnabled(boolean b) {
    for (IAction a: fSet) {
      a.setEnabled(b);
    }
  }
  
  /**
   * Tell whether or not the action shall be enabled.
   * @return <code>true</code> if the action shall be enabled.
   */
  public boolean isEnabled() {
    IWorkbenchPage ap = PlatformUI.getWorkbench().getActiveWorkbenchWindow().getActivePage();
    IEditorPart ed = ap.getActiveEditor();
    if(ed instanceof ProverEditor) {
      return TopLevelManager.getInstance() != null;
    }
    return false;
  }
  
  
  /*
   * (non-Javadoc)
   * @see org.eclipse.core.commands.IHandler#addHandlerListener(org.eclipse.core.commands.IHandlerListener)
   */
  public void addHandlerListener(IHandlerListener handlerListener) { 
    fHandlerSet.add(handlerListener);
  }
  /*
   * (non-Javadoc)
   * @see org.eclipse.core.commands.IHandler#removeHandlerListener(org.eclipse.core.commands.IHandlerListener)
   */
  public void removeHandlerListener(IHandlerListener handlerListener) { 
    fHandlerSet.remove(handlerListener);
  }

  /**
   * Fire the property change to all the listener.
   * @param event the event to advertise
   */
  protected void fireChangeToHandlers(HandlerEvent event) {
    for (IHandlerListener hl: fHandlerSet) {
      hl.handlerChanged(event);
    }
  }
  
  /*
   * (non-Javadoc)
   * @see org.eclipse.core.commands.IHandler#isHandled()
   */
  public boolean isHandled() {
    return true;
  }
  
  
  /*
   * (non-Javadoc)
   * @see org.eclipse.ui.IActionDelegate#run(org.eclipse.jface.action.IAction)
   */
  public void run(IAction action) {
    trigger();
  }
  
  
  /*
   * (non-Javadoc)
   * @see org.eclipse.core.commands.IHandler#execute(org.eclipse.core.commands.ExecutionEvent)
   */
  public Object execute(ExecutionEvent event) throws ExecutionException {
    trigger();
    return null;
  }
  
  /**
   * Trigger a prover action. The action is dependent
   * of the child implementations.
   */
  public abstract void trigger();
}
