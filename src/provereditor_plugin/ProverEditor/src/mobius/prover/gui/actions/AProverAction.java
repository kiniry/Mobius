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
 *
 * @author J. Charles (julien.charles@inria.fr)
 */
public abstract class AProverAction implements IWorkbenchWindowActionDelegate,  IHandler {
  /** The set of all the actions of type {@link AProverAction}. */
  private static Set<IAction> fSet = new HashSet<IAction>();
  /** the set of the handler listener for this handler. */
  private Set<IHandlerListener> fHandlerSet = new HashSet<IHandlerListener>();
  
  /**
   * Returns the current active editor of the workbench.
   * It has the same result as {@link 
   * PlatformUI#getWorkbench()#getActiveWorkbenchWindow()#getActivePage()#getActiveEditor()}
   * @return The active editor
   */
  protected static IEditorPart getActiveEditor() {
    return PlatformUI.getWorkbench().getActiveWorkbenchWindow().getActivePage().getActiveEditor();
  }
  
  /** {@inheritDoc} */
  @Override
  public void init(final IWorkbenchWindow window) {
    
  }
  
  /** {@inheritDoc} */
  @Override
  public void dispose() {
    
  }
  

  /** {@inheritDoc} */
  @Override
  public void selectionChanged(final IAction action, 
                               final ISelection selection) {
    fSet.add(action);
    action.setEnabled(isEnabled());
  }
  
  
  /**
   * Call on all actions implementing AProverAction the method
   * {@link IAction#setEnabled(boolean)}. With the value of
   * <code>b</code> as parameter.
   * @param b Whether or not it the actions shall be enabled
   */
  public static void setAllEnabled(final boolean b) {
    for (IAction a: fSet) {
      a.setEnabled(b);
    }
  }
  
  /**
   * Tell whether or not the action shall be enabled.
   * @return <code>true</code> if the action shall be enabled.
   */
  public boolean isEnabled() {
    final IWorkbenchPage ap = PlatformUI.getWorkbench().getActiveWorkbenchWindow().getActivePage();
    final IEditorPart ed = ap.getActiveEditor();
    if (ed instanceof ProverEditor) {
      return TopLevelManager.getInstance() != null;
    }
    return false;
  }
  
  /** {@inheritDoc} */
  @Override
  public void addHandlerListener(final IHandlerListener handlerListener) { 
    fHandlerSet.add(handlerListener);
  }
  
  /** {@inheritDoc} */
  @Override
  public void removeHandlerListener(final IHandlerListener handlerListener) { 
    fHandlerSet.remove(handlerListener);
  }

  /**
   * Fire the property change to all the listener.
   * @param event the event to advertise
   */
  protected void fireChangeToHandlers(final HandlerEvent event) {
    for (IHandlerListener hl: fHandlerSet) {
      hl.handlerChanged(event);
    }
  }
  
  /** {@inheritDoc} */
  @Override
  public boolean isHandled() {
    return true;
  }
  
  
  /** {@inheritDoc} */
  @Override
  public void run(final IAction action) {
    trigger();
  }
  
  
  /** {@inheritDoc} */
  @Override
  public Object execute(final ExecutionEvent event) throws ExecutionException {
    trigger();
    return null;
  }
  
  /**
   * Trigger a prover action. The action is dependent
   * of the child implementations.
   */
  public abstract void trigger();
}
