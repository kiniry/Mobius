package mobius.directvcgen.ui.poview.tree;

/**
 * An interface to trigger a show action. It makes the element showable. 
 * @author J. Charles (julien.charles@inria.fr)
 */
public interface IShowable {
  /**
   * Triggers an action to show the given node in an editor.
   */
  void show();
}
