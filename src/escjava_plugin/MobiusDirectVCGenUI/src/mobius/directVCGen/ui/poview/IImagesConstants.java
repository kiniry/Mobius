package mobius.directVCGen.ui.poview;


/**
 * The constants used to handle the images for the tree nodes.
 * 
 * @author J. Charles (julien.charles@inria.fr)
 */
public interface IImagesConstants {
  /** the default image. */
  int IMG_DEFAULT = 0;
  /** the image for an unknown file. */
  int IMG_UNKNOWN = 0;  
  
  /** the eclipse symbol for methods. */
  int IMG_METHOD = IMG_DEFAULT + 1;
  
  /** the eclipse symbol for classes. */
  int IMG_CLASS = IMG_METHOD + 1;
  
  /** a project (an open folder). */
  int IMG_PROJECT = IMG_CLASS + 1;
  
  /** an empty project (a closed folder). */
  int IMG_PROJECT_EMPTY = IMG_PROJECT + 1;
  

  int IMG_GOAL = IMG_PROJECT_EMPTY + 1;
  int IMG_GOAL_SOLVED = IMG_GOAL + 1;
  
  int IMG_LIB = IMG_GOAL_SOLVED + 1;
  
  int IMG_LIB_RED = IMG_LIB + 1;  
  
  int IMG_OBJS_LIBRARY = IMG_LIB_RED + 1;
  
  int IMG_FOLDER = IMG_OBJS_LIBRARY + 1;
  int IMG_SRC_FOLDER = IMG_FOLDER + 1;
  int IMG_PKG = IMG_SRC_FOLDER + 1;
  int IMG_MKFILE = IMG_PKG + 1;
  

  
}
