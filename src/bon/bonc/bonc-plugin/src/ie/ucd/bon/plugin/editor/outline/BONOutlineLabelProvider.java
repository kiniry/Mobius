package ie.ucd.bon.plugin.editor.outline;

import ie.ucd.bon.ast.Clazz;
import ie.ucd.bon.ast.Cluster;
import ie.ucd.bon.ast.StaticDiagram;

import org.eclipse.jface.viewers.ILabelProvider;
import org.eclipse.jface.viewers.ILabelProviderListener;
import org.eclipse.swt.graphics.Image;

public class BONOutlineLabelProvider implements ILabelProvider {

  public Image getImage(Object element) {
    return null;
  }

  public String getText(Object element) {
    System.out.println("Getting text");
    if (element instanceof StaticDiagram) {
      return ((StaticDiagram)element).extendedId;
    } else if (element instanceof Cluster) {
      return ((Cluster)element).name;
    } else if (element instanceof Clazz) {
      return ((Clazz)element).name.name;
    } 
    return "NONE...";    
  }

  public void dispose() {
    // TODO Auto-generated method stub
  }

  public boolean isLabelProperty(Object element, String property) {
    // TODO Auto-generated method stub
    return false;
  }

  public void addListener(ILabelProviderListener listener) {
    // TODO Auto-generated method stub 
  }
  
  public void removeListener(ILabelProviderListener listener) {
    // TODO Auto-generated method stub
  }

  

}
