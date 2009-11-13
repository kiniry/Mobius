package ie.ucd.bon.plugin.editor.outline;

import ie.ucd.bon.ast.AstNode;
import ie.ucd.bon.ast.Clazz;
import ie.ucd.bon.ast.Cluster;
import ie.ucd.bon.ast.StaticDiagram;
import ie.ucd.bon.util.Converter;
import ie.ucd.bon.util.StringUtil;

import org.eclipse.jdt.ui.ISharedImages;
import org.eclipse.jdt.ui.JavaUI;
import org.eclipse.jface.viewers.ILabelProvider;
import org.eclipse.jface.viewers.ILabelProviderListener;
import org.eclipse.swt.graphics.Image;

public class BONOutlineLabelProvider implements ILabelProvider {

  public Image getImage(Object element) {
    if (element instanceof BONDocumentOutlineNode){
      BONDocumentOutlineNode node = (BONDocumentOutlineNode)element;
      Object value = node.getValue();
      if (value instanceof StaticDiagram) {
        return null; //TODO
      } else if (value instanceof Cluster) {
        return JavaUI.getSharedImages().getImage(ISharedImages.IMG_OBJS_PACKAGE);
      } else if (value instanceof Clazz) {
        return JavaUI.getSharedImages().getImage(ISharedImages.IMG_OBJS_CLASS);
      }
    }
    return null;
  }

  public String getText(Object element) {
    if (element instanceof BONDocumentOutlineNode){
      BONDocumentOutlineNode node = (BONDocumentOutlineNode)element;
      Object value = node.getValue();
      if (value instanceof StaticDiagram) {
        return ((StaticDiagram)value).extendedId;
      } else if (value instanceof Cluster) {
        return ((Cluster)value).name;
      } else if (value instanceof Clazz) {
        Clazz clazz = ((Clazz)value);
        return clazz.name.name + (clazz.generics.size() > 0 ? "[" + StringUtil.appendWithSeparator(nodeToStringConverter.convert(clazz.generics), ",") + "]" : "");
      }
      return "NONE..." + value.getClass();
    }
    return "";
  }

  private static Converter<AstNode,String> nodeToStringConverter = new Converter<AstNode,String>() {
    public String convert(AstNode toConvert) {
      return StringUtil.prettyPrint(toConvert);
    }
  };

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
