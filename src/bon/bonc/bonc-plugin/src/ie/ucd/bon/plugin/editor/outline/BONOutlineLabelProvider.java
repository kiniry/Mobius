package ie.ucd.bon.plugin.editor.outline;

import ie.ucd.bon.ast.AstNode;
import ie.ucd.bon.ast.ClassChart;
import ie.ucd.bon.ast.Clazz;
import ie.ucd.bon.ast.ClientRelation;
import ie.ucd.bon.ast.Cluster;
import ie.ucd.bon.ast.ClusterChart;
import ie.ucd.bon.ast.FeatureArgument;
import ie.ucd.bon.ast.FeatureSpecification;
import ie.ucd.bon.ast.StaticDiagram;
import ie.ucd.bon.ast.Type;
import ie.ucd.bon.util.AstUtil;
import ie.ucd.bon.util.StringUtil;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.jdt.ui.ISharedImages;
import org.eclipse.jdt.ui.JavaUI;
import org.eclipse.jface.viewers.ILabelProvider;
import org.eclipse.jface.viewers.ILabelProviderListener;
import org.eclipse.swt.graphics.Image;

public class BONOutlineLabelProvider implements ILabelProvider {

  public Image getImage(Object element) {
    if (element instanceof BONDocumentOutlineNode){
      BONDocumentOutlineNode node = (BONDocumentOutlineNode)element;
      AstNode value = node.getValue();
      if (value instanceof StaticDiagram) {
        return JavaUI.getSharedImages().getImage(ISharedImages.IMG_OBJS_PACKFRAG_ROOT);
      } else if (value instanceof Cluster) {
        return JavaUI.getSharedImages().getImage(ISharedImages.IMG_OBJS_PACKAGE);
      } else if (value instanceof Clazz) {
        return JavaUI.getSharedImages().getImage(ISharedImages.IMG_OBJS_CLASS);
      } else if (value instanceof FeatureSpecification) {
        return JavaUI.getSharedImages().getImage(ISharedImages.IMG_FIELD_PUBLIC);
      } else if (value instanceof ClusterChart) {
        return JavaUI.getSharedImages().getImage(ISharedImages.IMG_OBJS_PACKAGE);
      } else if (value instanceof ClassChart) {
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
        StaticDiagram sd = (StaticDiagram)value;
        return sd.extendedId == null ? "static_diagram" : sd.extendedId;
      } else if (value instanceof Cluster) {
        return ((Cluster)value).name;
      } else if (value instanceof Clazz) {
        Clazz clazz = ((Clazz)value);
        return clazz.name.name + (clazz.generics.size() > 0 ? "[" + StringUtil.appendWithSeparator(AstUtil.nodeToStringConverter.convert(clazz.generics), ",") + "]" : "");
      } else if (value instanceof FeatureSpecification) {
        FeatureSpecification fSpec = (FeatureSpecification)value;
        String featureNames = StringUtil.appendWithSeparator(AstUtil.nodeToStringConverter.convert(fSpec.featureNames),",");
        List<Type> argTypes = new ArrayList<Type>();
        for (FeatureArgument fArg : fSpec.arguments) {
          argTypes.add(fArg.type);
        }
        String args = "(" + StringUtil.appendWithSeparator(AstUtil.nodeToStringConverter.convert(argTypes),",") + ")";
        String returnType = fSpec.hasType == null ? "" : " " + StringUtil.prettyPrint(fSpec.hasType);
        return featureNames + args + returnType; 
      } else if (value instanceof ClientRelation) {
        ClientRelation rel = (ClientRelation)value;
        return rel.client.name + " client " + rel.supplier.name;  
      }
      return "NONE..." + value.getClass();
    }
    return "";
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
