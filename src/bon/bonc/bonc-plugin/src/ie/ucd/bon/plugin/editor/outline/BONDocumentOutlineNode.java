package ie.ucd.bon.plugin.editor.outline;

import ie.ucd.bon.ast.AstNode;
import ie.ucd.bon.ast.BonSourceFile;
import ie.ucd.bon.ast.Clazz;
import ie.ucd.bon.ast.Cluster;
import ie.ucd.bon.ast.Feature;
import ie.ucd.bon.ast.FeatureSpecification;
import ie.ucd.bon.ast.StaticDiagram;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.jface.viewers.TreeNode;

public class BONDocumentOutlineNode extends TreeNode {
  
  private static TreeNode[] NO_CHILDREN = new TreeNode[0];
  
  public BONDocumentOutlineNode(BONDocumentOutlineNode parent, AstNode value) {
    super(value);
    setChildren(createChildren());
    setParent(parent);
  }

  protected TreeNode[] createChildren() {
    if (value instanceof BonSourceFile) {
      return elementsToTreeNodes(this, ((BonSourceFile)value).bonSpecification);
    } else if (value instanceof StaticDiagram) {
      return elementsToTreeNodes(this, ((StaticDiagram)value).components);
    } else if (value instanceof Cluster) {
      return elementsToTreeNodes(this, ((Cluster)value).components);
    } else if (value instanceof Clazz) {
      Clazz clazz = (Clazz)value;
      if (clazz.classInterface == null) {
        return NO_CHILDREN;
      } else {
        List<FeatureSpecification> featureSpecs = new ArrayList<FeatureSpecification>();
        for (Feature feat : clazz.classInterface.features) {
         featureSpecs.addAll(feat.featureSpecifications); 
        }        
        return elementsToTreeNodes(this, featureSpecs);
      }
    } else {
      return NO_CHILDREN;
    }
  }
  
  public static TreeNode[] elementsToTreeNodes(BONDocumentOutlineNode parent, List<? extends AstNode> els) {
    List<TreeNode> nodes = new ArrayList<TreeNode>(els.size());
    for (AstNode node : els) {
      nodes.add(new BONDocumentOutlineNode(parent, node));
    }
    return nodes.toArray(new TreeNode[nodes.size()]);
  }

  @Override
  public AstNode getValue() {
    return (AstNode)super.getValue();
  }

  @Override
  public String toString() {
    return "Tree node: " + value;
  }  
  
}
