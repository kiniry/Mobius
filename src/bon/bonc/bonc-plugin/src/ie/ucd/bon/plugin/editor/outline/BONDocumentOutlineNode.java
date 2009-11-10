package ie.ucd.bon.plugin.editor.outline;

import ie.ucd.bon.ast.AstNode;
import ie.ucd.bon.ast.BonSourceFile;
import ie.ucd.bon.ast.Cluster;
import ie.ucd.bon.ast.StaticDiagram;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.jface.viewers.TreeNode;

public class BONDocumentOutlineNode extends TreeNode {
  
  public BONDocumentOutlineNode(Object value) {
    super(value);
    System.out.println("Created node: " + value.getClass());
    setChildren(createChildren());
  }

  protected TreeNode[] createChildren() {
    System.out.println("creating");
    if (value instanceof BonSourceFile) {
      return elementsToTreeNodes(((BonSourceFile)value).bonSpecification);
    } else if (value instanceof StaticDiagram) {
      return elementsToTreeNodes(((StaticDiagram)value).components);
    } else if (value instanceof Cluster) {
      return elementsToTreeNodes(((Cluster)value).components);
    } else {
      return new TreeNode[0];
    }
  }
  
  private static TreeNode[] elementsToTreeNodes(List<? extends AstNode> els) {
    List<TreeNode> nodes = new ArrayList<TreeNode>(els.size());
    for (AstNode node : els) {
      nodes.add(new BONDocumentOutlineNode(node));
    }
    return nodes.toArray(new TreeNode[nodes.size()]);
  }
  

}
