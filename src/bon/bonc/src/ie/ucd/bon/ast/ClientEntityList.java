
/**
  This class is generated automatically from normal_classes.tpl. 
  Do not edit.
 */
package ie.ucd.bon.ast;

import java.util.List;
import ie.ucd.bon.source.SourceLocation;

public class ClientEntityList extends ClientEntityExpression {



  private final List<ClientEntity> entities;


  // === Constructors and Factories ===
  protected ClientEntityList(List<ClientEntity> entities, SourceLocation location) {
    super(location);
    this.entities = entities; assert entities != null;
    
  }
  
  public static ClientEntityList mk(List<ClientEntity> entities, SourceLocation location) {
    return new ClientEntityList(entities, location);
  }

  // === Accessors ===

  public List<ClientEntity> getEntities() { return entities; }

  // === Visitor ===
  public void accept(IVisitor visitor) {
    visitor.visitClientEntityList(this);
  }

  // === Others ===
  @Override
  public ClientEntityList clone() {
    List<ClientEntity> newEntities = entities;
    
    return ClientEntityList.mk(newEntities, getLocation());
  }
  
  @Override
  public String toString() {
    StringBuilder sb = new StringBuilder();
    sb.append("ClientEntityList ast node: ");
    
    sb.append("entities = ");
    sb.append(entities);
    sb.append(", ");
    
    if (sb.length() >= 2) {
      sb.delete(sb.length()-2,sb.length());
    }
    return sb.toString();
  }
}

