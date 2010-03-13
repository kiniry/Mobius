
/**
 * Copyright (c) 2007-2010, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 *
 * This class is generated automatically from normal_classes.tpl.
 * Do not edit.
 */
package ie.ucd.bon.ast;

import java.util.List;
import ie.ucd.bon.source.SourceLocation;
import ie.ucd.bon.util.StringUtil;

public class ClientEntityList extends ClientEntityExpression {



  public final List<ClientEntity> entities;


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
  public void accept(IVisitorWithAdditions visitor) {
    visitor.visitClientEntityList(this, entities, getLocation());
  }

  // === Others ===
  @Override
  public ClientEntityList clone() {
    List<ClientEntity> newEntities = entities;
    return ClientEntityList.mk(newEntities, getLocation());
  }

  @Override
  public String toString() {
    return StringUtil.prettyPrint(this);
  }
}

