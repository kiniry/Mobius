/**
 * Copyright (c) 2007-2009, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.typechecker;

import ie.ucd.bon.ast.TypeMark;


public class ClientRelation {

  private String client;
  private String supplier;
  
//  private List<Object> clientEntities;
  
  private TypeMark typeMark;
  
  public ClientRelation(String client) {
    this.client = client;
//    clientEntities = new LinkedList<Object>();
  }
  
  public void setSupplier(String supplier) {
    this.supplier = supplier;
  }
  
//  public void addClientEntity(Object entity) {
//    clientEntities.add(entity);
//  }
  
  public void setTypeMark(TypeMark typeMark) {
    this.typeMark = typeMark;
  }

  public String getClient() {
    return client;
  }

  public void setClient(String client) {
    this.client = client;
  }

  public String getSupplier() {
    return supplier;
  }

  public TypeMark getTypeMark() {
    return typeMark;
  }

  @Override
  public String toString() {
    return client + " client " + typeMark + " " + supplier;
  }
  
  
  
}
