/**
 * Copyright (c) 2007-2009, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.bon.typechecker;


public class ClientRelation {

  private String client;
  private String supplier;
  
//  private List<Object> clientEntities;
  
  //TODO should be enum type?
  private String typeMark;
  
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
  
  public void setTypeMark(String typeMark) {
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

  public String getTypeMark() {
    return typeMark;
  }
  
  
  
}
