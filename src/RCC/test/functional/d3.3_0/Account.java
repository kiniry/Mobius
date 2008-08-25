class OwnerInfo {}

public class Account {
  private OwnerInfo ownerInfo /*# guarded_by this */;
  private volatile int balance;
  public synchronized OwnerInfo getOwnerInfo() { return ownerInfo; }
  public void setOwnerInfo(OwnerInfo ownerInfo) /*# requires this */ {
    this.ownerInfo = ownerInfo;
  }
  public void deposit(int amount) { balance += amount; }
}
