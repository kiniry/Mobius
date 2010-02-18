package utils.smart;

import utils.BeetlzSourceLocation;

public class TypeSmartStringWithLocation extends TypeSmartString {

  private final BeetlzSourceLocation my_loc;
  
  public TypeSmartStringWithLocation(String aName, BeetlzSourceLocation a_loc) {
    super(aName);
    this.my_loc = a_loc;
  }
  
  public TypeSmartStringWithLocation(TypeSmartString aSS, BeetlzSourceLocation a_loc) {
    super(aSS.my_string);
    this.my_loc = a_loc;
  }

  public BeetlzSourceLocation getLocation() {
    return my_loc;
  }

}
