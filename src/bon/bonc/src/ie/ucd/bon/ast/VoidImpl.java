package ie.ucd.bon.ast;

import ie.ucd.bon.source.SourceLocation;

public class VoidImpl extends Void {

	public VoidImpl(SourceLocation location) {
    super(location);
  }

	public static VoidImpl mk(SourceLocation location) {
	  return new VoidImpl(location);
	}
	
  @Override
	public VoidImpl clone() {
		return mk(getLocation());
	}
}
