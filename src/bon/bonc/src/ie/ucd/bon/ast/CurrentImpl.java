package ie.ucd.bon.ast;

import ie.ucd.bon.source.SourceLocation;

public class CurrentImpl extends Current {

	public CurrentImpl(SourceLocation location) {
    super(location);
  }

	public static CurrentImpl mk(SourceLocation location) {
	  return new CurrentImpl(location);
	}
	
  @Override
	public CurrentImpl clone() {
		return mk(getLocation());
	}
}
