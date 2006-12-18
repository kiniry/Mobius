package annot.bcclass.attributes;

public class LoopSpecification implements BCAttribute {
	SingleLoopSpecification[] loopSpecs;
	
	public LoopSpecification(SingleLoopSpecification[] _loopSpecs) {
		loopSpecs = _loopSpecs;
	}

	public SingleLoopSpecification[] getLoopSpecifications() {
		return loopSpecs;
	}
}
