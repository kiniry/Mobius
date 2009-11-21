import log.CCLogManager;
import utils.*;
import utils.ModifierManager.ClassModifier;
import utils.ModifierManager.FeatureModifier;
import utils.smart.*;


public class ErrorMessages {

	static CCLogManager mylog = new CCLogManager();
	SourceLocation soc = new SourceLocation();
	private SmartString classJ = new SmartString("Foo");
	private SmartString featJ = new SmartString("methodOne");
	private SmartString methodJ = new SmartString("methodOne");
	
	public void generateErrors() {
		System.out.println("logAssignableDefaultCorrespondence");
		mylog.logAssignableDefaultCorrespondence();
		mylog.logClassNotFound(classJ);
		mylog.logExpectedAllPublic(soc, classJ);
		mylog.logExpectedClassModifier(soc, classJ, ClassModifier.ABSTRACT);
		mylog.logExpectedEnum(soc, classJ);
		mylog.logExpectedFeatureModifier(soc, classJ, featJ , FeatureModifier.ABSTRACT);
		mylog.logExpectedFeatureModifierWarning(soc, classJ, featJ, FeatureModifier.ABSTRACT);
		mylog.logGenericMethodNotSupported(soc, classJ, methodJ);
		mylog.logHistoryConstraints();
		mylog.logIncorrectFeatureType(soc, classJ, featJ, FeatureType.COMMAND, FeatureType.MIXED);
		mylog.logIncorrectFrameCondition(soc, classJ, featJ, "varOne", "varTwo");
		mylog.logIncorrectFrameDefault(soc, classJ, featJ, the_expected, the_found)
		mylog.logIncorrectGenerics(soc, classJ, the_expected, the_found)
		mylog.logIncorrectGenericsNumber(soc, classJ, the_expected, the_found)
		mylog.logIncorrectMapping(soc, "method@Foo");
		mylog.logIncorrectModifier(soc, classJ, featJ, the_expected, the_found)
		mylog.logIncorrectPackage(soc, classJ, the_expected, the_found)
		mylog.logIncorrectParameterTypeNullity(soc, classJ, featJ);
		mylog.logIncorrectReturnType(soc, classJ, featJ, the_expected, the_found)
		mylog.logIncorrectReturnTypeNullity(soc, classJ, featJ, the_expected, the_found)
		mylog.logIncorrectVisibilityModifier(soc, classJ, featJ, the_expected, the_found)
		mylog.logMissingAggregation(soc, classJ, a_missing_cls)
		mylog.logMissingConstructor(soc, classJ);
		mylog.logMissingFeature(soc, classJ, the_features)
		mylog.logMissingFrameCondition(soc, classJ, featJ, a_frame)
		mylog.logMissingHistoryContraint(soc, classJ, the_cond)
		mylog.logMissingInterface(soc, classJ, a_missing_cls)
		mylog.logMissingInvariant(soc, classJ);
		mylog.logMissingInvariantClauses(soc, classJ, the_clauses)
		mylog.logMissingParameter(soc, classJ, featJ, some_params)
		mylog.logMissingPostcondition(soc, classJ, featJ, the_post)
		mylog.logMissingPrecondition(soc, classJ, featJ, the_pre)
		mylog.logMissingSharedAssociation(soc, classJ, a_missing_cls)
		mylog.logMultipleClasses(classJ);
		mylog.logNotAccessible(soc, classJ);
		mylog.logNullityDefaultCorrespondence();
		mylog.logRedefinedCorrespondence(soc, classJ, featJ);
		mylog.logRedundantAggregation(soc, classJ, the_redundant_ass)
		mylog.logRedundantConstructor(soc, classJ);
		mylog.logRedundantEnclosingClass(soc, classJ, the_found)
		mylog.logRedundantFeature(soc, classJ, the_features)
		mylog.logRedundantInterface(soc, classJ, a_redundant_cls)
		mylog.logRedundantSharedAssociation(soc, classJ, the_redundant_ass)
		mylog.logShouldNotClassModifier(soc, classJ, a_should_not)
		mylog.logShouldNotEnum(soc, classJ);
		mylog.logShouldNotFeatureModifierWarning(soc, classJ, featJ, a_should_not)
		mylog.logTooManyInvariant(soc, classJ, the_inv)
		mylog.logTooManyParameter(soc, classJ, featJ, some_params)
		mylog.logTooManyPostcondition(soc, classJ, featJ, the_post)
		mylog.logTooManyPrecondition(soc, classJ, featJ, the_pre)
		
		
		
	}
	
	
}
