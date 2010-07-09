package ie.ucd.semantic_properties_plugin.file_checker;

import java.util.regex.Pattern;

import org.yaml.snakeyaml.nodes.Tag;
import org.yaml.snakeyaml.resolver.Resolver;

public class RefinementResolver extends Resolver {

	protected void addImplicitResolvers() {
		addImplicitResolver(new Tag("!transitions"), Pattern.compile("(?:equivalent|equals)"), null);
	}
}