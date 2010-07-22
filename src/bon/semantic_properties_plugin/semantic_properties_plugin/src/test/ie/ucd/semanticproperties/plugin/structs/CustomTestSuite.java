/**
 * Copyright (c) 2008-2010, http://code.google.com/p/snakeyaml/
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package ie.ucd.semanticproperties.plugin.structs;

import ie.ucd.semanticproperties.plugin.customobjects.CustomConstructorTestCase;
import ie.ucd.semanticproperties.plugin.customobjects.CustomRepresenterTestCase;
import ie.ucd.semanticproperties.plugin.customobjects.CustomResolverTestCase;

import java.util.HashMap;
import java.util.Map;

import junit.framework.Test;
import junit.framework.TestCase;
import junit.framework.TestSuite;

import org.yaml.snakeyaml.Dumper;
import org.yaml.snakeyaml.DumperOptions;
import org.yaml.snakeyaml.Loader;
import org.yaml.snakeyaml.Yaml;


public class CustomTestSuite  {

	public static Test suite() {

        TestSuite suite = new TestSuite();
  
        //
        // Add suites for all custom snakeyaml classes
        //
        suite.addTestSuite(CustomConstructorTestCase.class);

        suite.addTestSuite(CustomRepresenterTestCase.class);
        
        suite.addTestSuite(CustomResolverTestCase.class);
        
        suite.addTestSuite(SemanticProperyTest.class);
       
        return suite;
    }

    /**
     * Runs the test suite using the textual runner.
     */
    public static void main(String[] args) {
        junit.textui.TestRunner.run(suite());
    }

}