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

import junit.framework.Test;
import junit.framework.TestSuite;


public class CustomTestSuite  {

	public static Test suite() {

        TestSuite suite = new TestSuite();
  
        //
        // Add suites for all custom test classes
        //

        suite.addTestSuite(ConcurrencyTest.class);
        
        suite.addTestSuite(RegExpStructTest.class);
        
        suite.addTestSuite(SemanticPropertyTest.class);

        suite.addTestSuite(SemanticPropertyLevelSpecificationTest.class);
        
        suite.addTestSuite(SemanticPropertyRefinementSpecificationTest.class);
       
        return suite;
    }

    /**
     * Runs the test suite using the textual runner.
     */
    public static void main(String[] args) {
        junit.textui.TestRunner.run(suite());
    }

}