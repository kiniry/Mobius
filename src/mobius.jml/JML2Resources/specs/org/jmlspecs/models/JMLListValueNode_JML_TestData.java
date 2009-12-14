// @(#)$Id: JMLListValueNode_JML_TestData.java,v 1.5 2005/07/07 21:03:07 leavens Exp $

// Copyright (C) 2005 Iowa State University
//
// This file is part of the runtime library of the Java Modeling Language.
//
// This library is free software; you can redistribute it and/or
// modify it under the terms of the GNU Lesser General Public License
// as published by the Free Software Foundation; either version 2.1,
// of the License, or (at your option) any later version.
//
// This library is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
// Lesser General Public License for more details.
//
// You should have received a copy of the GNU Lesser General Public License
// along with JML; see the file LesserGPL.txt.  If not, write to the Free
// Software Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA
// 02110-1301  USA.

package org.jmlspecs.models;

/** Supply test data for the JML and JUnit based testing of 
 *  Person.
 *
 *  <p>Test data is supplied by overriding methods in this class.  See
 *  the JML documentation and the comments below about how to do this.
 *
 *  <p>This class is also the place to override the <kbd>setUp()</kbd>
 *  and <kbd>tearDown()</kbd> methods if your testing needs some
 *  actions to be taken before and after each test is executed.
 *
 *  <p>This class is never rewritten by jmlunit.
 *
 */
public abstract class JMLListValueNode_JML_TestData
    extends junit.framework.TestCase
{
    /** Initialize this class. */
    public JMLListValueNode_JML_TestData(java.lang.String name) {
        super(name);
    }

    /** Return the overall test suite for accumulating tests; the
     * result will hold every test that will be run.  This factory
     * method can be altered to provide filtering of test suites, as
     * they are added to this overall test suite, based on various
     * criteria.  The test driver will first call the method
     * addTestSuite to add a test suite formed from custom programmed
     * test methods (named testX for some X), which you can add to
     * this class; this initial test suite will also include a method
     * to check that the code being tested was compiled with jmlc.
     * After that, for each method to be tested, a test suite
     * containing tests for that method will be added to this overall
     * test suite, using the addTest method.  Test suites added for a
     * method will have some subtype of TestSuite and that method's
     * name as their name. So, if you want to control the overall
     * suite of tests for testing some method, e.g., to limit the
     * number of tests for each method, return a special-purpose
     * subclass of junit.framework.TestSuite in which you override the
     * addTest method.
     * @see junit.framework.TestSuite
     */
    //@ assignable objectState;
    //@ ensures \result != null;
    public junit.framework.TestSuite overallTestSuite() {
        return new junit.framework.TestSuite("Overall tests for JMLListValueNode");
    }

    /** Return an empty test suite for accumulating tests for the
     * named method.  This factory method can be altered to provide
     * filtering or limiting of the tests for the named method, as
     * they are added to the test suite for this method.  The driver
     * will add individual tests using the addTest method.  So, if you
     * want to filter individual tests, return a subclass of TestSuite
     * in which you override the addTest method.
     * @param methodName The method the tests in this suite are for.
     * @see junit.framework.TestSuite
     * @see org.jmlspecs.jmlunit.strategies.LimitedTestSuite
     */
    //@ assignable objectState;
    //@ ensures \result != null;
    public junit.framework.TestSuite emptyTestSuiteFor
        (java.lang.String methodName)
    {
        return new junit.framework.TestSuite(methodName);
    }

    // You should edit the following code to supply test data.  In the
    // skeleton originally supplied below the jmlunit tool made a
    // guess as to a minimal strategy for generating test data for
    // each type of object used as a receiver, and each type used as
    // an argument.  There is a library of strategies for generating
    // test data in org.jmlspecs.jmlunit.strategies, which are used in
    // the tool's guesses.  See the documentation for JML and in
    // particular for the org.jmlspecs.jmlunit.strategies package for
    // a general discussion of how to do this.  (This package's
    // documentation is available through the JML.html file in the top
    // of the JML release, and also in the package.html file that
    // ships with the package.)
    //
    // You can change the strategies guessed by the jmlunit tool, and
    // you can also define new ones to suit your needs.  You can also
    // delete any useless sample test data that has been generated
    // for you to show you the pattern of how to add your own test
    // data.  The only requirement is that you implement the methods
    // below.
    //
    // If you change the type being tested in a way that introduces
    // new types of arguments for some methods, then you will have to
    // introduce (by hand) definitions that are similar to the ones
    // below, because jmlunit never rewrites this file.

    /** Return a new, freshly allocated indefinite iterator that
     * produces test data of type 
     * org.jmlspecs.models.JMLType
     * for testing the method named by the String methodName in
     * a loop that encloses loopsThisSurrounds many other loops.
     * @param methodName name of the method for which this
     *                      test data will be used.
     * @param loopsThisSurrounds number of loops that the test
     *                           contains inside this one.
     */
    //@ requires methodName != null && loopsThisSurrounds >= 0;
    //@ ensures \fresh(\result);
    protected org.jmlspecs.jmlunit.strategies.IndefiniteIterator
        vorg_jmlspecs_models_JMLTypeIter
        (java.lang.String methodName, int loopsThisSurrounds)
    {
        return vorg_jmlspecs_models_JMLTypeStrategy.iterator();
    }

    /** The strategy for generating test data of type
     * org.jmlspecs.models.JMLType. */
    private org.jmlspecs.jmlunit.strategies.StrategyType
        vorg_jmlspecs_models_JMLTypeStrategy
        = new org.jmlspecs.jmlunit.strategies.ImmutableObjectAbstractStrategy()
            {
                protected java.lang.Object[] addData() {
                    return new org.jmlspecs.models.JMLType[] {
                        new JMLInteger(3),
                        new JMLInteger(4),
                        new JMLFloat(7.3f),
                        JMLListValueNode.cons(new JMLInteger(4),
                                              JMLListValueNode.cons(new JMLInteger(4),
                                                                    null)),
                    };
                }
            };

    /** Return a new, freshly allocated indefinite iterator that
     * produces test data of type 
     * org.jmlspecs.models.JMLListValueNode
     * for testing the method named by the String methodName in
     * a loop that encloses loopsThisSurrounds many other loops.
     * @param methodName name of the method for which this
     *                      test data will be used.
     * @param loopsThisSurrounds number of loops that the test
     *                           contains inside this one.
     */
    //@ requires methodName != null && loopsThisSurrounds >= 0;
    //@ ensures \fresh(\result);
    protected org.jmlspecs.jmlunit.strategies.IndefiniteIterator
        vorg_jmlspecs_models_JMLListValueNodeIter
        (java.lang.String methodName, int loopsThisSurrounds)
    {
        return vorg_jmlspecs_models_JMLListValueNodeStrategy.iterator();
    }

    /** The strategy for generating test data of type
     * org.jmlspecs.models.JMLListValueNode. */
    private org.jmlspecs.jmlunit.strategies.StrategyType
        vorg_jmlspecs_models_JMLListValueNodeStrategy
        = new org.jmlspecs.jmlunit.strategies.ImmutableObjectAbstractStrategy()
            {
                protected java.lang.Object[] addData() {
                    return new org.jmlspecs.models.JMLListValueNode[] {
                        new JMLListValueNode(null, null),
                        new JMLListValueNode(new JMLInteger(3), null),
                        new JMLListValueNode(null,
                                             new JMLListValueNode(null, null)),
                        new JMLListValueNode(new JMLInteger(3),
                                             new JMLListValueNode
                                             (new JMLInteger(4),
                                              null)),
                        new JMLListValueNode(null,
                                             new JMLListValueNode
                                             (new JMLInteger(4),
                                              null)),
                        new JMLListValueNode(new JMLFloat(7.3f),
                                             new JMLListValueNode
                                             (new JMLInteger(4),
                                              null)),
                        new JMLListValueNode(new JMLFloat(7.3f),
                                             new JMLListValueNode
                                             (new JMLInteger(4),
                                              new JMLListValueNode(null,
                                                                   null))),
                        new JMLListValueNode(null, 
                                             new JMLListValueNode
                                             (new JMLInteger(4),
                                              new JMLListValueNode
                                              (new JMLFloat(7.3f),
                                               null))),
                    };
                }
            };

    /** Return a new, freshly allocated indefinite iterator that
     * produces test data of type 
     * int
     * for testing the method named by the String methodName in
     * a loop that encloses loopsThisSurrounds many other loops.
     * @param methodName name of the method for which this
     *                      test data will be used.
     * @param loopsThisSurrounds number of loops that the test
     *                           contains inside this one.
     */
    //@ requires methodName != null && loopsThisSurrounds >= 0;
    //@ ensures \fresh(\result);
    protected org.jmlspecs.jmlunit.strategies.IntIterator
        vintIter
        (java.lang.String methodName, int loopsThisSurrounds)
    {
        return vintStrategy.intIterator();
    }

    /** The strategy for generating test data of type
     * int. */
    private org.jmlspecs.jmlunit.strategies.IntStrategyType
        vintStrategy
        = new org.jmlspecs.jmlunit.strategies.IntBigStrategy();

    /** Return a new, freshly allocated indefinite iterator that
     * produces test data of type 
     * java.lang.Object
     * for testing the method named by the String methodName in
     * a loop that encloses loopsThisSurrounds many other loops.
     * @param methodName name of the method for which this
     *                      test data will be used.
     * @param loopsThisSurrounds number of loops that the test
     *                           contains inside this one.
     */
    //@ requires methodName != null && loopsThisSurrounds >= 0;
    //@ ensures \fresh(\result);
    protected org.jmlspecs.jmlunit.strategies.IndefiniteIterator
        vjava_lang_ObjectIter
        (java.lang.String methodName, int loopsThisSurrounds)
    {
        return vjava_lang_ObjectStrategy.iterator();
    }

    /** The strategy for generating test data of type
     * java.lang.Object. */
    private org.jmlspecs.jmlunit.strategies.StrategyType
        vjava_lang_ObjectStrategy
        = new org.jmlspecs.jmlunit.strategies.CompositeStrategy
        (new org.jmlspecs.jmlunit.strategies.StrategyType[] {
            new org.jmlspecs.jmlunit.strategies.ObjectStrategy(),
            vorg_jmlspecs_models_JMLListValueNodeStrategy,
        });
}
