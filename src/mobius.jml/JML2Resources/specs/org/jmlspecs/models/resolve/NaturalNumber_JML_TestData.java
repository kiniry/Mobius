// @(#)$Id: NaturalNumber_JML_TestData.java,v 1.6 2005/07/07 21:03:09 leavens Exp $

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

package org.jmlspecs.models.resolve;

import java.math.BigInteger;

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
public abstract class NaturalNumber_JML_TestData
    extends junit.framework.TestCase
{
    /** Initialize this class. */
    public NaturalNumber_JML_TestData(java.lang.String name) {
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
        return new junit.framework.TestSuite("Overall tests for NaturalNumber");
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

    private final BigInteger nines
                = new BigInteger("999999999999999999999999999999999999");

    /** Return a new, freshly allocated indefinite iterator that
     * produces test data of type 
     * org.jmlspecs.models.resolve.NaturalNumber
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
        vorg_jmlspecs_models_resolve_NaturalNumberIter
        (java.lang.String methodName, int loopsThisSurrounds)
    {
        if (methodName.equals("multiply") || methodName.equals("pow")) {
            return vorg_jmlspecs_models_resolve_NatSmallStrategy.iterator();
        } else {
            return vorg_jmlspecs_models_resolve_NaturalNumberStrategy.iterator();        }
    }

    /** The strategy for generating test data of type
     * org.jmlspecs.models.resolve.NaturalNumber. */
    private org.jmlspecs.jmlunit.strategies.StrategyType
        vorg_jmlspecs_models_resolve_NaturalNumberStrategy
        = new org.jmlspecs.jmlunit.strategies.ImmutableObjectAbstractStrategy()
            {
                protected java.lang.Object[] addData() {
                    return new org.jmlspecs.models.resolve.NaturalNumber[] {
                        new NaturalNumber(),
                        new NaturalNumber(1L),
                        new NaturalNumber(3L),
                        new NaturalNumber(Long.MAX_VALUE),
                        new NaturalNumber(nines),
                        new NaturalNumber(nines.add(nines)),
                    };
                }
            };

    /** The strategy for generating test data of type
     * org.jmlspecs.models.resolve.NaturalNumber. */
    private org.jmlspecs.jmlunit.strategies.StrategyType
        vorg_jmlspecs_models_resolve_NatSmallStrategy
        = new org.jmlspecs.jmlunit.strategies.ImmutableObjectAbstractStrategy()
            {
                protected java.lang.Object[] addData() {
                    return new org.jmlspecs.models.resolve.NaturalNumber[] {
                        new NaturalNumber(),
                        new NaturalNumber(1L),
                        new NaturalNumber(3L),
                        new NaturalNumber(23L),
                    };
                }
            };

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
            vorg_jmlspecs_models_resolve_NaturalNumberStrategy,
        });

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
        if (methodName.equals("pow") || methodName.equals("shiftLeft")
            || methodName.equals("shiftRight")) {
            return new org.jmlspecs.jmlunit.strategies.IntStrategy()
            {
                protected int[] addData() {
                    return new int[] {
                        2, 3,
                    };
                }
            }
                .intIterator();
        } else {
            return new org.jmlspecs.jmlunit.strategies.IntBigStrategy()
                .intIterator();
        }
    }

    /** Return a new, freshly allocated indefinite iterator that
     * produces test data of type 
     * java.math.BigInteger
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
        vjava_math_BigIntegerIter
        (java.lang.String methodName, int loopsThisSurrounds)
    {
        return vjava_math_BigIntegerStrategy.iterator();
    }

    /** The strategy for generating test data of type
     * java.math.BigInteger. */
    private org.jmlspecs.jmlunit.strategies.StrategyType
        vjava_math_BigIntegerStrategy
        = new org.jmlspecs.jmlunit.strategies.ImmutableObjectAbstractStrategy()
            {
                protected java.lang.Object[] addData() {
                    return new java.math.BigInteger[] {
                        BigInteger.ZERO,
                        BigInteger.ONE,
                        new BigInteger("-23"),
                        new BigInteger("11"),
                    };
                }
            };

    /** Return a new, freshly allocated indefinite iterator that
     * produces test data of type 
     * long
     * for testing the method named by the String methodName in
     * a loop that encloses loopsThisSurrounds many other loops.
     * @param methodName name of the method for which this
     *                      test data will be used.
     * @param loopsThisSurrounds number of loops that the test
     *                           contains inside this one.
     */
    //@ requires methodName != null && loopsThisSurrounds >= 0;
    //@ ensures \fresh(\result);
    protected org.jmlspecs.jmlunit.strategies.LongIterator
        vlongIter
        (java.lang.String methodName, int loopsThisSurrounds)
    {
        return vlongStrategy.longIterator();
    }

    /** The strategy for generating test data of type
     * long. */
    private org.jmlspecs.jmlunit.strategies.LongStrategyType
        vlongStrategy
        = new org.jmlspecs.jmlunit.strategies.LongStrategy()
            {
                protected long[] addData() {
                    return new long[] {
                        0L, -1L, 1L, 2L, Long.MAX_VALUE, Long.MIN_VALUE, 541L,
                    };
                }
            };
}
