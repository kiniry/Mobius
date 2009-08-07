#include <rational.h>
#include "JniUtils.h"

using namespace std;
using namespace Java_cvc3_JniUtils;
using namespace CVC3;

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_Rational_jniRational1
(JNIEnv* env, jclass, jint jn, jint jd)
{
  try {
    int n(jn);
    int d(jd);
    return embed_copy(env, Rational(n, d));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_Rational_jniRational2
(JNIEnv* env, jclass, jstring jn, jint jd)
{
  try {
    string n(toCpp(env, jn));
    int d(jd);
    return embed_copy(env, Rational(n, d));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_Rational_jniRational3
(JNIEnv* env, jclass, jstring jn, jstring jd, jint jbase)
{
  try {
    string n(toCpp(env, jn));
    string d(toCpp(env, jd));
    int base(jbase);
    return embed_copy(env, Rational(n, d, base));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jboolean JNICALL Java_cvc3_Rational_jniEquals
(JNIEnv* env, jclass, jobject jr1, jobject jr2)
{
  try {
    const Rational* r1 = unembed_const<Rational>(env, jr1);
    const Rational* r2 = unembed_const<Rational>(env, jr2);
    return *r1 == *r2;
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jstring JNICALL Java_cvc3_Rational_jniToString
(JNIEnv* env, jclass, jobject jr)
{
  try {
    const Rational* r = unembed_const<Rational>(env, jr);
    return toJava(env, r->toString());
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jint JNICALL Java_cvc3_Rational_jniHash
(JNIEnv* env, jclass, jobject jr)
{
  try {
    const Rational* r = unembed_const<Rational>(env, jr);
    return r->hash();
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jboolean JNICALL Java_cvc3_Rational_jniIsLe
(JNIEnv* env, jclass, jobject jr1, jobject jr2)
{
  try {
    const Rational* r1 = unembed_const<Rational>(env, jr1);
    const Rational* r2 = unembed_const<Rational>(env, jr2);
    return *r1 <= *r2;
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jboolean JNICALL Java_cvc3_Rational_jniIsLt
(JNIEnv* env, jclass, jobject jr1, jobject jr2)
{
  try {
    const Rational* r1 = unembed_const<Rational>(env, jr1);
    const Rational* r2 = unembed_const<Rational>(env, jr2);
    return *r1 < *r2;
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jboolean JNICALL Java_cvc3_Rational_jniIsGe
(JNIEnv* env, jclass, jobject jr1, jobject jr2)
{
  try {
    const Rational* r1 = unembed_const<Rational>(env, jr1);
    const Rational* r2 = unembed_const<Rational>(env, jr2);
    return *r1 >= *r2;
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jboolean JNICALL Java_cvc3_Rational_jniIsGt
(JNIEnv* env, jclass, jobject jr1, jobject jr2)
{
  try {
    const Rational* r1 = unembed_const<Rational>(env, jr1);
    const Rational* r2 = unembed_const<Rational>(env, jr2);
    return *r1 > *r2;
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_Rational_jniPlus
(JNIEnv* env, jclass, jobject jr1, jobject jr2)
{
  try {
    const Rational* r1 = unembed_const<Rational>(env, jr1);
    const Rational* r2 = unembed_const<Rational>(env, jr2);
    return embed_copy(env, *r1 + *r2);
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_Rational_jniMinus
(JNIEnv* env, jclass, jobject jr1, jobject jr2)
{
  try {
    const Rational* r1 = unembed_const<Rational>(env, jr1);
    const Rational* r2 = unembed_const<Rational>(env, jr2);
    return embed_copy(env, *r1 + *r2);
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_Rational_jniMult
(JNIEnv* env, jclass, jobject jr1, jobject jr2)
{
  try {
    const Rational* r1 = unembed_const<Rational>(env, jr1);
    const Rational* r2 = unembed_const<Rational>(env, jr2);
    return embed_copy(env, *r1 + *r2);
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_Rational_jniDivide
(JNIEnv* env, jclass, jobject jr1, jobject jr2)
{
  try {
    const Rational* r1 = unembed_const<Rational>(env, jr1);
    const Rational* r2 = unembed_const<Rational>(env, jr2);
    return embed_copy(env, *r1 + *r2);
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_Rational_jniMod
(JNIEnv* env, jclass, jobject jr1, jobject jr2)
{
  try {
    const Rational* r1 = unembed_const<Rational>(env, jr1);
    const Rational* r2 = unembed_const<Rational>(env, jr2);
    return embed_copy(env, *r1 % *r2);
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_Rational_jniGetNumerator
(JNIEnv* env, jclass, jobject jr)
{
  try {
    const Rational* r = unembed_const<Rational>(env, jr);
    return embed_copy(env, r->getNumerator());
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_Rational_jniGetDenominator
(JNIEnv* env, jclass, jobject jr)
{
  try {
    const Rational* r = unembed_const<Rational>(env, jr);
    return embed_copy(env, r->getDenominator());
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jboolean JNICALL Java_cvc3_Rational_jniIsInteger
(JNIEnv* env, jclass, jobject jr)
{
  try {
    const Rational* r = unembed_const<Rational>(env, jr);
    return r->isInteger();
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jint JNICALL Java_cvc3_Rational_jniGetInteger
(JNIEnv* env, jclass, jobject jr)
{
  try {
    Rational* r = unembed_mut<Rational>(env, jr);
    return r->getInt();
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_Rational_jniGcd
(JNIEnv* env, jclass, jobject jr1, jobject jr2)
{
  try {
    const Rational* r1 = unembed_const<Rational>(env, jr1);
    const Rational* r2 = unembed_const<Rational>(env, jr2);
    return embed_copy(env, gcd(*r1, *r2));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_Rational_jniLcm
(JNIEnv* env, jclass, jobject jr1, jobject jr2)
{
  try {
    const Rational* r1 = unembed_const<Rational>(env, jr1);
    const Rational* r2 = unembed_const<Rational>(env, jr2);
    return embed_copy(env, lcm(*r1, *r2));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_Rational_jniAbs
(JNIEnv* env, jclass, jobject jr)
{
  try {
    const Rational* r = unembed_const<Rational>(env, jr);
    return embed_copy(env, abs(*r));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_Rational_jniFloor
(JNIEnv* env, jclass, jobject jr)
{
  try {
    const Rational* r = unembed_const<Rational>(env, jr);
    return embed_copy(env, floor(*r));
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_Rational_jniCeil
(JNIEnv* env, jclass, jobject jr)
{
  try {
    const Rational* r = unembed_const<Rational>(env, jr);
    return embed_copy(env, ceil(*r));
  } catch (const Exception& e) { toJava(env, e); };
}

