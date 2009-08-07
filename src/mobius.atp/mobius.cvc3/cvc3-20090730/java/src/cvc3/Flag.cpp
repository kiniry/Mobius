#include "JniUtils.h"

using namespace std;
using namespace Java_cvc3_JniUtils;
using namespace CVC3;

extern "C"
JNIEXPORT jboolean JNICALL Java_cvc3_Flag_jniIsNull
(JNIEnv* env, jclass, jobject jflag)
{
  try {
    const CLFlag* flag = unembed_const<CLFlag>(env, jflag);
    return (flag->getType() == CLFLAG_NULL);
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jboolean JNICALL Java_cvc3_Flag_jniIsBool
(JNIEnv* env, jclass, jobject jflag)
{
  try {
    const CLFlag* flag = unembed_const<CLFlag>(env, jflag);
    return (flag->getType() == CLFLAG_BOOL);
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jboolean JNICALL Java_cvc3_Flag_jniIsInt
(JNIEnv* env, jclass, jobject jflag)
{
  try {
    const CLFlag* flag = unembed_const<CLFlag>(env, jflag);
    return (flag->getType() == CLFLAG_INT);
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jboolean JNICALL Java_cvc3_Flag_jniIsString
(JNIEnv* env, jclass, jobject jflag)
{
  try {
    const CLFlag* flag = unembed_const<CLFlag>(env, jflag);
    return (flag->getType() == CLFLAG_STRING);
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jboolean JNICALL Java_cvc3_Flag_jniIsStringVec
(JNIEnv* env, jclass, jobject jflag)
{
  try {
    const CLFlag* flag = unembed_const<CLFlag>(env, jflag);
    return (flag->getType() == CLFLAG_STRVEC);
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jboolean JNICALL Java_cvc3_Flag_jniGetBool
(JNIEnv* env, jclass, jobject jflag)
{
  try {
    const CLFlag* flag = unembed_const<CLFlag>(env, jflag);
    return flag->getBool();
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jint JNICALL Java_cvc3_Flag_jniGetInt
(JNIEnv* env, jclass, jobject jflag)
{
  try {
    const CLFlag* flag = unembed_const<CLFlag>(env, jflag);
    return flag->getInt();
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jstring JNICALL Java_cvc3_Flag_jniGetString
(JNIEnv* env, jclass, jobject jflag)
{
  try {
    const CLFlag* flag = unembed_const<CLFlag>(env, jflag);
    return toJava(env, flag->getString());
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jstring JNICALL Java_cvc3_Flag_jniGetHelp
(JNIEnv* env, jclass, jobject jflag)
{
  try {
    const CLFlag* flag = unembed_const<CLFlag>(env, jflag);
    return toJava(env, flag->getHelp());
  } catch (const Exception& e) { toJava(env, e); };
}

