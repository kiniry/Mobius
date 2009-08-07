#include "JniUtils.h"

using namespace std;
using namespace Java_cvc3_JniUtils;
using namespace CVC3;

extern "C"
JNIEXPORT void JNICALL Java_cvc3_FlagsMut_jniSetFlag1
(JNIEnv* env, jclass, jobject jflags, jstring jname, jboolean jvalue)
{
  try {
    CLFlags* flags = unembed_mut<CLFlags>(env, jflags);
    string name(toCpp(env, jname));
    bool value(jvalue);
    flags->setFlag(name, value);
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT void JNICALL Java_cvc3_FlagsMut_jniSetFlag2
(JNIEnv* env, jclass, jobject jflags, jstring jname, jint jvalue)
{
  try {
    CLFlags* flags = unembed_mut<CLFlags>(env, jflags);
    string name(toCpp(env, jname));
    int value(jvalue);
    flags->setFlag(name, value);
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT void JNICALL Java_cvc3_FlagsMut_jniSetFlag3
(JNIEnv* env, jclass, jobject jflags, jstring jname, jstring jvalue)
{
  try {
    CLFlags* flags = unembed_mut<CLFlags>(env, jflags);
    string name(toCpp(env, jname));
    string value(toCpp(env, jvalue));
    flags->setFlag(name, value);
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT void JNICALL Java_cvc3_FlagsMut_jniSetFlag4
(JNIEnv* env, jclass, jobject jflags, jstring jmap, jstring jname, jboolean jvalue)
{
  try {
    CLFlags* flags = unembed_mut<CLFlags>(env, jflags);
    string map(toCpp(env, jmap));
    string name(toCpp(env, jname));
    bool value(jvalue);
    flags->setFlag(map, std::make_pair(name, value));
  } catch (const Exception& e) { toJava(env, e); };
}

