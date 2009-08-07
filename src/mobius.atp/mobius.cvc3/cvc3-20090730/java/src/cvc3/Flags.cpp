#include "JniUtils.h"

using namespace std;
using namespace Java_cvc3_JniUtils;
using namespace CVC3;

extern "C"
JNIEXPORT jobjectArray JNICALL Java_cvc3_Flags_jniGetFlags
(JNIEnv* env, jclass, jobject jflags, jstring jprefix)
{
  try {
    const CLFlags* flags = unembed_const<CLFlags>(env, jflags);
    string prefix(toCpp(env, jprefix));
        
    // get flag names
    vector<string> names;
    flags->countFlags(prefix, names);
    return toJavaV(env, names);
  } catch (const Exception& e) { toJava(env, e); };
}

extern "C"
JNIEXPORT jobject JNICALL Java_cvc3_Flags_jniGetFlag
(JNIEnv* env, jclass, jobject jflags, jstring jname)
{
  try {
    const CLFlags* flags = unembed_const<CLFlags>(env, jflags);
    string name(toCpp(env, jname));
    const CLFlag& flag = flags->getFlag(name);
    return embed_const_ref(env, &flag);
  } catch (const Exception& e) { toJava(env, e); };
}

