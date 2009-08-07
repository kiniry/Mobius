#include "JniUtils.h"

using namespace std;
using namespace Java_cvc3_JniUtils;
using namespace CVC3;

extern "C"
JNIEXPORT void JNICALL Java_cvc3_EmbeddedManager_jniDelete
(JNIEnv* env, jclass, jobject jobj)
{
  try {
    deleteEmbedded(env, jobj);
  } catch (const Exception& e) { toJava(env, e); };
}

