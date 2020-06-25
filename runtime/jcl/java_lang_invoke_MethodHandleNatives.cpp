/*******************************************************************************
 * Copyright (c) 2020, 2020 IBM Corp. and others
 *
 * This program and the accompanying materials are made available under
 * the terms of the Eclipse Public License 2.0 which accompanies this
 * distribution and is available at https://www.eclipse.org/legal/epl-2.0/
 * or the Apache License, Version 2.0 which accompanies this distribution and
 * is available at https://www.apache.org/licenses/LICENSE-2.0.
 *
 * This Source Code may also be made available under the following
 * Secondary Licenses when the conditions for such availability set
 * forth in the Eclipse Public License, v. 2.0 are satisfied: GNU
 * General Public License, version 2 with the GNU Classpath
 * Exception [1] and GNU General Public License, version 2 with the
 * OpenJDK Assembly Exception [2].
 *
 * [1] https://www.gnu.org/software/classpath/license.html
 * [2] http://openjdk.java.net/legal/assembly-exception.html
 *
 * SPDX-License-Identifier: EPL-2.0 OR Apache-2.0 OR GPL-2.0 WITH Classpath-exception-2.0 OR LicenseRef-GPL-2.0 WITH Assembly-exception
 *******************************************************************************/

#include "j9.h"
#include "jclprots.h"
#include "j9cp.h"
#include "j9protos.h"
#include "ut_j9jcl.h"
#include "j9port.h"
#include "jclglob.h"
#include "jcl_internal.h"
#include "util_api.h"

#include <string.h>
#include <assert.h>

#include "VMHelpers.hpp"

extern "C" {

#define MN_IS_METHOD		0x00010000
#define MN_IS_CONSTRUCTOR	0x00020000
#define MN_IS_FIELD			0x00040000
#define MN_IS_TYPE			0x00080000
#define MN_CALLER_SENSITIVE	0x00100000

#define MN_REFERENCE_KIND_SHIFT	24
#define MN_REFERENCE_KIND_MASK	(0x0F000000 >> MN_REFERENCE_KIND_SHIFT)

#define MN_SEARCH_SUPERCLASSES	0x00100000
#define MN_SEARCH_INTERFACES	0x00200000

typedef struct IteratorData {
	J9VMThread *currentThread;
	j9object_t fieldNameObj;
	J9ROMFieldShape *foundField;  /**< [out] field with name matching fieldNameObj */
	J9Class *declaringClass;  /**< [out] class that declares foundField */
} FindFieldData;


void
initImpl(J9VMThread *currentThread, j9object_t membernameObject, j9object_t refObject)
{
	J9JavaVM *vm = currentThread->javaVM;
	J9InternalVMFunctions *vmFuncs = vm->internalVMFunctions;

	J9Class* refClass = J9OBJECT_CLAZZ(currentThread, refObject);

	jint flags;
	jlong vmindex;
	j9object_t clazzObject, nameObject, typeObject, targetObject;

	j9object_t resolvedMethodObject = J9VMJAVALANGINVOKEMEMBERNAME_METHOD(currentThread, membernameObject);
	if (NULL == resolvedMethodObject) {
		// Create ResolvedMethodName Object
		resolvedMethodObject = vm->memoryManagerFunctions->J9AllocateObject(currentThread, J9VMJAVALANGINVOKERESOLVEDMETHODNAME(vm), J9_GC_ALLOCATE_OBJECT_INSTRUMENTABLE);
		J9VMJAVALANGINVOKEMEMBERNAME_SET_METHOD(currentThread, membernameObject, resolvedMethodObject);
	}

	if (refClass == J9VM_JAVALANGREFLECTFIELD_OR_NULL(vm)) {
		J9JNIFieldID *fieldID = vm->reflectFunctions.idFromFieldObject(currentThread, NULL, refObject);
		vmindex = (jlong)fieldID;

		flags = fieldID->field->modifiers & CFR_FIELD_ACCESS_MASK;
		flags |= MN_IS_FIELD;
		flags |= (J9_ARE_ANY_BITS_SET(flags, J9AccStatic) ? MH_REF_GETSTATIC : MH_REF_GETFIELD) << REFERENCE_KIND_SHIFT;
		J9UTF8 *name = J9ROMNAMEANDSIGNATURE_NAME(fieldID->field->nameAndSignature);
		J9UTF8 *signature = J9ROMNAMEANDSIGNATURE_SIGNATURE(fieldID->field->nameAndSignature);

		nameObject = vmThread->javaVM->memoryManagerFunctions->j9gc_createJavaLangString(currentThread, J9UTF8_DATA(name), (U_32)J9UTF8_LENGTH(name), J9_STR_INTERN);
		typeObject = vmThread->javaVM->memoryManagerFunctions->j9gc_createJavaLangString(currentThread, J9UTF8_DATA(signature), (U_32)J9UTF8_LENGTH(signature), J9_STR_INTERN);

		clazzObject = J9VM_J9CLASS_TO_HEAPCLASS(field->declaringClass);

		J9VMJAVALANGINVOKEMEMBERNAME_SET_NAME(currentThread, membernameObject, nameObject);
		J9VMJAVALANGINVOKEMEMBERNAME_SET_TYPE(currentThread, membernameObject, typeObject);
	} else if (refClass == J9VM_JAVALANGREFLECTMETHOD_OR_NULL(vm)) {
		J9JNIMethodID *methodID = vm->reflectFunctions.idFromMethodObject(currentThread, NULL, refObject);
		vmindex = (jlong)methodID;

		J9ROMMethod *romMethod = J9_ROM_METHOD_FROM_RAM_METHOD(methodID->method);

		flags = romMethod & CFR_METHOD_ACCESS_MASK;
		flags |= MN_IS_METHOD;
		if (J9_ARE_ANY_BITS_SET(methodID->vTableIndex, J9_JNI_MID_INTERFACE) {
			flags |= MH_REF_INVOKEINTERFACE << REFERENCE_KIND_SHIFT;
		} else {
			flags |= MH_REF_INVOKEVIRTUAL << REFERENCE_KIND_SHIFT;
		}

		clazzObject = J9VMJAVALANGREFLECTMETHOD_DECLARINGCLASS(currentThread, refObject);
	} else if (refClass == J9VM_JAVALANGREFLECTCONSTRUCTOR_OR_NULL(vm)) {
		J9JNIMethodID *methodID = vm->reflectFunctions.idFromConstructorObject(currentThread, NULL, refObject);
		vmindex = (jlong)methodID;

		J9ROMMethod *romMethod = J9_ROM_METHOD_FROM_RAM_METHOD(methodID->method);

		flags = romMethod & CFR_METHOD_ACCESS_MASK;
		flags |= MN_IS_CONSTRUCTOR | (MH_REF_INVOKESPECIAL << REFERENCE_KIND_SHIFT);

		clazzObject = J9VMJAVALANGREFLECTMETHOD_DECLARINGCLASS(currentThread, refObject);
	} else {
		vmFuncs->setCurrentExceptionUTF(currentThread, J9VMCONSTANTPOOL_JAVALANGILLEGALARGUMENTEXCEPTION, NULL);
	}

	if (!VM_VMHelpers::exceptionPending(currentThread)) {
		J9VMJAVALANGINVOKEMEMBERNAME_SET_FLAGS(currentThread, membernameObject, flags);
		J9VMJAVALANGINVOKEMEMBERNAME_SET_CLAZZ(currentThread, membernameObject, clazzObject);
		J9VMJAVALANGINVOKERESOLVEDMETHODNAME_SET_VMINDEX(currentThread, resolvedMethodObject, vmindex);
	}
}

/**
 * static native void init(MemberName self, Object ref);
 */
void JNICALL
Java_java_lang_invoke_MethodHandleNatives_init(JNIEnv *env, jclass clazz, jobject self, jobject ref)
{
	J9VMThread *currentThread = (J9VMThread*)env;
	J9JavaVM *vm = currentThread->javaVM;
	J9InternalVMFunctions *vmFuncs = vm->internalVMFunctions;
	vmFuncs->internalEnterVMFromJNI(currentThread);

	if (NULL == self || NULL == ref) {
		vmFuncs->setCurrentExceptionUTF(currentThread, J9VMCONSTANTPOOL_JAVALANGNULLPOINTEREXCEPTION, NULL);
	} else {
		j9object_t membernameObject = J9_JNI_UNWRAP_REFERENCE(self);
		j9object_t refObject = J9_JNI_UNWRAP_REFERENCE(ref);

		initImpl(currentThread, membernameObject, refObject);
	}
	vmFuncs->internalExitVMToJNI(currentThread);
}

/**
 * static native void expand(MemberName self);
 */
void JNICALL
Java_java_lang_invoke_MethodHandleNatives_expand(JNIEnv *env, jclass clazz, jobject self)
{
	J9VMThread *currentThread = (J9VMThread*)env;
	J9JavaVM *vm = currentThread->javaVM;
	J9InternalVMFunctions *vmFuncs = vm->internalVMFunctions;
	vmFuncs->internalEnterVMFromJNI(currentThread);

	if (NULL == self) {
		vmFuncs->setCurrentExceptionUTF(currentThread, J9VMCONSTANTPOOL_JAVALANGNULLPOINTEREXCEPTION, NULL);
	} else {
		j9object_t membernameObject = J9_JNI_UNWRAP_REFERENCE(self);
		j9object_t clazzObject = J9VMJAVALANGINVOKEMEMBERNAME_CLAZZ(currentThread, membernameObject);
		j9object_t nameObject = J9VMJAVALANGINVOKEMEMBERNAME_NAME(currentThread, membernameObject);
		j9object_t typeObject = J9VMJAVALANGINVOKEMEMBERNAME_TYPE(currentThread, membernameObject);
		j9object_t resolvedMethodObject = J9VMJAVALANGINVOKEMEMBERNAME_METHOD(currentThread, membernameObject);
		j9object_t targetObject, holderObject;
		jlong vmindex;

		if (resolvedMethodObject != NULL) {
			target = J9VMJAVALANGINVOKERESOLVEDMETHODNAME_VMTARGET(currentThread, resolvedMethodObject);
			holderObject = J9VMJAVALANGINVOKERESOLVEDMETHODNAME_VMHOLDER(currentThread, resolvedMethodObject);
			vmindex = J9VMJAVALANGINVOKERESOLVEDMETHODNAME_VMINDEX(currentThread, resolvedMethodObject);
		}
		jint flags = J9VMJAVALANGINVOKEMEMBERNAME_FLAGS(currentThread, membernameObject);

		if (J9_ARE_ANY_BITS_SET(flags, MN_IS_FIELD)) {
			if (clazzObject != NULL) {
				J9Class *clazz = J9VM_J9CLASS_FROM_HEAPCLASS(currentThread, clazzObject);

				J9JNIFieldID *field = (J9JNIFieldID*)vmindex; /* magically find this using vmindex */
				J9UTF8 *name = J9ROMFIELDSHAPE_NAME(field->field);
				J9UTF8 *signature = J9ROMFIELDSHAPE_SIGNATURE(field->field);

				if (nameObject == NULL) {
					j9object_t nameString = vmThread->javaVM->memoryManagerFunctions->j9gc_createJavaLangString(currentThread, J9UTF8_DATA(name), (U_32)J9UTF8_LENGTH(name), J9_STR_INTERN);
					J9VMJAVALANGINVOKEMEMBERNAME_SET_NAME(currentThread, membernameObject, nameString);
				}
				if (typeObject == NULL) {
					j9object_t signatureString = vmThread->javaVM->memoryManagerFunctions->j9gc_createJavaLangString(currentThread, J9UTF8_DATA(signature), (U_32)J9UTF8_LENGTH(signature), J9_STR_INTERN);
					J9VMJAVALANGINVOKEMEMBERNAME_SET_TYPE(currentThread, membernameObject, signatureString);
				}
			} else {
				vmFuncs->setCurrentExceptionUTF(currentThread, J9VMCONSTANTPOOL_JAVALANGILLEGALARGUMENTEXCEPTION, NULL);
			}
		} else if (J9_ARE_ANY_BITS_SET(flags, MN_IS_METHOD | MN_IS_CONSTRUCTOR)) {
			if (vmindex != NULL) {
				J9JNIMethodID *methodID = (J9JNIMethodID*)vmindex;
				J9ROMMethod *romMethod = J9_ROM_METHOD_FROM_RAM_METHOD(methodID->method);

				if (clazzObject == NULL) {
					j9object_t newClassObject = J9VM_J9CLASS_TO_HEAPCLASS(J9_CLASS_FROM_METHOD(methodID->method));
					J9VMJAVALANGINVOKEMEMBERNAME_SET_CLAZZ(currentThread, membernameObject, newClassObject);
				}
				if (nameObject == NULL) {
					J9UTF8 *name = J9ROMMETHOD_NAME(romMethod);
					j9object_t nameString = vmThread->javaVM->memoryManagerFunctions->j9gc_createJavaLangString(currentThread, J9UTF8_DATA(name), (U_32)J9UTF8_LENGTH(name), J9_STR_INTERN);
					J9VMJAVALANGINVOKEMEMBERNAME_SET_NAME(currentThread, membernameObject, nameString);
				}
				if (typeObject == NULL) {
					J9UTF8 *signature = J9ROMMETHOD_SIGNATURE(romMethod);
					j9object_t signatureString = vmThread->javaVM->memoryManagerFunctions->j9gc_createJavaLangString(currentThread, J9UTF8_DATA(signature), (U_32)J9UTF8_LENGTH(signature), J9_STR_INTERN);
					J9VMJAVALANGINVOKEMEMBERNAME_SET_TYPE(currentThread, membernameObject, signatureString);
				}
			} else {
				vmFuncs->setCurrentExceptionUTF(currentThread, J9VMCONSTANTPOOL_JAVALANGILLEGALARGUMENTEXCEPTION, NULL);
			}
		} else {
			vmFuncs->setCurrentExceptionUTF(currentThread, J9VMCONSTANTPOOL_JAVALANGINTERNALERROR, NULL);
		}
	}
	vmFuncs->internalExitVMToJNI(currentThread);
}

/**
 * static native MemberName resolve(MemberName self, Class<?> caller,
 *      boolean speculativeResolve) throws LinkageError, ClassNotFoundException;
 */
void JNICALL
Java_java_lang_invoke_MethodHandleNatives_resolve(JNIEnv *env, jclass clazz, jobject self, jclass caller, jboolean speculativeResolve)
{
	// TODO
}

/**
 * static native int getMembers(Class<?> defc, String matchName, String matchSig,
 *      int matchFlags, Class<?> caller, int skip, MemberName[] results);
 */
jint JNICALL
Java_java_lang_invoke_MethodHandleNatives_getMembers(JNIEnv *env, jclass clazz, jclass defc, jstring matchName, jstring matchSig, jint matchFlags, jclass caller, jint skip, jobjectArray results)
{
	J9VMThread *currentThread = (J9VMThread*)env;
	J9JavaVM *vm = currentThread->javaVM;
	J9InternalVMFunctions *vmFuncs = vm->internalVMFunctions;
	vmFuncs->internalEnterVMFromJNI(currentThread);
	jint result = 0;

	if (NULL == defc || NULL == results) {
		result = -1;
	} else {
		j9object_t defcObject = J9_JNI_UNWRAP_REFERENCE(defc);
		j9array_t resultsArray = (j9array_t)J9_JNI_UNWRAP_REFERENCE(results);
		j9object_t nameObject = ((NULL == matchName) ? NULL : J9_JNI_UNWRAP_REFERENCE(matchName);
		j9object_t sigObject = ((NULL == matchSig) ? NULL : J9_JNI_UNWRAP_REFERENCE(matchSig);
		j9object_t callerObject = ((NULL == caller) ? NULL : J9_JNI_UNWRAP_REFERENCE(caller);

		if (NULL == defcObject) {
			result = -1;
		} else if (!((NULL != matchName && NULL == nameObject) || (NULL != matchSig && NULL == sigObject))) {
			J9Class *defClass = J9VM_J9CLASS_FROM_HEAPCLASS(currentThread, defcObject);
			UDATA length = J9INDEXABLEOBJECT_SIZE(currentThread, resultsArray);
			UDATA index = 0;
			if (!((NULL != nameObject) && (0 == J9VMJAVALANGSTRING_LENGTH(currentThread, nameObject)))) {
				if (J9ROMCLASS_IS_INTERFACE(defClass->romClass) {
					result = -1;
				} else {
					if (J9_ARE_ANY_BITS_SET(matchFlags, MN_IS_FIELD)) {
						J9ROMFieldShape *romField = NULL;
						J9ROMFieldWalkState walkState;

						UDATA classDepth = 0;
						if (J9_ARE_ANY_BITS_SET(matchFlags, MN_SEARCH_SUPERCLASSES)) {
							/* walk superclasses */
							J9CLASS_DEPTH(defClass);
						}
						J9Class *currentClass = defClass;

						while (NULL != currentClass) {
							/* walk currentClass */
							memset(&walkState, 0, sizeof(walkState));
							romField = romFieldsStartDo(currentClass->romClass, &walkState);

							while (NULL != romField) {
								J9UTF8 *nameUTF = J9ROMFIELDSHAPE_NAME(romField);
								J9UTF8 *signatureUTF = J9ROMFIELDSHAPE_SIGNATURE(romField);
								if (((NULL == nameObject) || (0 != vmFuncs->compareStringToUTF8(currentThread, nameObject, FALSE, J9UTF8_DATA(nameUTF), J9UTF8_LENGTH(nameUTF))))
								&& ((NULL != sigObject) && (0 == vmFuncs->compareStringToUTF8(currentThread, sigObject, FALSE, J9UTF8_DATA(signatureUTF), J9UTF8_LENGTH(signatureUTF))))
								) {
									if (skip > 0) {
										skip -=1;
									} else {
										if (index < length) {
											j9object_t memberName = J9JAVAARRAYOFOBJECT_LOAD(currentThread, resultsArray, index);
											if (NULL == memberName) {
												vmFuncs->internalExitVMToJNI(currentThread);
												return -99;
											}
											UDATA inconsistentData = 0;
											j9object_t fieldObj = NULL;
											if (romField->modifiers & J9AccStatic) {
												/* create static field object */
												fieldObj = createStaticFieldObject(romField, currentClass, defClass, currentThread, &inconsistentData);
											} else {
												/* create instance field object */
												fieldObj = createInstanceFieldObject(romField, currentClass, defClass, currentThread, &inconsistentData);
											}
											initImpl(currentThread, memberName, fieldObj);
										}
									}
									result += 1;
								}
								romField = romFieldsNextDo(&walkState);
							}

							/* get the superclass */
							if (classDepth >= 1) {
								classDepth -= 1;
								currentClass = defClass->superclasses[classDepth];
							} else {
								currentClass = NULL;
							}
						}

						/* walk interfaces */
						if (J9_ARE_ANY_BITS_SET(matchFlags, MN_SEARCH_INTERFACES)) {
							J9ITable *currentITable = (J9ITable *)defClass->iTable;

							while (NULL != currentITable) {
								memset(&walkState, 0, sizeof(walkState));
								romField = romFieldsStartDo(currentITable->interfaceClass->romClass, &walkState);
								while (NULL != romField) {
									J9UTF8 *nameUTF = J9ROMFIELDSHAPE_NAME(romField);
									J9UTF8 *signatureUTF = J9ROMFIELDSHAPE_SIGNATURE(romField);
									if (((NULL == nameObject) || (0 != vmFuncs->compareStringToUTF8(currentThread, nameObject, FALSE, J9UTF8_DATA(nameUTF), J9UTF8_LENGTH(nameUTF))))
									&& ((NULL != sigObject) && (0 == vmFuncs->compareStringToUTF8(currentThread, sigObject, FALSE, J9UTF8_DATA(signatureUTF), J9UTF8_LENGTH(signatureUTF))))
									) {
										if (skip > 0) {
											skip -=1;
										} else {
											if (index < length) {
												j9object_t memberName = J9JAVAARRAYOFOBJECT_LOAD(currentThread, resultsArray, index);
												if (NULL == memberName) {
													vmFuncs->internalExitVMToJNI(currentThread);
													return -99;
												}
												UDATA inconsistentData = 0;
												j9object_t fieldObj = NULL;
												if (romField->modifiers & J9AccStatic) {
													/* create static field object */
													fieldObj = createStaticFieldObject(romField, currentClass, defClass, currentThread, &inconsistentData);
												} else {
													/* create instance field object */
													fieldObj = createInstanceFieldObject(romField, currentClass, defClass, currentThread, &inconsistentData);
												}
												initImpl(currentThread, memberName, fieldObj);
											}
										}
										result += 1;
									}
									romField = romFieldsNextDo(&walkState);
								}
								currentITable = currentITable->next;
							}
						}
					} else if (J9_ARE_ANY_BITS_SET(matchFlags, MN_IS_CONSTRUCTOR | MN_IS_METHOD)) {
						UDATA classDepth = 0;
						if (J9_ARE_ANY_BITS_SET(matchFlags, MN_SEARCH_SUPERCLASSES)) {
							/* walk superclasses */
							J9CLASS_DEPTH(defClass);
						}
						J9Class *currentClass = defClass;

						while (NULL != currentClass) {
							if (!J9ROMCLASS_IS_PRIMITIVE_OR_ARRAY(currentClass->romClass)) {
								J9Method *currentMethod = currentClass->ramMethods;
								J9Method *endOfMethods = currentMethod + currentClass->romClass->romMethodCount;
								while (currentMethod != endOfMethods) {
									J9ROMMethod *romMethod = J9_ROM_METHOD_FROM_RAM_METHOD(currentMethod);
									J9UTF8 *nameUTF = J9ROMMETHOD_SIGNATURE(romMethod);
									J9UTF8 *signatureUTF = J9ROMMETHOD_SIGNATURE(romMethod);
									if (((NULL == nameObject) || (0 != vmFuncs->compareStringToUTF8(currentThread, nameObject, FALSE, J9UTF8_DATA(nameUTF), J9UTF8_LENGTH(nameUTF))))
									&& ((NULL != sigObject) && (0 == vmFuncs->compareStringToUTF8(currentThread, sigObject, FALSE, J9UTF8_DATA(signatureUTF), J9UTF8_LENGTH(signatureUTF))))
									) {
										if (skip > 0) {
											skip -=1;
										} else {
											if (index < length) {
												j9object_t memberName = J9JAVAARRAYOFOBJECT_LOAD(currentThread, resultsArray, index);
												if (NULL == memberName) {
													vmFuncs->internalExitVMToJNI(currentThread);
													return -99;
												}
												j9object_t methodObj = NULL;
												if (J9_ARE_NO_BITS_SET(romMethod->modifiers, J9AccStatic)) && isSpecialMethod(romMethod) {
													/* create constructor object */
													methodObj = vm->reflectFunctions.createConstructorObject(currentMethod, currentClass, NULL, currentThread);
												} else {
													/* create method object */
													methodObj = vm->reflectFunctions.createMethodObject(currentMethod, currentClass, NULL, currentThread);
												}
												initImpl(currentThread, memberName, methodObj);
											}
										}
										result += 1;
									}
									currentMethod += 1;
								}
							}

							/* get the superclass */
							if (classDepth >= 1) {
								classDepth -= 1;
								currentClass = defClass->superclasses[classDepth];
							} else {
								currentClass = NULL;
							}
						}

						/* walk interfaces */
						if (J9_ARE_ANY_BITS_SET(matchFlags, MN_SEARCH_INTERFACES)) {
							J9ITable *currentITable = (J9ITable *)defClass->iTable;

							while (NULL != currentITable) {
								J9Class *currentClass = currentITable->interfaceClass;
								J9Method *currentMethod = currentClass->ramMethods;
								J9Method *endOfMethods = currentMethod + currentClass->romClass->romMethodCount;
								while (currentMethod != endOfMethods) {
									J9ROMMethod *romMethod = J9_ROM_METHOD_FROM_RAM_METHOD(currentMethod);
									J9UTF8 *nameUTF = J9ROMMETHOD_SIGNATURE(romMethod);
									J9UTF8 *signatureUTF = J9ROMMETHOD_SIGNATURE(romMethod);
									if (((NULL == nameObject) || (0 != vmFuncs->compareStringToUTF8(currentThread, nameObject, FALSE, J9UTF8_DATA(nameUTF), J9UTF8_LENGTH(nameUTF))))
									&& ((NULL != sigObject) && (0 == vmFuncs->compareStringToUTF8(currentThread, sigObject, FALSE, J9UTF8_DATA(signatureUTF), J9UTF8_LENGTH(signatureUTF))))
									) {
										if (skip > 0) {
											skip -=1;
										} else {
											if (index < length) {
												j9object_t memberName = J9JAVAARRAYOFOBJECT_LOAD(currentThread, resultsArray, index);
												if (NULL == memberName) {
													vmFuncs->internalExitVMToJNI(currentThread);
													return -99;
												}
												j9object_t methodObj = NULL;
												if (J9_ARE_NO_BITS_SET(romMethod->modifiers, J9AccStatic)) && isSpecialMethod(romMethod) {
													/* create constructor object */
													methodObj = vm->reflectFunctions.createConstructorObject(currentMethod, clazz, NULL, currentThread);
												} else {
													/* create method object */
													methodObj = vm->reflectFunctions.createMethodObject(currentMethod, clazz, NULL, currentThread);
												}
												initImpl(currentThread, memberName, methodObj);
											}
										}
										result += 1;
									}
									currentMethod += 1;
								}
								currentITable = currentITable->next;
							}
						}
					}
				}
			}
		}
	}
	vmFuncs->internalExitVMToJNI(currentThread);
	return result;
}

/**
 * static native long objectFieldOffset(MemberName self);  // e.g., returns vmindex
 */
jlong JNICALL
Java_java_lang_invoke_MethodHandleNatives_objectFieldOffset(JNIEnv *env, jclass clazz, jobject self)
{
	J9VMThread *currentThread = (J9VMThread*)env;
	J9JavaVM *vm = currentThread->javaVM;
	J9InternalVMFunctions *vmFuncs = vm->internalVMFunctions;
	vmFuncs->internalEnterVMFromJNI(currentThread);
	jlong result = 0;

	if (NULL == self) {
		vmFuncs->setCurrentExceptionUTF(currentThread, J9VMCONSTANTPOOL_JAVALANGNULLPOINTEREXCEPTION, NULL);
	} else {
		j9object_t membernameObject = J9_JNI_UNWRAP_REFERENCE(self);
		j9object_t clazzObject = J9VMJAVALANGINVOKEMEMBERNAME_CLAZZ(currentThread, membernameObject);

		if (NULL == clazzObject) {
			vmFuncs->setCurrentExceptionUTF(currentThread, J9VMCONSTANTPOOL_JAVALANGINTERNALERROR, NULL);
		} else {
			jint flags = J9VMJAVALANGINVOKEMEMBERNAME_FLAGS(currentThread, membernameObject);
			if (J9_ARE_ANY_BITS_SET(flags, MN_IS_FIELD) && J9_ARE_NO_BITS_SET(flags, J9AccStatic)) {
				j9object_t resolvedMethodObject = J9VMJAVALANGINVOKEMEMBERNAME_METHOD(currentThread, membernameObject);
				J9JNIFieldID *fieldID = (J9JNIFieldID*)J9VMJAVALANGINVOKERESOLVEDMETHODNAME_VMINDEX(currentThread, resolvedMethodObject);
				result = (jlong)fieldID->offset + J9VMTHREAD_OBJECT_HEADER_SIZE(currentThread);
			} else {
				vmFuncs->setCurrentExceptionUTF(currentThread, J9VMCONSTANTPOOL_JAVALANGINTERNALERROR, NULL);
			}
		}
	}
	vmFuncs->internalExitVMToJNI(currentThread);
	return result;
}

/**
 * static native long staticFieldOffset(MemberName self);  // e.g., returns vmindex
 */
jlong JNICALL
Java_java_lang_invoke_MethodHandleNatives_staticFieldOffset(JNIEnv *env, jclass clazz, jobject self)
{
	J9VMThread *currentThread = (J9VMThread*)env;
	J9JavaVM *vm = currentThread->javaVM;
	J9InternalVMFunctions *vmFuncs = vm->internalVMFunctions;
	vmFuncs->internalEnterVMFromJNI(currentThread);
	jlong result = 0;

	if (NULL == self) {
		vmFuncs->setCurrentExceptionUTF(currentThread, J9VMCONSTANTPOOL_JAVALANGNULLPOINTEREXCEPTION, NULL);
	} else {
		j9object_t membernameObject = J9_JNI_UNWRAP_REFERENCE(self);
		j9object_t clazzObject = J9VMJAVALANGINVOKEMEMBERNAME_CLAZZ(currentThread, membernameObject);

		if (NULL == clazzObject) {
			vmFuncs->setCurrentExceptionUTF(currentThread, J9VMCONSTANTPOOL_JAVALANGINTERNALERROR, NULL);
		} else {
			jint flags = J9VMJAVALANGINVOKEMEMBERNAME_FLAGS(currentThread, membernameObject);
			if (J9_ARE_ANY_BITS_SET(flags, MN_IS_FIELD & J9AccStatic)) {
				j9object_t resolvedMethodObject = J9VMJAVALANGINVOKEMEMBERNAME_METHOD(currentThread, membernameObject);
				J9JNIFieldID *fieldID = (J9JNIFieldID*)J9VMJAVALANGINVOKERESOLVEDMETHODNAME_VMINDEX(currentThread, resolvedMethodObject);
				J9ROMFieldShape *romField = fieldID->field;
				result = (jlong)fieldID->offset | J9_SUN_STATIC_FIELD_OFFSET_TAG;

				if (J9_ARE_ANY_BITS_SET(romField->modifiers, J9AccFinal)) {
					result |= J9_SUN_FINAL_FIELD_OFFSET_TAG;
				}
			} else {
				vmFuncs->setCurrentExceptionUTF(currentThread, J9VMCONSTANTPOOL_JAVALANGINTERNALERROR, NULL);
			}
		}
	}
	vmFuncs->internalExitVMToJNI(currentThread);
	return result;
}

/**
 * static native Object staticFieldBase(MemberName self);  // e.g., returns clazz
 */
jobject JNICALL
Java_java_lang_invoke_MethodHandleNatives_staticFieldBase(JNIEnv *env, jclass clazz, jobject self)
{
	J9VMThread *currentThread = (J9VMThread*)env;
	J9JavaVM *vm = currentThread->javaVM;
	J9InternalVMFunctions *vmFuncs = vm->internalVMFunctions;
	vmFuncs->internalEnterVMFromJNI(currentThread);
	jobject result = NULL;

	if (NULL == self) {
		vmFuncs->setCurrentExceptionUTF(currentThread, J9VMCONSTANTPOOL_JAVALANGNULLPOINTEREXCEPTION, NULL);
	} else {
		j9object_t membernameObject = J9_JNI_UNWRAP_REFERENCE(self);
		j9object_t clazzObject = J9VMJAVALANGINVOKEMEMBERNAME_CLAZZ(currentThread, membernameObject);

		if (NULL == clazzObject) {
			vmFuncs->setCurrentExceptionUTF(currentThread, J9VMCONSTANTPOOL_JAVALANGINTERNALERROR, NULL);
		} else {
			jint flags = J9VMJAVALANGINVOKEMEMBERNAME_FLAGS(currentThread, membernameObject);
			if (J9_ARE_ANY_BITS_SET(flags, MN_IS_FIELD & J9AccStatic)) {
				result = vmFuncs->j9jni_createLocalRef(env, clazzObject);
			} else {
				vmFuncs->setCurrentExceptionUTF(currentThread, J9VMCONSTANTPOOL_JAVALANGINTERNALERROR, NULL);
			}
		}
	}
	vmFuncs->internalExitVMToJNI(currentThread);
	return result;
}

/**
 * static native Object getMemberVMInfo(MemberName self);  // returns {vmindex,vmtarget}
 */
jobject JNICALL
Java_java_lang_invoke_MethodHandleNatives_getMemberVMInfo(JNIEnv *env, jclass clazz, jobject self)
{
	J9VMThread *currentThread = (J9VMThread*)env;
	J9JavaVM *vm = currentThread->javaVM;
	J9InternalVMFunctions *vmFuncs = vm->internalVMFunctions;
	jobject result = NULL;
	vmFuncs->internalEnterVMFromJNI(currentThread);

	if (NULL != self) {
		j9object_t membernameObject = J9_JNI_UNWRAP_REFERENCE(self);
		j9object_t clazzObject = J9VMJAVALANGINVOKEMEMBERNAME_CLAZZ(currentThread, membernameObject);
		jint flags = J9VMJAVALANGINVOKEMEMBERNAME_FLAGS(currentThread, membernameObject);

		j9object_t target;
		if (J9_ARE_ANY_BITS_SET(flags, MN_IS_FIELD)) {
			target = clazzObject;
		} else {
			target = membernameObject;
		}
		j9object_t resolvedMethodObject = J9VMJAVALANGINVOKEMEMBERNAME_METHOD(currentThread, membernameObject);
		jlong vmindex = J9VMJAVALANGINVOKERESOLVEDMETHODNAME_VMINDEX(currentThread, resolvedMethodObject);
		j9object_t box = vm->memoryManagerFunctions->J9AllocateObject(_currentThread, longWrapperClass, J9_GC_ALLOCATE_OBJECT_NON_INSTRUMENTABLE);
		J9VMJAVALANGLONG_SET_VALUE(currentThread, box, vmindex);

		J9Class *arrayClass = fetchArrayClass(currentThread, J9VMJAVALANGOBJECT(vm));
		j9object_t arrayObject = currentThread->javaVM->memoryManagerFunctions->J9AllocateIndexableObject(currentThread, arrayClass, 2, J9_GC_ALLOCATE_OBJECT_INSTRUMENTABLE);
		J9JAVAARRAYOFOBJECT_STORE(currentThread, arrayObject, 0, box);
		J9JAVAARRAYOFOBJECT_STORE(currentThread, arrayObject, 0, target);

		result = vmFuncs->j9jni_createLocalRef(env, clazzObject);
	}
	vmFuncs->internalExitVMToJNI(currentThread);
	return result;

}

/* CallSite support

static native void setCallSiteTargetNormal(CallSite site, MethodHandle target);
static native void setCallSiteTargetVolatile(CallSite site, MethodHandle target);

static native void copyOutBootstrapArguments(Class<?> caller, int[] indexInfo,
												int start, int end,
												Object[] buf, int pos,
												boolean resolve,
												Object ifNotAvailable);


private static native void clearCallSiteContext(CallSiteContext context);

private static native void registerNatives();

private static native int getNamedCon(int which, Object[] name);
*/
} /* extern "C" */
