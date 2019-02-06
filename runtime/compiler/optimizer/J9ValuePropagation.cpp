/*******************************************************************************
 * Copyright (c) 2000, 2019 IBM Corp. and others
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

#include "optimizer/J9ValuePropagation.hpp"
#include "optimizer/VPBCDConstraint.hpp"
#include "compile/Compilation.hpp"
#include "il/symbol/ParameterSymbol.hpp"
#include "il/Node.hpp"
#include "il/Node_inlines.hpp"
#include "il/Symbol.hpp"
#include "env/CHTable.hpp"
#include "env/ClassTableCriticalSection.hpp"
#include "env/PersistentCHTable.hpp"
#include "env/VMJ9.h"
#include "optimizer/Optimization_inlines.hpp"
#include "env/j9method.h"
#include "env/TRMemory.hpp"
#include "il/Block.hpp"
#include "infra/Cfg.hpp"
#include "compile/VirtualGuard.hpp"
#include "env/CompilerEnv.hpp"
#include "optimizer/TransformUtil.hpp"
#include "il/symbol/StaticSymbol.hpp"
#include "env/VMAccessCriticalSection.hpp"
#include "runtime/RuntimeAssumptions.hpp"
#include "env/J9JitMemory.hpp"
#include "optimizer/HCRGuardAnalysis.hpp"
#include "env/JSR292Methods.h"

#define OPT_DETAILS "O^O VALUE PROPAGATION: "

J9::ValuePropagation::ValuePropagation(TR::OptimizationManager *manager)
   : OMR::ValuePropagation(manager),
     _bcdSignConstraints(NULL),
     _callsToBeFoldedToIconst(trMemory())
   {
   }

// _bcdSignConstraints is an array organized first by TR::DataType and then by TR_BCDSignConstraint
// getBCDSignConstraints returns a pointer to the first entry for a given dt.
// e.g.:
// 0 : TR::PackedDecimal - TR_Sign_Unknown       <- return when dt=TR::PackedDecimal
// 1 : TR::PackedDecimal - TR_Sign_Clean
// ...
// 6 : TR::PackedDecimal - TR_Sign_Minus_Clean
// 7 : TR::ZonedDecimal  - TR_Sign_Unknown       <- return when dt=TR::ZonedDecimal
// ...
// 13: TR::ZonedDecimal  - TR_Sign_Minus_Clean
// ...
// ...
// xx: TR::LastBCDType   - TR_Sign_Unknown       <- return when dt=TR::LastBCDType
//  ...
// zz: TR::LastBCDType   - TR_Sign_Minus_Clean
//
TR::VP_BCDSign **J9::ValuePropagation::getBCDSignConstraints(TR::DataType dt)
   {
   TR_ASSERT(dt.isBCD(),"dt %s not a bcd type\n",dt.toString());
   if (_bcdSignConstraints == NULL)
      {
      size_t size = TR::DataType::numBCDTypes() * TR_Sign_Num_Types * sizeof(TR::VP_BCDSign*);
      _bcdSignConstraints = (TR::VP_BCDSign**)trMemory()->allocateStackMemory(size);
      memset(_bcdSignConstraints, 0, size);
//    traceMsg(comp(),"create _bcdSignConstraints %p of size %d (numBCDTypes %d * TR_Sign_Num_Types %d * sizeof(TR::VP_BCDSign*) %d)\n",
//       _bcdSignConstraints,size,TR::DataType::numBCDTypes(),TR_Sign_Num_Types,sizeof(TR::VP_BCDSign*));
      }
//   traceMsg(comp(),"lookup dt %d, ret %p + %d = %p\n",
//      dt,_bcdSignConstraints,(dt-TR::FirstBCDType)*TR_Sign_Num_Types,_bcdSignConstraints + (dt-TR::FirstBCDType)*TR_Sign_Num_Types);
   return _bcdSignConstraints + (dt-TR::FirstBCDType)*TR_Sign_Num_Types;
   }

/**
 * \brief
 *    Generate a diamond for a call with the guard being an HCR guard, the fast path being an iconst node
 *    and the slow path being the original call.
 *
 * \parm callTree
 *    Tree of call to be folded.
 *
 * \parm result
 *    The constant used to replace the call in the fast path.
 */
void
J9::ValuePropagation::transformCallToIconstWithHCRGuard(TR::TreeTop *callTree, int32_t result)
   {
   static const char *disableHCRGuards = feGetEnv("TR_DisableHCRGuards");
   TR_ASSERT(!disableHCRGuards && comp()->getHCRMode() != TR::none, "foldCallToConstantInHCRMode should be called in HCR mode");

   TR::Node * callNode = callTree->getNode()->getFirstChild();
   TR_ASSERT(callNode->getSymbol()->isResolvedMethod(), "Expecting resolved call in transformCallToIconstWithHCRGuard");

   TR::ResolvedMethodSymbol *calleeSymbol = callNode->getSymbol()->castToResolvedMethodSymbol();

   // Add the call to inlining table
   if (!comp()->incInlineDepth(calleeSymbol, callNode->getByteCodeInfo(), callNode->getSymbolReference()->getCPIndex(), callNode->getSymbolReference(), !callNode->getOpCode().isCallIndirect(), 0))
      {
      if (trace())
         traceMsg(comp(), "Cannot inline call %p, quit transforming it into a constant\n", callNode);
      return;
      }
   // With the method added to the inlining table, getCurrentInlinedSiteIndex() will return the desired inlined site index
   int16_t calleeIndex = comp()->getCurrentInlinedSiteIndex();
   TR::Node *compareNode= TR_VirtualGuard::createHCRGuard(comp(), calleeIndex, callNode, NULL, calleeSymbol, calleeSymbol->getResolvedMethod()->classOfMethod());

   // ifTree is a duplicate allTree
   J9::TransformUtil::createTempsForCall(this, callTree);
   TR::TreeTop *compareTree = TR::TreeTop::create(comp(), compareNode);
   TR::TreeTop *ifTree = TR::TreeTop::create(comp(),callTree->getNode()->duplicateTree());
   ifTree->getNode()->getFirstChild()->setIsTheVirtualCallNodeForAGuardedInlinedCall();
   // resultNode is the inlined node, should have the correct callee index
   // Pass compareNode as the originatingByteCodeNode so that the resultNode has the correct callee index
   TR::Node *resultNode = TR::Node::iconst(compareNode, result);
   TR::TreeTop *elseTree = TR::TreeTop::create(comp(), TR::Node::create(callNode, TR::treetop, 1, resultNode));
   J9::TransformUtil::createDiamondForCall(this, callTree, compareTree, ifTree, elseTree, false /*changeBlockExtensions*/, true /*markCold*/);
   comp()->decInlineDepth();
   }

/**
 * \brief
 *    Return a pointer to the object reference if applicable.
 *
 * \parm constraint
 *    The VP constraint from which an object location is asked for.
 *
 * \return
 *    Return a pointer to the object reference if the constraint is a constString or a known object constraint,
 *    otherwise return NULL.
 */
uintptrj_t*
J9::ValuePropagation::getObjectLocationFromConstraint(TR::VPConstraint *constraint)
   {
    uintptrj_t* objectLocation = NULL;
    if (constraint->isConstString())
       {
       // VPConstString constraint, the symref is resolved for VPConstString constraint
       objectLocation = (uintptrj_t*)constraint->getClassType()->asConstString()->getSymRef()->getSymbol()->castToStaticSymbol()->getStaticAddress();
       }
    else if (constraint->getKnownObject())
       {
       TR::KnownObjectTable::Index index = constraint->getKnownObject()->getIndex();
       if (index != TR::KnownObjectTable::UNKNOWN)
          objectLocation = comp()->getKnownObjectTable()->getPointerLocation(index);
       }
   return objectLocation;
   }

/**
 * \brief
 *    Fold a call to the given result in place or add it to the worklist of delayed transformations.
 *
 * \parm callTree
 *    The tree containing the call to be folded.
 *
 * \parm result
 *    The constant used to replace the call.
 *
 * \parm isGlobal
 *    If true, add global constraint to the new node if call is folded in place.
 *
 * \parm inPlace
 *   If true, fold the call in place. Otherwise in delayed transformations.
 */
void
J9::ValuePropagation::transformCallToIconstInPlaceOrInDelayedTransformations(TR::TreeTop* callTree, int32_t result, bool isGlobal, bool inPlace)
   {
    TR::Node * callNode = callTree->getNode()->getFirstChild();
    TR_Method * calledMethod = callNode->getSymbol()->castToMethodSymbol()->getMethod();
    const char *signature = calledMethod->signature(comp()->trMemory(), stackAlloc);
    if (inPlace)
       {
       if (trace())
          traceMsg(comp(), "Fold the call to %s on node %p to %d\n", signature, callNode, result);
       replaceByConstant(callNode, TR::VPIntConst::create(this, result), isGlobal);
       }
    else
       {
       if (trace())
          traceMsg(comp(), "The call to %s on node %p will be folded to %d in delayed transformations\n", signature, callNode, result);
       _callsToBeFoldedToIconst.add(new (trStackMemory()) TreeIntResultPair(callTree, result));
       }
  }

/**
 * \brief
 *    Check if the given constraint is for a java/lang/String object.
 *
 * \parm constraint
 *    The VP constraint to be checked.
 *
 * \return
 *    Return TR_yes if the constraint is for a java/lang/String object,
 *    TR_no if it is not, TR_maybe if it is unclear.
 */
TR_YesNoMaybe
J9::ValuePropagation::isStringObject(TR::VPConstraint *constraint)
   {
   if (constraint
       && constraint->getClassType()
       && constraint->getClass()
       && constraint->getClassType()->asResolvedClass())
      {
      if (constraint->isClassObject() == TR_yes)
         return TR_no;
      if (constraint->isClassObject() == TR_no)
         {
         TR_OpaqueClassBlock* objectClass = constraint->getClass();
         if (constraint->getClassType()->asFixedClass())
            return comp()->fej9()->isString(objectClass) ? TR_yes : TR_no;
         else
            return comp()->fej9()->typeReferenceStringObject(objectClass);
         }
      }
   return TR_maybe;
   }

/**
 * \brief
 *    Check if the given constraint indicates a known java/lang/String object.
 *
 * \parm constraint
 *    The VP constraint to be checked.
 *
 * \return
 *    Return true if the constraint indicates a known java/lang/String object, false otherwise.
 */
bool
J9::ValuePropagation::isKnownStringObject(TR::VPConstraint *constraint)
   {
   return isStringObject(constraint) == TR_yes
          && constraint->isNonNullObject()
          && (constraint->isConstString() || constraint->getKnownObject());
   }

static TR::TreeTop*
findInvokeExactForAsTypeCall(TR::TreeTop* asTypeTree)
   {
   TR::TreeTop* lastTT = asTypeTree->getEnclosingBlock()->getExit();
   TR::Node* asTypeCall = asTypeTree->getNode()->getFirstChild();
   for (TR::TreeTop* tt = asTypeTree->getNextTreeTop(); tt != lastTT; tt = tt->getNextTreeTop())
      {
      if (tt->getNode()->getNumChildren() == 1)
         {
         TR::Node* node = tt->getNode()->getFirstChild();
         if (node && node->getOpCode().isCallIndirect()  && !node->getSymbol()->castToMethodSymbol()->isHelper())
            {
            TR::ResolvedMethodSymbol* symbol = node->getSymbol()->getResolvedMethodSymbol();
            TR::RecognizedMethod rm = symbol->getRecognizedMethod();
            if (rm == TR::java_lang_invoke_MethodHandle_invokeExact
                && node->getFirstArgument() == asTypeCall)
               return tt;
            }
         }
      }

   return NULL;
   }

// Check if one type can be converted to another type
static TR_YesNoMaybe
typesAreConvertible(TR::Compilation* comp, TR_J9VMBase* fej9, TR_OpaqueClassBlock* fromClazz, TR_OpaqueClassBlock* toClazz)
   {
   int32_t fromClassNameLength;
   char* fromClassName = fej9->getClassNameChars(fromClazz, fromClassNameLength);

   int32_t toClassNameLength;
   char* toClassName = fej9->getClassNameChars(toClazz, toClassNameLength);

   traceMsg(comp, "converting from %.*s to %.*s\n", fromClassNameLength, fromClassName, toClassNameLength, toClassName);

   if (fromClazz == toClazz)
      return TR_yes;

   bool fromIsPrimitive = fej9->isPrimitiveClass(fromClazz);
   bool toIsPrimitive = fej9->isPrimitiveClass(toClazz);

   if (fromIsPrimitive && toIsPrimitive)
      {
      if (fej9->isWideningPrimitiveConversion(fromClazz, toClazz))
         return TR_yes;
      else
         return TR_no;
      }

   if (toIsPrimitive)
      {
      // check if is unboxing + widening primitive conversion
      // fromClazz has to be reference type { Object, Number, Boolean, Byte, Integer, etc }
      // If fromClazz is a super class of the wrapper class of toClazz, types may be convertible
      TR_OpaqueClassBlock* toWrapperClazz = fej9->getWrapperClassOfPrimitive(toClazz);
      // liqun: what's the meaning of yes no maybe here
      // more like if we can apply certain conversion at compile time, maybe the function name should
      // be adjusted?
      if (!toWrapperClazz)
         return TR_no;

      if (fromClazz == toWrapperClazz)
         return TR_yes;

      TR_YesNoMaybe result = fej9->isInstanceOf(toWrapperClazz, fromClazz, true, false);
      if (result != TR_no)
         return result;

      // check if is widening primitive conversion
      if (fej9->isWrapperClass(fromClazz))
         {
         TR_OpaqueClassBlock* fromUnwrappedClazz =  fej9->getPrimitiveClassOfWrapperClass(fromClazz);
         if (fej9->isWideningPrimitiveConversion(fromUnwrappedClazz, toClazz))
            return TR_yes;
         }

      return TR_no;
      }

   // toClazz is reference type
   // check if is boxing conversion, widening reference conversion
   // toClazz has to be the wrapper type of fromClazz, Object or Number
   if (fromIsPrimitive)
      {
      TR_OpaqueClassBlock* fromWrapperClazz = fej9->getWrapperClassOfPrimitive(fromClazz);
      if (!fromWrapperClazz)
         return TR_no;

      if (toClazz == fromWrapperClazz)
         return TR_yes;

      return fej9->isInstanceOf(fromWrapperClazz, toClazz, true, true);
      }

   return TR_maybe;

   if (fej9->isJavaLangVoid(fromClazz))
      return TR_yes;

   // Both classes are reference type
   return fej9->isInstanceOf(fromClazz, toClazz, true, true);
   }

static TR_YesNoMaybe
returnTypesAreConvertibleBetweenMethodTypes(TR::Compilation* comp, TR_J9VMBase* fej9, uintptrj_t fromMethodType, uintptrj_t toMethodType)
   {
   TR_ASSERT(fej9->haveAccess(), "returnTypesAreConvertibleBetweenMethodTypes requires VM access");
   TR_OpaqueClassBlock* fromClazz = fej9->getClassFromJavaLangClass(fej9->methodType_returnType(fromMethodType));
   TR_OpaqueClassBlock* toClazz = fej9->getClassFromJavaLangClass(fej9->methodType_returnType(toMethodType));

   // Converting to void, just ignore the return result
   // Converting from void, null for Object, constant 0 for primitive
   if (fej9->isVoid(fromClazz) || fej9->isVoid(toClazz))
      return TR_yes;

   return typesAreConvertible(comp, fej9, fromClazz, toClazz);
   }

static TR_YesNoMaybe
argumentsAreConvertibleBetweenMethodTypes(TR::Compilation* comp, TR_J9VMBase* fej9, uintptrj_t fromMethodType, uintptrj_t toMethodType)
   {
   TR_ASSERT(fej9->haveAccess(), "argumentsAreConvertibleBetweenMethodTypes requires VM access");
   uintptrj_t fromArgArray = fej9->methodType_arguments(fromMethodType);
   uintptrj_t toArgArray = fej9->methodType_arguments(toMethodType);

   intptrj_t fromArgNum = fej9->getArrayLengthInElements(fromArgArray);
   intptrj_t toArgNum = fej9->getArrayLengthInElements(toArgArray);

   if (fromArgNum != toArgNum)
      return TR_no;

   TR_YesNoMaybe result = TR_yes;

   for (int i=0; i< fromArgNum; i++)
      {
      TR_OpaqueClassBlock* fromArgClazz = fej9->getClassFromJavaLangClass(fej9->getReferenceElement(fromArgArray, i));
      TR_OpaqueClassBlock* toArgClazz = fej9->getClassFromJavaLangClass(fej9->getReferenceElement(toArgArray, i));
      TR_YesNoMaybe tmpResult = typesAreConvertible(comp, fej9, fromArgClazz, toArgClazz);
      if (tmpResult == TR_no)
         return TR_no;
      else if (tmpResult == TR_maybe)
         result = TR_maybe;
      }

   return result;
   }

static TR_YesNoMaybe
canInvokeMethodHandleWithType(TR::Compilation* comp, TR_J9VMBase* fej9, uintptrj_t methodHandle, uintptrj_t newType)
   {
   TR_ASSERT(fej9->haveAccess(), "canInvokeMethodHandleWithType requires VM access");
   uintptrj_t mhType = fej9->methodHandle_type(methodHandle);

   if (mhType == newType)
      return TR_yes;

   TR_YesNoMaybe returnTypesConvertible = returnTypesAreConvertibleBetweenMethodTypes(comp, fej9, mhType, newType);
   TR_YesNoMaybe argumentsConvertible = argumentsAreConvertibleBetweenMethodTypes(comp, fej9, newType, mhType);

   if (returnTypesConvertible == TR_no
       || argumentsConvertible == TR_no)
      return TR_no;
   else if (returnTypesConvertible == TR_yes
            && argumentsConvertible == TR_yes)
      return TR_yes;

   return TR_maybe;
   }

static TR::SymbolReference*
methodSymRefForBoxingConversion(TR::Compilation* comp, TR_OpaqueClassBlock* fromClazz)
   {
   TR_J9VMBase* fej9 = comp->fej9();
   TR_ASSERT(fej9->isPrimitiveClass(fromClazz), "fromClazz 0x%p is not a primitive class", fromClazz);
   // Find the method of the valueOf(X)Ljava/lang/Y;
   TR_OpaqueClassBlock* fromWrapperClass = fej9->getWrapperClassOfPrimitive(fromClazz);
   int32_t fromWrapperClassNameLength;
   char* fromWrapperClassName = fej9->getClassNameChars(fromWrapperClass, fromWrapperClassNameLength);
   J9Type fromJ9Type = fej9->j9TypeForClass(fromClazz);
   char* fromClassSig = fej9->signatureForPrimitive(fromJ9Type);
   char valueOfMethodSig[40];
   sprintf(valueOfMethodSig, "(%s)L%.*s;", fromClassSig, fromWrapperClassNameLength, fromWrapperClassName);
   TR_OpaqueMethodBlock *valueOf = fej9->getMethodFromClass(fromWrapperClass, "valueOf", valueOfMethodSig, NULL /*pass NULL to skip visibility check*/);

   TR_ASSERT(valueOf, "Can't find boxing methods");

   TR::SymbolReference *valueOfSymRef = comp->getSymRefTab()->findOrCreateMethodSymbol(JITTED_METHOD_INDEX,
                                                                                       -1,
                                                                                       fej9->createResolvedMethod(comp->trMemory(), valueOf),
                                                                                       TR::MethodSymbol::Static);

   return valueOfSymRef;
   }

// Unboxing and widening primitive conversion
static TR::SymbolReference*
methodSymRefForUnboxingConversion(TR::Compilation* comp, TR_OpaqueClassBlock* fromClazz, TR_OpaqueClassBlock* toClazz)
   {
   TR_J9VMBase* fej9 = comp->fej9();
   char methodName[30], methodSignature[50];
   J9Type toJ9Type = fej9->j9TypeForClass(toClazz);
   char* targetType = fej9->signatureForPrimitive(toJ9Type);
   TR_OpaqueClassBlock* javaLangNumber = fej9->getSystemClassFromClassName("java/lang/Number", strlen("java/lang/Number"));
   if (javaLangNumber && fej9->isInstanceOf(fromClazz, javaLangNumber, false, true) == TR_yes)
      {
      sprintf(methodName, "number2%s", targetType);
      sprintf(methodSignature, "(Ljava/lang/Number;)%s", targetType);
      }
   else
      {
      sprintf(methodName, "object2%s", targetType);
      sprintf(methodSignature, "(Ljava/lang/Object;)%s", targetType);
      }
   TR::SymbolReference *methodSymRef = comp->getSymRefTab()->methodSymRefFromName(comp->getMethodSymbol(),
                                                                                  "java/lang/invoke/ConvertHandle$FilterHelpers",
                                                                                  methodName,
                                                                                  methodSignature,
                                                                                  TR::MethodSymbol::Static);
   TR_ASSERT(methodSymRef, "Can't find conversion methods");
   return methodSymRef;
   }

static TR::Node*
boxingOrUnboxingConversion(TR::Compilation* comp, TR::Node* originatingByteCodeNode, TR::Node* fromNode, TR_OpaqueClassBlock* fromClazz, TR_OpaqueClassBlock* toClazz)
   {
   TR::DataType fromType = comp->fej9()->classDataType(fromClazz);
   TR::DataType toType = comp->fej9()->classDataType(toClazz);
   TR::SymbolReference *methodSymRef = NULL;
   if (toType == TR::Address/*is boxing conversion*/)
      methodSymRef = methodSymRefForBoxingConversion(comp, fromClazz);
   else
      methodSymRef = methodSymRefForUnboxingConversion(comp, fromClazz, toClazz);

   TR::Node* convertedNode = TR::Node::createWithSymRef(originatingByteCodeNode,
                                                        methodSymRef->getSymbol()->castToMethodSymbol()->getMethod()->directCallOpCode(),
                                                        1,
                                                        fromNode,
                                                        methodSymRef);
   return convertedNode;
   }

static TR::TreeTop*
createCheckCast(TR::Compilation* comp, TR::Node* originatingByteCodeNode, TR::Node* objectNode, TR_OpaqueClassBlock* toClazz)
   {
   TR::Node *toClazzLoad = TR::Node::createWithSymRef(originatingByteCodeNode,
                                                      TR::loadaddr,
                                                      0,
                                                      comp->getSymRefTab()->findOrCreateClassSymbol(comp->getMethodSymbol(), -1, toClazz));
   TR::Node* checkcast = TR::Node::create(originatingByteCodeNode, TR::checkcast, 2, objectNode, toClazzLoad);
   checkcast->setSymbolReference(comp->getSymRefTab()->findOrCreateCheckCastSymbolRef(comp->getMethodSymbol()));
   return TR::TreeTop::create(comp, checkcast);
   }

static void
traceConversion(TR::Compilation* comp, TR::Node* nodeToBeConverted, TR_OpaqueClassBlock* fromClazz, TR_OpaqueClassBlock* toClazz)
   {
   int32_t fromClazzNameLength;
   char* fromClazzName = comp->fej9()->getClassNameChars(fromClazz, fromClazzNameLength);
   int32_t toClazzNameLength;
   char* toClazzName = comp->fej9()->getClassNameChars(toClazz, toClazzNameLength);
   traceMsg(comp, "Trying to convert node %p n%dn from %.*s to %.*s\n", nodeToBeConverted, nodeToBeConverted->getGlobalIndex(), fromClazzNameLength, fromClazzName, toClazzNameLength, toClazzName);
   }

TR::TreeTop*
J9::ValuePropagation::convertReturnValue(TR::TreeTop* invokeExactTree, uintptrj_t fromMethodType, uintptrj_t toMethodType, bool isGlobal)
   {
   TR_J9VMBase* fej9 = comp()->fej9();
   TR_OpaqueClassBlock* fromClazz = fej9->getClassFromJavaLangClass(fej9->methodType_returnType(fromMethodType));
   TR_OpaqueClassBlock* toClazz = fej9->getClassFromJavaLangClass(fej9->methodType_returnType(toMethodType));
   TR::DataType fromType = fej9->classDataType(fromClazz);
   TR::DataType toType = fej9->classDataType(toClazz);
   TR::Node* invokeExactCall = invokeExactTree->getNode()->getFirstChild();
   bool enableTrace = trace();

   if (enableTrace)
      traceConversion(comp(), invokeExactCall, fromClazz, toClazz);

   if (fromClazz == toClazz
       || fej9->isVoid(toClazz)
       || (fromType == toType && fromType != TR::Address))
      {
      return invokeExactTree;
      }
   else if (fromType == TR::Address && toType == TR::Address)
      {
      if (fej9->isInstanceOf(fromClazz, toClazz, false, true) != TR_yes)
         {
         dumpOptDetails(comp(), "%sAdd checkcast on result of call node %p n%dn\n", OPT_DETAILS, invokeExactCall, invokeExactCall->getGlobalIndex());
         invokeExactTree->insertAfter(createCheckCast(comp(), invokeExactCall, invokeExactCall, toClazz));
         }

      return invokeExactTree;
      }
   else if (fej9->isVoid(fromClazz) && !isGlobal && !lastTimeThrough())
      {
      // The transformation will introduce node with constant value which will result in global constraint
      if (enableTrace)
         traceMsg(comp(), "Converting void to non-void and transformation is driven by local constraints, defer it to the last time through\n");
      return NULL;
      }

   // An explicit conversion is needed
   TR::Node* convertedResult = NULL;
   TR::Node* duplicatedCall = invokeExactCall->duplicateTree(false /*duplicateChildren*/);
   TR::TreeTop* duplicatedCallTree = TR::TreeTop::create(comp(), TR::Node::create(invokeExactCall, TR::treetop, 1, duplicatedCall));
   invokeExactTree->insertBefore(duplicatedCallTree);

   if (fej9->isWideningPrimitiveConversion(fromClazz, toClazz))
      {
      TR::ILOpCodes conversionOpCode = TR::ILOpCode::getProperConversion(fromType, toType, false);
      TR_ASSERT(conversionOpCode != TR::BadILOp, "Could not get proper conversion");
      convertedResult = TR::Node::create(invokeExactCall, conversionOpCode, 1, duplicatedCallTree->getNode()->getFirstChild());
      }
   else if (fej9->isVoid(fromClazz))
      {
      // Converting from void, null for Object, const 0 for primitive
      convertedResult = TR::Node::createConstZeroValue(invokeExactCall, toType);
      }
   else
      {
      // Boxing or unboxing conversion
      convertedResult =  boxingOrUnboxingConversion(comp(), invokeExactCall, duplicatedCallTree->getNode()->getFirstChild(), fromClazz, toClazz);
      TR::TreeTop::create(comp(), duplicatedCallTree /*precedingTreeTop*/, TR::Node::create(invokeExactCall, TR::treetop, 1, convertedResult));
      }

   dumpOptDetails(comp(), "%sTransform the original call node %p n%dn to a passthrough of converted result %p n%dn\n", OPT_DETAILS, invokeExactCall, invokeExactCall->getGlobalIndex(), convertedResult, convertedResult->getGlobalIndex());
   TR::TransformUtil::transformCallNodeToPassThrough(this, invokeExactCall, NULL, convertedResult);

   return duplicatedCallTree;
   }

// The two types have to be mutually convertable when calling this function
void
J9::ValuePropagation::convertArguments(TR::TreeTop* invokeExactTree, uintptrj_t fromMethodType, uintptrj_t toMethodType)
   {
   TR_J9VMBase* fej9 = comp()->fej9();
   TR::Node* invokeExactCall = invokeExactTree->getNode()->getFirstChild();
   uintptrj_t fromArgArray = fej9->methodType_arguments(fromMethodType);
   uintptrj_t toArgArray = fej9->methodType_arguments(toMethodType);
   int32_t receiverArgIndex = invokeExactCall->getFirstArgumentIndex();
   bool enableTrace = trace();

   // Go through all the arguments except receiver, insert trees to convert them to desired type
   for (int i = 1; i < invokeExactCall->getNumArguments(); i++)
      {
      TR::Node* child = invokeExactCall->getArgument(i);
      TR_OpaqueClassBlock* fromClazz = fej9->getClassFromJavaLangClass(fej9->getReferenceElement(fromArgArray, i-1));
      TR_OpaqueClassBlock* toClazz = fej9->getClassFromJavaLangClass(fej9->getReferenceElement(toArgArray, i-1));
      TR::DataType fromType = fej9->classDataType(fromClazz);
      TR::DataType toType = fej9->classDataType(toClazz);

      if (enableTrace)
         traceConversion(comp(), child, fromClazz, toClazz);

      if (fromClazz == toClazz
          || (fromType == toType && fromType != TR::Address))
         continue;
      else if (fromType == TR::Address && toType == TR::Address)
         {
         if (fej9->isInstanceOf(fromClazz, toClazz, false, true) != TR_yes)
            invokeExactTree->insertBefore(createCheckCast(comp(), invokeExactCall, child, toClazz));
         continue;
         }
      else
         {
         // Need to convert the child
         TR::Node* convertedChild = NULL;
         if (fej9->isWideningPrimitiveConversion(fromClazz, toClazz))
            {
            // widening primitive conversion
            TR::ILOpCodes conversionOpCode = TR::ILOpCode::getProperConversion(fromType, toType, false);
            convertedChild = TR::Node::create(invokeExactCall, conversionOpCode, 1, child);
            }
         else if (fromType == TR::Address || toType == TR::Address)
            {
            convertedChild =  boxingOrUnboxingConversion(comp(), invokeExactCall, child, fromClazz, toClazz);
            invokeExactTree->insertBefore(TR::TreeTop::create(comp(), TR::Node::create(invokeExactCall, TR::treetop, 1, convertedChild)));
            }

         // Replace child with the converted one
         invokeExactCall->setAndIncChild(i + receiverArgIndex, convertedChild);
         child->recursivelyDecReferenceCount();
         }
      }
   }

static void
devirtualizeInvokeExact(TR::Compilation* comp, TR::Node* node, uintptrj_t* mhLocation)
   {
   TR::SymbolReference* symRef = node->getSymbolReference();
   TR::ResolvedMethodSymbol* owningMethod = symRef->getOwningMethodSymbol(comp);
   TR_ResolvedMethod* resolvedMethod = comp->fej9()->createMethodHandleArchetypeSpecimen(comp->trMemory(), mhLocation, owningMethod->getResolvedMethod());
   TR::SymbolReference *specimenSymRef = comp->getSymRefTab()->findOrCreateMethodSymbol(owningMethod->getResolvedMethodIndex(), -1, resolvedMethod, TR::MethodSymbol::ComputedVirtual);
   dumpOptDetails(comp, "%sSubstituting more specific method symbol on %p: %s\n", OPT_DETAILS, node, specimenSymRef->getName(comp->getDebug()));
   TR::Node::recreateWithSymRef(node, specimenSymRef->getSymbol()->castToMethodSymbol()->getMethod()->indirectCallOpCode(), specimenSymRef);
   }

void
J9::ValuePropagation::processAsTypeCallNew(TR::Node* node)
   {
   const char *signature = node->getSymbol()->getResolvedMethodSymbol()->getResolvedMethod()->signature(comp()->trMemory(), stackAlloc);

   TR::ResolvedMethodSymbol* symbol = node->getSymbol()->getResolvedMethodSymbol();
   TR_ResolvedMethod* calledMethod = symbol->getResolvedMethod();
   const char* comSig = comp()->signature();
   const char* thisMethodSig = calledMethod->owningMethod()->signature(comp()->trMemory(), stackAlloc);
   const char* hotness = comp()->getHotnessName();
   const char* formatString = "asType/%s/%d/(%s %s)/(%s)";
   int32_t inlineDepth = comp()->getInlineDepth();

   TR_J9VMBase* fej9 = comp()->fej9();
   TR::Node* mh = node->getArgument(0);
   TR::Node* mt = node->getArgument(1);
   bool mhConstraintGlobal, mtConstraintGlobal;
   TR::VPConstraint* mhConstraint = getConstraint(mh, mhConstraintGlobal);
   TR::VPConstraint* mtConstraint = getConstraint(mt, mtConstraintGlobal);
   TR_OpaqueClassBlock* methodHandleClass = fej9->getSystemClassFromClassName(JSR292_MethodHandle, strlen(JSR292_MethodHandle));
   TR_OpaqueClassBlock* methodTypeClass = fej9->getSystemClassFromClassName(JSR292_MethodType, strlen(JSR292_MethodType));
   if (mhConstraint
       && mtConstraint
       && mhConstraint->getKnownObject()
       && mhConstraint->isNonNullObject()
       && mtConstraint->getKnownObject()
       && mtConstraint->isNonNullObject()
       && mhConstraint->getClass()
       && mtConstraint->getClass()
       && fej9->isInstanceOf(mhConstraint->getClass(), methodHandleClass, true, true) == TR_yes
       && fej9->isInstanceOf(mtConstraint->getClass(), methodTypeClass, true, true) == TR_yes)
      {
      uintptrj_t* mhLocation = getObjectLocationFromConstraint(mhConstraint);
      uintptrj_t* mtLocation = getObjectLocationFromConstraint(mtConstraint);

      TR::VMAccessCriticalSection asType(comp(),
                                                  TR::VMAccessCriticalSection::tryToAcquireVMAccess);
      if (!asType.hasVMAccess())
         return;
      uintptrj_t mhObject = fej9->getStaticReferenceFieldAtAddress((uintptrj_t)mhLocation);
      uintptrj_t mtInMh = fej9->methodHandle_type(mhObject);
      uintptrj_t mtObject = fej9->getStaticReferenceFieldAtAddress((uintptrj_t)mtLocation);

      if (trace())
         traceMsg(comp(), "mhLocation %p mtLocation %p mhObject %p mtObject %p\n", mhLocation, mtLocation, mhObject, mtObject);

      if (canInvokeMethodHandleWithType(comp(), fej9, mhObject, mtObject) == TR_no)
         {
         TR::DebugCounter::incStaticDebugCounter(comp(), TR::DebugCounter::debugCounterName(comp(), formatString, "cannotfold", inlineDepth, comSig, hotness, thisMethodSig));
         if (trace())
            traceMsg(comp(), "Callsite type and receiver MethodHandle type are not compatible, can't fold asType\n");
         return;
         }

      if (!performTransformation(comp(), "%sTransforming %s on node %p to a PassThrough with child %p\n", OPT_DETAILS, signature, node, mh))
         return;


      if (mtInMh != mtObject)
         {
         // Look for invokeExact call and transform the call
         TR::TreeTop* invokeExactTree = findInvokeExactForAsTypeCall(_curTree);
         if (!invokeExactTree)
            return;

         TR::TreeTop* newCallTree = convertReturnValue(invokeExactTree, mtInMh, mtObject, mhConstraintGlobal && mtConstraintGlobal);
         // Can't transform in this pass
         if (!newCallTree)
            return;

         convertArguments(newCallTree, mtObject, mtInMh);
         devirtualizeInvokeExact(comp(), newCallTree->getNode()->getFirstChild(), mhLocation);
         TR::DebugCounter::incStaticDebugCounter(comp(), TR::DebugCounter::debugCounterName(comp(), formatString, "foldwithconversion", inlineDepth, comSig, hotness, thisMethodSig));
         }
      else
         TR::DebugCounter::incStaticDebugCounter(comp(), TR::DebugCounter::debugCounterName(comp(), formatString, "fold", inlineDepth, comSig, hotness, thisMethodSig));

      // Transform asType call
      TR::TransformUtil::transformCallNodeToPassThrough(this, node, _curTree, mh);
      addBlockOrGlobalConstraint(node, mhConstraint, mhConstraintGlobal && mtConstraintGlobal);
      TR::DebugCounter::incStaticDebugCounter(comp(), TR::DebugCounter::debugCounterName(comp(), "constrainCall/(%s)", signature));

      comp()->dumpMethodTrees("liqun: after transform asType");
      return;
      }
   else
      TR::DebugCounter::incStaticDebugCounter(comp(), TR::DebugCounter::debugCounterName(comp(), formatString, "noconstraint", inlineDepth, comSig, hotness, thisMethodSig));
   }

void
J9::ValuePropagation::processAsTypeCall(TR::Node* node)
   {
   const char *signature = node->getSymbol()->getResolvedMethodSymbol()->getResolvedMethod()->signature(comp()->trMemory(), stackAlloc);

   TR::Node* mh = node->getArgument(0);
   TR::Node* mt = node->getArgument(1);
   bool mhConstraintGlobal, mtConstraintGlobal;
   TR::VPConstraint* mhConstraint = getConstraint(mh, mhConstraintGlobal);
   TR::VPConstraint* mtConstraint = getConstraint(mt, mtConstraintGlobal);
   J9VMThread* vmThread = comp()->fej9()->vmThread();
   TR_OpaqueClassBlock* methodHandleClass = J9JitMemory::convertClassPtrToClassOffset(J9VMJAVALANGINVOKEMETHODHANDLE(vmThread->javaVM));
   TR_OpaqueClassBlock* methodTypeClass = J9JitMemory::convertClassPtrToClassOffset(J9VMJAVALANGINVOKEMETHODTYPE(vmThread->javaVM));
   if (mhConstraint
       && mtConstraint
       && mhConstraint->getKnownObject()
       && mhConstraint->isNonNullObject()
       && mtConstraint->getKnownObject()
       && mtConstraint->isNonNullObject()
       && mhConstraint->getClass()
       && mtConstraint->getClass()
       && comp()->fej9()->isInstanceOf(mhConstraint->getClass(), methodHandleClass, true, true) == TR_yes
       && comp()->fej9()->isInstanceOf(mtConstraint->getClass(), methodTypeClass, true, true) == TR_yes)
      {
      uintptrj_t* mhLocation = getObjectLocationFromConstraint(mhConstraint);
      uintptrj_t* mtLocation = getObjectLocationFromConstraint(mtConstraint);
      uint32_t mtOffset = J9VMJAVALANGINVOKEMETHODHANDLE_TYPE_OFFSET(vmThread);

      TR::VMAccessCriticalSection asType(comp(),
                                                  TR::VMAccessCriticalSection::tryToAcquireVMAccess);
      if (!asType.hasVMAccess())
         return;
      uintptrj_t mhObject = comp()->fej9()->getStaticReferenceFieldAtAddress((uintptrj_t)mhLocation);
      uintptrj_t mtInMh = comp()->fej9()->getReferenceFieldAtAddress(mhObject + mtOffset);
      uintptrj_t mtObject = comp()->fej9()->getStaticReferenceFieldAtAddress((uintptrj_t)mtLocation);

      if (trace())
         traceMsg(comp(), "mhLocation %p mtLocation %p mhObject %p mtOffset %d mtInMh %p mtObject %p\n", mhLocation, mtLocation, mhObject, mtOffset, mtInMh, mtObject);

      // AOT doesn't relocate/validate objects, which is why this transformation is disabled under AOT
      if (mtInMh == mtObject)
         {
         if (!performTransformation(comp(), "%sTransforming %s on node %p to a PassThrough with child %p\n", OPT_DETAILS, signature, node, mh))
            return;

         TR::TransformUtil::transformCallNodeToPassThrough(this, node, _curTree, mh);
         addGlobalConstraint(node, mhConstraint);
         TR::DebugCounter::incStaticDebugCounter(comp(), TR::DebugCounter::debugCounterName(comp(), "constrainCall/(%s)", signature));
         return;
         }
      }
   }

void
J9::ValuePropagation::constrainRecognizedMethod(TR::Node *node)
   {
   // Only constrain resolved calls
   if (!node->getSymbol()->isResolvedMethod())
      return;

   const static char *disableVPFoldRecognizedMethod = feGetEnv("TR_disableVPFoldRecognizedMethod");
   if (disableVPFoldRecognizedMethod)
      return;
   TR::ResolvedMethodSymbol* symbol = node->getSymbol()->getResolvedMethodSymbol();
   TR::RecognizedMethod rm = symbol->getRecognizedMethod();
   if(rm == TR::unknownMethod)
      return;
   // Do not constraint a call node for a guarded inlined call
   if (node->isTheVirtualCallNodeForAGuardedInlinedCall())
      return;

   TR_ResolvedMethod* calledMethod = symbol->getResolvedMethod();
   const char *signature = calledMethod->signature(comp()->trMemory(), stackAlloc);

   static const char *disableHCRGuards = feGetEnv("TR_DisableHCRGuards");
   bool transformNonnativeMethodInPlace = disableHCRGuards || comp()->getHCRMode() == TR::none;

   if (trace())
      traceMsg(comp(), "Trying to compute the result of call to %s on node %p at compile time\n", signature, node);
   // This switch is used for transformations with AOT support
   switch (rm)
      {
      case TR::java_lang_Class_isInterface:
         {
         // Only constrain the call in the last run of vp to avoid adding the candidate twice if the call is inside a loop
         if (!lastTimeThrough())
            return;
         TR::Node *receiverChild = node->getLastChild();
         bool receiverChildGlobal;
         TR::VPConstraint *receiverChildConstraint = getConstraint(receiverChild, receiverChildGlobal);
         if (receiverChildConstraint
             && receiverChildConstraint->isJavaLangClassObject() == TR_yes
             && receiverChildConstraint->isNonNullObject()
             && receiverChildConstraint->getClassType()
             && receiverChildConstraint->getClassType()->asFixedClass())
            {
            int32_t isInterface = TR::Compiler->cls.isInterfaceClass(comp(), receiverChildConstraint->getClass());
            transformCallToIconstInPlaceOrInDelayedTransformations(_curTree, isInterface, receiverChildGlobal, transformNonnativeMethodInPlace);
            TR::DebugCounter::incStaticDebugCounter(comp(), TR::DebugCounter::debugCounterName(comp(), "constrainCall/(%s)", signature));
            return;
            }
         break;
         }
      case TR::java_lang_String_hashCode:
         {
         // Only constrain the call in the last run of vp to avoid adding the candidate twice if the call is inside a loop
         if (!lastTimeThrough())
            return;
         TR::Node *receiverChild = node->getLastChild();
         bool receiverChildGlobal;
         TR::VPConstraint *receiverChildConstraint= getConstraint(receiverChild, receiverChildGlobal);
         if (isKnownStringObject(receiverChildConstraint))
            {
            uintptrj_t* stringLocation = getObjectLocationFromConstraint(receiverChildConstraint);
            TR_ASSERT(stringLocation, "Expecting non null pointer to String object for constString or known String object");
            int32_t hashCode;
            bool success = comp()->fej9()->getStringHashCode(comp(), stringLocation, hashCode);
            if (!success)
               {
               if (trace())
                  traceMsg(comp(), "Cannot get access to the String object, quit transforming String.hashCode\n");
               break;
               }
            transformCallToIconstInPlaceOrInDelayedTransformations(_curTree, hashCode, receiverChildGlobal, transformNonnativeMethodInPlace);
            TR::DebugCounter::incStaticDebugCounter(comp(), TR::DebugCounter::debugCounterName(comp(), "constrainCall/(%s)", signature));
            return;
            }
         break;
         }
      case TR::java_lang_String_equals:
         {
         // Only constrain the call in the last run of vp to avoid adding the candidate twice if the call is inside a loop
         if (!lastTimeThrough())
            return;
         int32_t numChildren = node->getNumChildren();
         TR::Node *receiverChild = node->getChild(numChildren - 2);
         TR::Node *objectChild = node->getChild(numChildren - 1);
         bool receiverChildGlobal, objectChildGlobal;
         TR::VPConstraint *receiverChildConstraint = getConstraint(receiverChild, receiverChildGlobal);
         TR::VPConstraint *objectChildConstraint = getConstraint(objectChild, objectChildGlobal);
         if (isStringObject(receiverChildConstraint) == TR_yes
             && receiverChildConstraint->isNonNullObject()
             && objectChildConstraint)
            {
            // According to java doc, String.equals returns false when the argument object is null
            if (objectChildConstraint->isNullObject())
               {
               transformCallToIconstInPlaceOrInDelayedTransformations(_curTree, 0, receiverChildGlobal && objectChildGlobal, transformNonnativeMethodInPlace);
               TR::DebugCounter::incStaticDebugCounter(comp(), TR::DebugCounter::debugCounterName(comp(), "constrainCall/(%s)", signature));
               return;
               }

            TR_YesNoMaybe isObjectString = isStringObject(objectChildConstraint);

            if (isObjectString == TR_maybe)
               {
               if (trace())
                  traceMsg(comp(), "Argument type is unknown, quit transforming String.equals on node %p\n", node);
               break;
               }
            else if (isObjectString == TR_no)
               {
               transformCallToIconstInPlaceOrInDelayedTransformations(_curTree, 0, receiverChildGlobal && objectChildGlobal, transformNonnativeMethodInPlace);
               TR::DebugCounter::incStaticDebugCounter(comp(), TR::DebugCounter::debugCounterName(comp(), "constrainCall/(%s)", signature));
               return;
               }
            else // isObjectString == TR_yes
               {
               // The receiver and the argument object have to be const strings or objects known to be strings
               if (isKnownStringObject(receiverChildConstraint)
                   && isKnownStringObject(objectChildConstraint))
                  {
                  uintptrj_t* receiverLocation = getObjectLocationFromConstraint(receiverChildConstraint);
                  uintptrj_t* objectLocation = getObjectLocationFromConstraint(objectChildConstraint);
                  TR_ASSERT(receiverLocation && objectLocation, "Expecting non null pointer to String object for constString or known String object");

                  int32_t result = 0;
                  bool success = comp()->fej9()->stringEquals(comp(), receiverLocation, objectLocation, result);
                  if (!success)
                     {
                     if (trace())
                        traceMsg(comp(), "Does not have VM access, cannot tell whether %p and %p are equal\n", receiverChild, objectChild);
                     break;
                     }
                  transformCallToIconstInPlaceOrInDelayedTransformations(_curTree, result, receiverChildGlobal && objectChildGlobal, transformNonnativeMethodInPlace);
                  TR::DebugCounter::incStaticDebugCounter(comp(), TR::DebugCounter::debugCounterName(comp(), "constrainCall/(%s)", signature));
                  return;
                  }
               }
            }
         break;
         }
      case TR::java_lang_String_length:
      // Only constrain the call in the last run of vp to avoid adding the candidate twice if the call is inside a loop
      if (!lastTimeThrough())
         return;
      // java/lang/String.lengthInternal is only used internally so can be folded without generating HCR guard.
      case TR::java_lang_String_lengthInternal:
         {
         TR::Node *receiverChild = node->getLastChild();
         bool receiverChildGlobal;
         TR::VPConstraint *receiverChildConstraint = getConstraint(receiverChild, receiverChildGlobal);
         // Receiver is a const string or known string object
         if (isKnownStringObject(receiverChildConstraint))
            {
            uintptrj_t* stringLocation = getObjectLocationFromConstraint(receiverChildConstraint);
            TR_ASSERT(stringLocation, "Expecting non null pointer to String object for constString or known String object");
            int32_t len;
            {
            TR::VMAccessCriticalSection getStringlength(comp(),
                                                        TR::VMAccessCriticalSection::tryToAcquireVMAccess);
            if (!getStringlength.hasVMAccess())
               break;
            uintptrj_t stringObject = comp()->fej9()->getStaticReferenceFieldAtAddress((uintptrj_t)stringLocation);
            len = comp()->fej9()->getStringLength(stringObject);
            }
            // java/lang/String.lengthInternal is used internally and HCR guards can be skipped for calls to it.
            transformCallToIconstInPlaceOrInDelayedTransformations(_curTree, len, receiverChildGlobal, transformNonnativeMethodInPlace || rm == TR::java_lang_String_lengthInternal);
            TR::DebugCounter::incStaticDebugCounter(comp(), TR::DebugCounter::debugCounterName(comp(), "constrainCall/(%s)", signature));
            return;
            }
         break;
         }
      case TR::java_lang_Class_getModifiersImpl:
         {
         TR::Node *classChild = node->getLastChild();
         bool classChildGlobal;
         TR::VPConstraint *classChildConstraint = getConstraint(classChild, classChildGlobal);
         if (classChildConstraint && classChildConstraint->isJavaLangClassObject() == TR_yes
             && classChildConstraint->isNonNullObject()
             && classChildConstraint->getClassType()
             && classChildConstraint->getClassType()->asFixedClass())
            {
            int32_t modifiersForClass = 0;
            bool success = comp()->fej9()->javaLangClassGetModifiersImpl(classChildConstraint->getClass(), modifiersForClass);
            if (!success)
               break;
            transformCallToIconstInPlaceOrInDelayedTransformations(_curTree, modifiersForClass, classChildGlobal, true);
            TR::DebugCounter::incStaticDebugCounter(comp(), TR::DebugCounter::debugCounterName(comp(), "constrainCall/(%s)", signature));
            return;
            }
         break;
         }
      case TR::java_lang_Class_isAssignableFrom:
         {
         int32_t numChildren = node->getNumChildren();
         TR::Node *firstClassChild = node->getChild(numChildren-2);
         bool firstClassChildGlobal;
         TR::VPConstraint *firstClassChildConstraint = getConstraint(firstClassChild, firstClassChildGlobal);
         TR::Node *secondClassChild = node->getChild(numChildren-1);
         bool secondClassChildGlobal;
         TR::VPConstraint *secondClassChildConstraint = getConstraint(secondClassChild, secondClassChildGlobal);

         if (firstClassChildConstraint && firstClassChildConstraint->isJavaLangClassObject() == TR_yes
             && firstClassChildConstraint->isNonNullObject()
             && firstClassChildConstraint->getClassType()
             && firstClassChildConstraint->getClassType()->asFixedClass())
            {
            if (secondClassChildConstraint && secondClassChildConstraint->isJavaLangClassObject() == TR_yes
                && secondClassChildConstraint->isNonNullObject()   // NullPointerException is expected if the class is null
                && secondClassChildConstraint->getClassType())
               {
               TR_OpaqueClassBlock *firstClass = firstClassChildConstraint->getClass();
               TR_OpaqueClassBlock *secondClass = secondClassChildConstraint->getClass();
               int32_t assignable = 0;
               if (secondClassChildConstraint->getClassType()->asFixedClass())
                  {
                  TR_YesNoMaybe isInstanceOfResult = comp()->fej9()->isInstanceOf(secondClass, firstClass, true, true);
                  TR_ASSERT(isInstanceOfResult != TR_maybe, "Expecting TR_yes or TR_no to call isInstanceOf when two types are fixed");
                  if (isInstanceOfResult == TR_yes)
                     assignable = 1;
                  }
               else
                  {
                  TR_YesNoMaybe isInstanceOfResult = comp()->fej9()->isInstanceOf(secondClass, firstClass, false, true);
                  if (isInstanceOfResult == TR_maybe)
                     {
                     if (trace())
                        traceMsg(comp(), "Relationship between %p and %p is unknown, quit transforming Class.isAssignableFrom\n", firstClassChild, secondClassChild);
                     return;
                     }
                  else if (isInstanceOfResult == TR_yes)
                     assignable = 1;
                  }
               transformCallToIconstInPlaceOrInDelayedTransformations(_curTree, assignable, firstClassChildGlobal && secondClassChildGlobal, true);
               TR::DebugCounter::incStaticDebugCounter(comp(), TR::DebugCounter::debugCounterName(comp(), "constrainCall/(%s)", signature));
               return;
               }
            }
         break;
         }
      case TR::java_lang_J9VMInternals_identityHashCode:
      case TR::java_lang_J9VMInternals_fastIdentityHashCode:
         {
         // Get the last child because sometimes the first child can be a pointer to java/lang/Class field in J9Class for a direct native call
         TR::Node *classChild = node->getLastChild();
         bool classChildGlobal;
         TR::VPConstraint *classChildConstraint = getConstraint(classChild, classChildGlobal);
         if (classChildConstraint && classChildConstraint->isJavaLangClassObject() == TR_yes
             && classChildConstraint->isNonNullObject()
             && classChildConstraint->getClassType()
             && classChildConstraint->getClassType()->asFixedClass())
            {
            bool hashCodeWasComputed = false;
            int32_t hashCodeForClass = comp()->fej9()->getJavaLangClassHashCode(comp(), classChildConstraint->getClass(), hashCodeWasComputed);
            if (hashCodeWasComputed)
               {
               transformCallToIconstInPlaceOrInDelayedTransformations(_curTree, hashCodeForClass, classChildGlobal, true);
               TR::DebugCounter::incStaticDebugCounter(comp(), TR::DebugCounter::debugCounterName(comp(), "constrainCall/(%s)", signature));
               return;
               }
            }
         break;
         }
      case TR::java_lang_Class_getComponentType:
         {
         TR::Node *classChild = node->getLastChild();
         bool classChildGlobal;
         TR::VPConstraint *classChildConstraint = getConstraint(classChild, classChildGlobal);
         if (classChildConstraint && classChildConstraint->isJavaLangClassObject() == TR_yes
             && classChildConstraint->isNonNullObject()
             && classChildConstraint->getClassType()
             && classChildConstraint->getClassType()->asFixedClass())
            {
            TR_OpaqueClassBlock *thisClass = classChildConstraint->getClass();
            if (comp()->fej9()->isClassArray(thisClass))
               {
               TR_OpaqueClassBlock *arrayComponentClass = comp()->fej9()->getComponentClassFromArrayClass(thisClass);
               // J9Class pointer introduced by the opt has to be remembered under AOT
               if (!arrayComponentClass)
                  {
                  if (trace())
                     traceMsg(comp(), "Array component class cannot be remembered, quit transforming Class.getComponentType on node %p\n", node);
                  break;
                  }

               if (!performTransformation(comp(), "%sTransforming %s on node %p to an aloadi\n", OPT_DETAILS, signature, node))
                  break;

               anchorAllChildren(node, _curTree);
               node->removeAllChildren();

               // Use aconst instead of loadaddr because AOT relocation is not supported for loadaddr
               TR::Node *arrayComponentClassPointer = TR::Node::aconst(node, (uintptrj_t)arrayComponentClass);
               // The classPointerConstant flag has to be set for AOT relocation
               arrayComponentClassPointer->setIsClassPointerConstant(true);
               node = TR::Node::recreateWithoutProperties(node, TR::aloadi, 1, arrayComponentClassPointer, comp()->getSymRefTab()->findOrCreateJavaLangClassFromClassSymbolRef());

               TR::KnownObjectTable *knot = comp()->getOrCreateKnownObjectTable();
               if (knot)
                  {
                  TR::KnownObjectTable::Index knownObjectIndex = knot->getIndexAt((uintptrj_t*)(arrayComponentClass + comp()->fej9()->getOffsetOfJavaLangClassFromClassField()));
                  addBlockOrGlobalConstraint(node,
                        TR::VPClass::create(this,
                           TR::VPKnownObject::createForJavaLangClass(this, knownObjectIndex),
                           TR::VPNonNullObject::create(this), NULL, NULL,
                           TR::VPObjectLocation::create(this, TR::VPObjectLocation::JavaLangClassObject)),
                        classChildGlobal);
                  }

               invalidateUseDefInfo();
               invalidateValueNumberInfo();
               TR::DebugCounter::incStaticDebugCounter(comp(), TR::DebugCounter::debugCounterName(comp(), "constrainCall/(%s)", signature));
               return;
               }
            else
               {
               // Not an array, return null as the component type
               if (trace())
                  traceMsg(comp(), "Class is not an array class, transforming %s on node %p to null\n", signature, node);
               TR::VPConstraint *getComponentTypeConstraint = TR::VPNullObject::create(this);
               replaceByConstant(node, getComponentTypeConstraint, classChildGlobal);
               TR::DebugCounter::incStaticDebugCounter(comp(), TR::DebugCounter::debugCounterName(comp(), "constrainCall/(%s)", signature));
               return;
               }
            }
         break;
         }
      case TR::java_lang_J9VMInternals_getSuperclass:
      case TR::com_ibm_jit_JITHelpers_getSuperclass:
         {
         TR::Node *classChild = node->getLastChild();
         bool classChildGlobal;
         TR::VPConstraint *classChildConstraint = getConstraint(classChild, classChildGlobal);
         if (classChildConstraint && classChildConstraint->isJavaLangClassObject() == TR_yes
             && classChildConstraint->isNonNullObject()
             && classChildConstraint->getClassType()
             && classChildConstraint->getClassType()->asFixedClass())
            {
            TR_OpaqueClassBlock * thisClass = classChildConstraint->getClass();
            // superClass is null for java/lang/Object class
            TR_OpaqueClassBlock *superClass = comp()->fej9()->getSuperClass(thisClass);

            // Super class does not exist for interface class, primitive class and java/lang/Object class object
            if (!superClass || TR::Compiler->cls.isInterfaceClass(comp(),thisClass) || TR::Compiler->cls.isPrimitiveClass(comp(), thisClass))
               {
               if (trace())
                  {
                  if (TR::Compiler->cls.isInterfaceClass(comp(),thisClass))
                     traceMsg(comp(), "Node %p is an interface class and does not have a super class\n", classChild);
                  else if (TR::Compiler->cls.isPrimitiveClass(comp(),thisClass))
                     traceMsg(comp(), "Node %p is a primitive class and does not have a super class\n", classChild);
                  else if (!superClass)
                     traceMsg(comp(), "Node %p is java/lang/Object class and does not have a super class\n", classChild);
                  traceMsg(comp(), "Transform call to %s on node %p to null\n", signature, node);
                  }
               TR::VPConstraint *getSuperClassConstraint = TR::VPNullObject::create(this);
               replaceByConstant(node, getSuperClassConstraint, classChildGlobal);
               TR::DebugCounter::incStaticDebugCounter(comp(), TR::DebugCounter::debugCounterName(comp(), "constrainCall/(%s)", signature));
               return;
               }
            else
               {
               if (!performTransformation(comp(), "%sTransforming %s on node %p into an aloadi\n", OPT_DETAILS, signature, node))
                  break;

               anchorAllChildren(node, _curTree);
               node->removeAllChildren();

               // Use aconst instead of loadaddr because AOT relocation is not supported for loadaddr
               TR::Node *superClassPointer = TR::Node::aconst(node, (uintptrj_t)superClass);
               // The classPointerConstant flag has to be set for AOT relocation
               superClassPointer->setIsClassPointerConstant(true);
               node = TR::Node::recreateWithoutProperties(node, TR::aloadi, 1, superClassPointer, comp()->getSymRefTab()->findOrCreateJavaLangClassFromClassSymbolRef());

               TR::KnownObjectTable *knot = comp()->getOrCreateKnownObjectTable();
               if (knot)
                  {
                  TR::KnownObjectTable::Index knownObjectIndex = knot->getIndexAt((uintptrj_t*)(superClass + comp()->fej9()->getOffsetOfJavaLangClassFromClassField()));
                  addBlockOrGlobalConstraint(node,
                        TR::VPClass::create(this,
                           TR::VPKnownObject::createForJavaLangClass(this, knownObjectIndex),
                           TR::VPNonNullObject::create(this), NULL, NULL,
                           TR::VPObjectLocation::create(this, TR::VPObjectLocation::JavaLangClassObject)),
                        classChildGlobal);
                  }

               invalidateUseDefInfo();
               invalidateValueNumberInfo();
               TR::DebugCounter::incStaticDebugCounter(comp(), TR::DebugCounter::debugCounterName(comp(), "constrainCall/(%s)", signature));
               return;
               }
            }
         break;
         }
      }

   // The following are opts that do not support AOT
   if (!comp()->compileRelocatableCode())
      {
      switch (rm)
         {
         case TR::java_lang_invoke_MethodHandle_asType:
            processAsTypeCallNew(node);
            break;
         case TR::java_lang_invoke_PrimitiveHandle_initializeClassIfRequired:
            {
            TR::Node* mh = node->getArgument(0);
            bool mhConstraintGlobal;
            TR::VPConstraint* mhConstraint = getConstraint(mh, mhConstraintGlobal);
            J9VMThread* vmThread = comp()->fej9()->vmThread();
            TR_OpaqueClassBlock* primitiveHandleClass = J9JitMemory::convertClassPtrToClassOffset(J9VMJAVALANGINVOKEPRIMITIVEHANDLE(vmThread->javaVM));
            bool removeCall = false;
            if (mhConstraint
                && mhConstraint->getKnownObject()
                && mhConstraint->isNonNullObject()
                && mhConstraint->getClass()
                && comp()->fej9()->isInstanceOf(mhConstraint->getClass(), primitiveHandleClass, true, true) == TR_yes)
               {
               uint32_t defcOffset = J9VMJAVALANGINVOKEPRIMITIVEHANDLE_DEFC_OFFSET(comp()->fej9()->vmThread());
               uintptrj_t* mhLocation = getObjectLocationFromConstraint(mhConstraint);

               TR::VMAccessCriticalSection initializeClassIfRequired(comp(),
                                                        TR::VMAccessCriticalSection::tryToAcquireVMAccess);
               if (!initializeClassIfRequired.hasVMAccess())
                  break;
               uintptrj_t mhObject = comp()->fej9()->getStaticReferenceFieldAtAddress((uintptrj_t)mhLocation);
               uintptrj_t defc = comp()->fej9()->getReferenceFieldAtAddress(mhObject + defcOffset);
               J9Class* defcClazz = (J9Class*)TR::Compiler->cls.classFromJavaLangClass(comp(), defc);
               if (defcClazz->initializeStatus == J9ClassInitSucceeded)
                  {
                  removeCall = true;
                  if (trace())
                     {
                     traceMsg(comp(), "defc in MethodHandle %p has been initialized\n", mh);
                     }
                  }
               }

            if (removeCall
                && performTransformation(comp(), "%sRemoving call node %s [" POINTER_PRINTF_FORMAT "]\n", OPT_DETAILS, node->getOpCode().getName(), node))
               {
               TR::Node* receiverChild = node->getArgument(0);
               TR::TransformUtil::transformCallNodeToPassThrough(this, node, _curTree, receiverChild);
               TR::DebugCounter::incStaticDebugCounter(comp(), TR::DebugCounter::debugCounterName(comp(), "constrainCall/(%s)", signature));
               return;
               }
            break;
            }
         case TR::java_lang_invoke_DirectHandle_nullCheckIfRequired:
            {
            TR::Node* mh = node->getArgument(0);
            TR::Node* receiver = node->getArgument(1);
            bool mhConstraintGlobal, receiverConstraintGlobal;
            TR::VPConstraint* mhConstraint = getConstraint(mh, mhConstraintGlobal);
            TR::VPConstraint* receiverConstraint = getConstraint(receiver, receiverConstraintGlobal);

            J9VMThread* vmThread = comp()->fej9()->vmThread();
            TR_OpaqueClassBlock* directHandleClass = calledMethod->classOfMethod();
            if (!mhConstraint
                || !mhConstraint->getClass()
                || comp()->fej9()->isInstanceOf(mhConstraint->getClass(), directHandleClass, true, true) != TR_yes)
               break;

            bool removeCall = false;
            if (receiverConstraint
                && receiverConstraint->isNonNullObject())
               {
               removeCall = true;
               if (trace())
                  {
                  traceMsg(comp(), "receiver child %p for DirectHandle.nullCheckIfRequired is non-null\n", receiver);
                  }
               }
            else if (mhConstraint->getKnownObject()
                     && mhConstraint->isNonNullObject())
               {
               TR_OpaqueClassBlock* mhClass = mhConstraint->getClass();
               int32_t modifierOffset = comp()->fej9()->getInstanceFieldOffset(mhClass, "final_modifiers", 15, "I", 1);
               if (modifierOffset < 0)
                  break;
               uintptrj_t* mhLocation = getObjectLocationFromConstraint(mhConstraint);

               TR::VMAccessCriticalSection nullCheckIfRequired(comp(),
                                                        TR::VMAccessCriticalSection::tryToAcquireVMAccess);
               if (!nullCheckIfRequired.hasVMAccess())
                  break;
               uintptrj_t mhObject = comp()->fej9()->getStaticReferenceFieldAtAddress((uintptrj_t)mhLocation);
               int32_t modifier = comp()->fej9()->getInt32FieldAt(mhObject, modifierOffset);
               if (modifier & J9AccStatic)
                  {
                  removeCall = true;
                  if (trace())
                     {
                     traceMsg(comp(), "Modifier in MethodHandle %p is %d and is static\n", mh, modifier);
                     }
                  }
               }

            if (removeCall
                && performTransformation(comp(), "%sRemoving call node %s [" POINTER_PRINTF_FORMAT "]\n", OPT_DETAILS, node->getOpCode().getName(), node))
               {
               TR::Node* receiverChild = node->getArgument(0);
               TR::TransformUtil::transformCallNodeToPassThrough(this, node, _curTree, receiverChild);
               TR::DebugCounter::incStaticDebugCounter(comp(), TR::DebugCounter::debugCounterName(comp(), "constrainCall/(%s)", signature));
               return;
               }
            break;
            }
         // Transform java/lang/Object.newInstancePrototype into new and a call to default constructor of the given class
         // AOT class pointer relocation is only supported on aconst nodes. However aconst node cannot be a child work of
         // a TR::New node because it does not have a symref indicating the size of the instance of the class.
         case TR::java_lang_Object_newInstancePrototype:
            {
            // The result of newInstancePrototype will never be null since it's equivalent to bytecode new
            addGlobalConstraint(node, TR::VPNonNullObject::create(this));
            node->setIsNonNull(true);

            TR::Node *classChild = node->getChild(1);
            bool classChildGlobal;
            TR::VPConstraint *classChildConstraint = getConstraint(classChild, classChildGlobal);

            if (!classChildConstraint ||
                !classChildConstraint->isNonNullObject() ||
                classChildConstraint->isJavaLangClassObject() != TR_yes ||
                !classChildConstraint->getClassType() ||
                !classChildConstraint->getClassType()->asFixedClass())
               {
               if (trace())
                  traceMsg(comp(), "Class child %p is not a non-null java/lang/Class object with fixed class constraint, quit transforming Object.newInstancePrototype on node %p\n", classChild, node);
               break;
               }

            addGlobalConstraint(node, TR::VPFixedClass::create(this, classChildConstraint->getClass()));

            TR::Node *callerClassChild = node->getChild(2);
            bool callerClassChildGlobal;
            TR::VPConstraint *callerClassChildConstraint = getConstraint(callerClassChild, callerClassChildGlobal);
            if (!callerClassChildConstraint ||
                !callerClassChildConstraint->isNonNullObject() ||
                !callerClassChildConstraint->getClassType() ||
                !callerClassChildConstraint->getClassType()->asFixedClass() ||
                callerClassChildConstraint->isJavaLangClassObject() != TR_yes)
               {
               if (trace())
                  traceMsg(comp(), "Caller class %p is not a non-null java/lang/Class object with fixed class constraint, quit transforming Object.newInstancePrototype on node %p\n", callerClassChild, node);
               break;
               }

            TR_OpaqueClassBlock *newClass = classChildConstraint->getClass();
            TR_OpaqueClassBlock *callerClass = callerClassChildConstraint->getClass();

            // The following classes cannot be instantiated normally, i.e. via the new bytecode
            // InstantiationException will be thrown when calling java/lang/Class.newInstance on the following classes
            if (comp()->fej9()->isAbstractClass(newClass) ||
                comp()->fej9()->isPrimitiveClass(newClass) ||
                comp()->fej9()->isInterfaceClass(newClass) ||
                comp()->fej9()->isClassArray(newClass))
               {
               if (trace())
                  traceMsg(comp(), "Class is not instantiatable via bytecode new, quit transforming Object.newInstancePrototype on node %p\n", node);
               break;
               }

            // Visibility check
            if (!comp()->fej9()->isClassVisible(callerClass, newClass))
               {
               if (trace())
                  traceMsg(comp(), "Class is not visialbe to caller class, quit transforming Object.newInstancePrototype on node %p\n", node);
               break;
               }

            // Look up the default constructor for newClass, visibility check will be done during the look up
            TR_OpaqueMethodBlock *constructor = comp()->fej9()->getMethodFromClass(newClass, "<init>", "()V", callerClass);

            if (!constructor)
               {
               if (trace())
                  traceMsg(comp(), "Cannot find the default constructor, quit transforming Object.newInstancePrototype on node %p\n", node);
               break;
               }

            // Transform the call
            if (performTransformation(comp(), "%sTransforming %s to new and a call to constructor on node %p\n", OPT_DETAILS, signature, node))
               {
               anchorAllChildren(node, _curTree);
               node->removeAllChildren();

               TR::Node *classPointerNode = TR::Node::createWithSymRef(node, TR::loadaddr, 0,
                                         comp()->getSymRefTab()->findOrCreateClassSymbol(node->getSymbolReference()->getOwningMethodSymbol(comp()), -1, newClass));

               TR::Node::recreateWithoutProperties(node, TR::New, 1, comp()->getSymRefTab()->findOrCreateNewObjectSymbolRef(node->getSymbolReference()->getOwningMethodSymbol(comp())));
               node->setAndIncChild(0, classPointerNode);

               TR::SymbolReference *constructorSymRef = comp()->getSymRefTab()->findOrCreateMethodSymbol(JITTED_METHOD_INDEX, -1,
                  comp()->fej9()->createResolvedMethod(trMemory(), constructor), TR::MethodSymbol::Special);

               TR::TreeTop *constructorCall = TR::TreeTop::create(comp(), _curTree,
                   TR::Node::create(node, TR::treetop, 1,
                      TR::Node::createWithSymRef(node, TR::call, 1,
                         node,
                         constructorSymRef)));

               invalidateUseDefInfo();
               invalidateValueNumberInfo();
               TR::DebugCounter::incStaticDebugCounter(comp(), TR::DebugCounter::debugCounterName(comp(), "constrainCall/(%s)", signature));
               return;
               }
            break;
            }
         }
      }
   }

void
J9::ValuePropagation::doDelayedTransformations()
   {
   ListIterator<TreeIntResultPair> callsToBeFoldedToIconst(&_callsToBeFoldedToIconst);
   for (TreeIntResultPair *it = callsToBeFoldedToIconst.getFirst();
        it;
        it = callsToBeFoldedToIconst.getNext())
      {
      TR::TreeTop *callTree = it->_tree;
      int32_t result = it->_result;
      TR::Node * callNode = callTree->getNode()->getFirstChild();
      TR_Method * calledMethod = callNode->getSymbol()->castToMethodSymbol()->getMethod();
      const char *signature = calledMethod->signature(comp()->trMemory(), stackAlloc);

      if (!performTransformation(comp(), "%sTransforming call %s on node %p on tree %p to iconst %d\n", OPT_DETAILS, signature, callNode, callTree, result))
         break;

      transformCallToIconstWithHCRGuard(callTree, result);
      }
   _callsToBeFoldedToIconst.deleteAll();

   OMR::ValuePropagation::doDelayedTransformations();
   }



void
J9::ValuePropagation::getParmValues()
   {
   // Determine how many parms there are
   //
   TR::ResolvedMethodSymbol *methodSym = comp()->getMethodSymbol();
   int32_t numParms = methodSym->getParameterList().getSize();
   if (numParms == 0)
      return;

   // Allocate the constraints array for the parameters
   //
   _parmValues = (TR::VPConstraint**)trMemory()->allocateStackMemory(numParms*sizeof(TR::VPConstraint*));

   // Create a constraint for each parameter that we can find info for.
   // First look for a "this" parameter then look through the method's signature
   //
   TR_ResolvedMethod *method = comp()->getCurrentMethod();
   TR_OpaqueClassBlock *classObject;

   if (!chTableValidityChecked() && usePreexistence())
      {
      TR::ClassTableCriticalSection setCHTableWasValid(comp()->fe());
      if (comp()->getFailCHTableCommit())
         setChTableWasValid(false);
      else
         setChTableWasValid(true);
      setChTableValidityChecked(true);
      }

   int32_t parmIndex = 0;
   TR::VPConstraint *constraint = NULL;
   ListIterator<TR::ParameterSymbol> parms(&methodSym->getParameterList());
   TR::ParameterSymbol *p = parms.getFirst();
   if (!comp()->getCurrentMethod()->isStatic())
      {
      if (p && p->getOffset() == 0)
         {
         classObject = method->containingClass();

         TR_OpaqueClassBlock *prexClass = NULL;
         if (usePreexistence())
            {
            TR::ClassTableCriticalSection usesPreexistence(comp()->fe());

            prexClass = classObject;
            if (TR::Compiler->cls.isAbstractClass(comp(), classObject))
               classObject = comp()->getPersistentInfo()->getPersistentCHTable()->findSingleConcreteSubClass(classObject, comp());

            if (!classObject)
               {
               classObject = prexClass;
               prexClass = NULL;
               }
            else
               {
               TR_PersistentClassInfo * cl = comp()->getPersistentInfo()->getPersistentCHTable()->findClassInfoAfterLocking(classObject, comp());
               if (!cl)
                  prexClass = NULL;
               else
                  {
                  if (!cl->shouldNotBeNewlyExtended())
                     _resetClassesThatShouldNotBeNewlyExtended.add(cl);
                  cl->setShouldNotBeNewlyExtended(comp()->getCompThreadID());

                  TR_ScratchList<TR_PersistentClassInfo> subClasses(trMemory());
                  TR_ClassQueries::collectAllSubClasses(cl, &subClasses, comp());

                  ListIterator<TR_PersistentClassInfo> it(&subClasses);
                  TR_PersistentClassInfo *info = NULL;
                  for (info = it.getFirst(); info; info = it.getNext())
                     {
                     if (!info->shouldNotBeNewlyExtended())
                        _resetClassesThatShouldNotBeNewlyExtended.add(info);
                     info->setShouldNotBeNewlyExtended(comp()->getCompThreadID());
                     }
                  }
               }

            }

         if (prexClass && !fe()->classHasBeenExtended(classObject))
            {
            TR_OpaqueClassBlock *jlKlass = fe()->getClassClassPointer(classObject);
            if (jlKlass)
               {
               if (classObject != jlKlass)
                  {
                  if (!fe()->classHasBeenExtended(classObject))
                     constraint = TR::VPFixedClass::create(this, classObject);
                  else
                     constraint = TR::VPResolvedClass::create(this, classObject);
                  }
               else
                  constraint = TR::VPObjectLocation::create(this, TR::VPObjectLocation::JavaLangClassObject);
               constraint = constraint->intersect(TR::VPPreexistentObject::create(this, prexClass), this);
               TR_ASSERT(constraint, "Cannot intersect constraints");
               }
            }
         else
            {
            // Constraining the receiver's type here should be fine, even if
            // its declared type is an interface (i.e. for a default method
            // implementation). The receiver must always be an instance of (a
            // subtype of) the type that declares the method.
            TR_OpaqueClassBlock *jlKlass = fe()->getClassClassPointer(classObject);
            if (jlKlass)
               {
               if (classObject != jlKlass)
                  constraint = TR::VPResolvedClass::create(this, classObject);
               else
                  constraint = TR::VPObjectLocation::create(this, TR::VPObjectLocation::JavaLangClassObject);
               }
            }

         if (0 && constraint) // cannot do this if 'this' is changed in the method...allow the non null property on the TR::Node set by IL gen to dictate the creation of non null constraint
            {
            constraint = constraint->intersect(TR::VPNonNullObject::create(this), this);
            TR_ASSERT(constraint, "Cannot intersect constraints");
            }

         _parmValues[parmIndex++] = constraint;
         p = parms.getNext();
         }
      }

   TR_MethodParameterIterator * parmIterator = method->getParameterIterator(*comp());
   for ( ; p; p = parms.getNext())
      {
      TR_ASSERT(!parmIterator->atEnd(), "Ran out of parameters unexpectedly.");
      TR::DataType dataType = parmIterator->getDataType();
      if ((dataType == TR::Int8 || dataType == TR::Int16)
          && comp()->getOption(TR_AllowVPRangeNarrowingBasedOnDeclaredType))
         {
         _parmValues[parmIndex++] = TR::VPIntRange::create(this, dataType, TR_maybe);
         }
      else if (dataType == TR::Aggregate)
         {
         constraint = NULL;

         TR_OpaqueClassBlock *opaqueClass = parmIterator->getOpaqueClass();
         if (opaqueClass)
            {
            TR_OpaqueClassBlock *prexClass = NULL;
            if (usePreexistence())
               {
               TR::ClassTableCriticalSection usesPreexistence(comp()->fe());

               prexClass = opaqueClass;
               if (TR::Compiler->cls.isInterfaceClass(comp(), opaqueClass) || TR::Compiler->cls.isAbstractClass(comp(), opaqueClass))
                  opaqueClass = comp()->getPersistentInfo()->getPersistentCHTable()->findSingleConcreteSubClass(opaqueClass, comp());

               if (!opaqueClass)
                  {
                  opaqueClass = prexClass;
                  prexClass = NULL;
                  }
               else
                  {
                  TR_PersistentClassInfo * cl = comp()->getPersistentInfo()->getPersistentCHTable()->findClassInfoAfterLocking(opaqueClass, comp());
                  if (!cl)
                     prexClass = NULL;
                  else
                     {
                     if (!cl->shouldNotBeNewlyExtended())
                        _resetClassesThatShouldNotBeNewlyExtended.add(cl);
                     cl->setShouldNotBeNewlyExtended(comp()->getCompThreadID());

                     TR_ScratchList<TR_PersistentClassInfo> subClasses(trMemory());
                     TR_ClassQueries::collectAllSubClasses(cl, &subClasses, comp());

                     ListIterator<TR_PersistentClassInfo> it(&subClasses);
                     TR_PersistentClassInfo *info = NULL;
                     for (info = it.getFirst(); info; info = it.getNext())
                        {
                        if (!info->shouldNotBeNewlyExtended())
                           _resetClassesThatShouldNotBeNewlyExtended.add(info);
                        info->setShouldNotBeNewlyExtended(comp()->getCompThreadID());
                        }
                     }
                  }

               }

            if (prexClass && !fe()->classHasBeenExtended(opaqueClass))
               {
               TR_OpaqueClassBlock *jlKlass = fe()->getClassClassPointer(opaqueClass);
               if (jlKlass)
                  {
                  if (opaqueClass != jlKlass)
                     {
                     if (!fe()->classHasBeenExtended(opaqueClass))
                        constraint = TR::VPFixedClass::create(this, opaqueClass);
                     else
                        constraint = TR::VPResolvedClass::create(this, opaqueClass);
                     }
                  else
                     constraint = TR::VPObjectLocation::create(this, TR::VPObjectLocation::JavaLangClassObject);
                  constraint = constraint->intersect(TR::VPPreexistentObject::create(this, prexClass), this);
                  TR_ASSERT(constraint, "Cannot intersect constraints");
                  }
               }
            else if (!TR::Compiler->cls.isInterfaceClass(comp(), opaqueClass)
                     || comp()->getOption(TR_TrustAllInterfaceTypeInfo))
               {
               // Interface-typed parameters are not handled here because they
               // will accept arbitrary objects.
               TR_OpaqueClassBlock *jlKlass = fe()->getClassClassPointer(opaqueClass);
               if (jlKlass)
                  {
                  if (opaqueClass != jlKlass)
                     constraint = TR::VPResolvedClass::create(this, opaqueClass);
                  else
                     constraint = TR::VPObjectLocation::create(this, TR::VPObjectLocation::JavaLangClassObject);
                  }
               }
            }
         else if (0) //added here since an unresolved parm could be an interface in which case nothing is known
            {
            char *sig;
            uint32_t len;
            sig = parmIterator->getUnresolvedJavaClassSignature(len);
            constraint = TR::VPUnresolvedClass::create(this, sig, len, method);
            if (usePreexistence() && parmIterator->isClass())
               {
               classObject = constraint->getClass();
               if (classObject && !fe()->classHasBeenExtended(classObject))
                  constraint = TR::VPFixedClass::create(this, classObject);
               constraint = constraint->intersect(TR::VPPreexistentObject::create(this, classObject), this);
               TR_ASSERT(constraint, "Cannot intersect constraints");
               }
            }

         _parmValues[parmIndex++] = constraint;
         }
      else
         {
         _parmValues[parmIndex++] = NULL;
         }
      parmIterator->advanceCursor();
      }

   TR_ASSERT(parmIterator->atEnd() && parmIndex == numParms, "Bad signature for owning method");
   }

static bool isTakenSideOfAVirtualGuard(TR::Compilation* comp, TR::Block* block)
   {
   // First block can never be taken side
   if (block == comp->getMethodSymbol()->getFirstTreeTop()->getEnclosingBlock())
      return false;

   for (auto edge = block->getPredecessors().begin(); edge != block->getPredecessors().end(); ++edge)
      {
      TR::Block *pred = toBlock((*edge)->getFrom());
      TR::Node* predLastRealNode = pred->getLastRealTreeTop()->getNode();

      if (predLastRealNode
          && predLastRealNode->isTheVirtualGuardForAGuardedInlinedCall()
          && predLastRealNode->getBranchDestination()->getEnclosingBlock() == block)
         return true;

      }

   return false;
   }

static bool skipFinalFieldFoldingInBlock(TR::Compilation* comp, TR::Block* block)
   {
   if (block->isCold()
       || block->isOSRCatchBlock()
       || block->isOSRCodeBlock()
       || isTakenSideOfAVirtualGuard(comp, block))
      return true;

   return false;
   }

static bool isStaticFinalFieldWorthFolding(TR::Compilation* comp, TR_OpaqueClassBlock* declaringClass, char* fieldSignature, int32_t fieldSigLength)
   {
   if (comp->getMethodSymbol()->hasMethodHandleInvokes()
       && !TR::Compiler->cls.classHasIllegalStaticFinalFieldModification(declaringClass))
      {
      if (fieldSigLength == 28 && !strncmp(fieldSignature, "Ljava/lang/invoke/VarHandle;", 28))
         return true;
      }

   return false;
   }


// Do not add fear point in a frame that doesn't support OSR
static bool cannotAttemptOSRDuring(TR::Compilation* comp, int32_t callerIndex)
   {
   TR::ResolvedMethodSymbol *method = callerIndex == -1 ?
      comp->getJittedMethodSymbol() : comp->getInlinedResolvedMethodSymbol(callerIndex);

   return method->cannotAttemptOSRDuring(callerIndex, comp, false);
   }

bool J9::ValuePropagation::transformDirectLoad(TR::Node* node)
   {
   // Allow OMR to fold reliable static final field first
   if (OMR::ValuePropagation::transformDirectLoad(node))
      return true;

   if (node->isLoadOfStaticFinalField() &&
       tryFoldStaticFinalFieldAt(_curTree, node))
      {
      return true;
      }

   return false;
   }


static TR_HCRGuardAnalysis* runHCRGuardAnalysisIfPossible()
   {
   return NULL;
   }

TR_YesNoMaybe J9::ValuePropagation::safeToAddFearPointAt(TR::TreeTop* tt)
   {
   if (trace())
      {
      traceMsg(comp(), "Checking if it is safe to add fear point at n%dn\n", tt->getNode()->getGlobalIndex());
      }

   int32_t callerIndex = tt->getNode()->getByteCodeInfo().getCallerIndex();
   if (!cannotAttemptOSRDuring(comp(), callerIndex) && !comp()->isOSRProhibitedOverRangeOfTrees())
      {
      if (trace())
         {
         traceMsg(comp(), "Safe to add fear point because there is no OSR prohibition\n");
         }
      return TR_yes;
      }

   // Look for an OSR point dominating tt in block
   TR::Block* block = tt->getEnclosingBlock();
   TR::TreeTop* firstTT = block->getEntry();
   while (tt != firstTT)
      {
      if (comp()->isPotentialOSRPoint(tt->getNode()))
         {
         TR_YesNoMaybe result = comp()->isPotentialOSRPointWithSupport(tt) ? TR_yes : TR_no;
         if (trace())
            {
            traceMsg(comp(), "Found %s potential OSR point n%dn, %s to add fear point\n",
                     result == TR_yes ? "supported" : "unsupported",
                     tt->getNode()->getGlobalIndex(),
                     result == TR_yes ? "Safe" : "Not safe");
            }

         return result;
         }
      tt = tt->getPrevTreeTop();
      }

   TR_HCRGuardAnalysis* guardAnalysis = runHCRGuardAnalysisIfPossible();
   if (guardAnalysis)
      {
      TR_YesNoMaybe result = guardAnalysis->_blockAnalysisInfo[block->getNumber()]->isEmpty() ? TR_yes : TR_no;
      if (trace())
         {
         traceMsg(comp(), "%s to add fear point based on HCRGuardAnalysis\n", result == TR_yes ? "Safe" : "Not safe");
         }

      return result;
      }

   if (trace())
      {
      traceMsg(comp(), "Cannot determine if it is safe\n");
      }
   return TR_maybe;
   }

/** \brief
 *     Try to fold static final field
 *
 *  \param tree
 *     The tree with the load of static final field.
 *
 *  \param fieldNode
 *     The node which is a load of a static final field.
 */
bool J9::ValuePropagation::tryFoldStaticFinalFieldAt(TR::TreeTop* tree, TR::Node* fieldNode)
   {
   TR_ASSERT(fieldNode->isLoadOfStaticFinalField(), "Node n%dn %p has to be a load of a static final field", fieldNode->getGlobalIndex(), fieldNode);

   if (comp()->getOption(TR_DisableGuardedStaticFinalFieldFolding))
      {
      return false;
      }

   if (!comp()->supportsInduceOSR()
       || !comp()->isOSRTransitionTarget(TR::postExecutionOSR)
       || comp()->getOSRMode() != TR::voluntaryOSR)
      {
      return false;
      }

   TR::SymbolReference* symRef = fieldNode->getSymbolReference();
   if (symRef->hasKnownObjectIndex())
      {
      return false;
      }

   if (skipFinalFieldFoldingInBlock(comp(), tree->getEnclosingBlock())
       || TR::TransformUtil::canFoldStaticFinalField(comp(), fieldNode) != TR_maybe)
      {
      return false;
      }

   int32_t cpIndex = symRef->getCPIndex();
   TR_OpaqueClassBlock* declaringClass = symRef->getOwningMethod(comp())->getClassFromFieldOrStatic(comp(), cpIndex);
   int32_t fieldNameLen;
   char* fieldName = symRef->getOwningMethod(comp())->fieldName(cpIndex, fieldNameLen, comp()->trMemory(), stackAlloc);
   int32_t fieldSigLength;
   char* fieldSignature = symRef->getOwningMethod(comp())->staticSignatureChars(cpIndex, fieldSigLength);

   if (trace())
      {
      traceMsg(comp(),
              "Looking at static final field n%dn %.*s declared in class %p\n",
              fieldNode->getGlobalIndex(), fieldNameLen, fieldName, declaringClass);
      }

   if (isStaticFinalFieldWorthFolding(comp(), declaringClass, fieldSignature, fieldSigLength))
      {
      if (safeToAddFearPointAt(tree) != TR_yes)
         {
         TR::DebugCounter::prependDebugCounter(comp(),
                                               TR::DebugCounter::debugCounterName(comp(),
                                                                                  "staticFinalFieldFolding/notsafe/(field %.*s)/(%s %s)",
                                                                                  fieldNameLen,
                                                                                  fieldName,
                                                                                  comp()->signature(),
                                                                                  comp()->getHotnessName(comp()->getMethodHotness())),
                                                                                  tree->getNextTreeTop());
         }
      else if (TR::TransformUtil::foldStaticFinalFieldAssumingProtection(comp(), fieldNode))
         {
         // Add class to assumption table
         comp()->addClassForStaticFinalFieldModification(declaringClass);
         // Insert osrFearPointHelper call
         TR::TreeTop* helperTree = TR::TreeTop::create(comp(),
                                                       TR::Node::create(fieldNode,
                                                                        TR::treetop,
                                                                        1,
                                                                        TR::Node::createOSRFearPointHelperCall(fieldNode)));
         tree->insertBefore(helperTree);

         if (trace())
            {
            traceMsg(comp(),
                    "Static final field n%dn is folded with OSRFearPointHelper call tree n%dn  helper tree n%dn\n",
                    fieldNode->getGlobalIndex(), tree->getNode()->getGlobalIndex(), helperTree->getNode()->getGlobalIndex());
            }

         TR::DebugCounter::prependDebugCounter(comp(),
                                               TR::DebugCounter::debugCounterName(comp(),
                                                                                  "staticFinalFieldFolding/success/(field %.*s)/(%s %s)",
                                                                                  fieldNameLen,
                                                                                  fieldName,
                                                                                  comp()->signature(),
                                                                                  comp()->getHotnessName(comp()->getMethodHotness())),
                                                                                  tree->getNextTreeTop());

         return true;
         }
      else
         {
         TR::DebugCounter::prependDebugCounter(comp(),
                                               TR::DebugCounter::debugCounterName(comp(),
                                                                                  "staticFinalFieldFolding/cannotfold/(field %.*s)/(%s %s)",
                                                                                  fieldNameLen,
                                                                                  fieldName,
                                                                                  comp()->signature(),
                                                                                  comp()->getHotnessName(comp()->getMethodHotness())),
                                                                                  tree->getNextTreeTop());
         }
      }
   else
      {
      TR::DebugCounter::prependDebugCounter(comp(),
                                            TR::DebugCounter::debugCounterName(comp(),
                                                                               "staticFinalFieldFolding/notWorthFolding/(field %.*s)/(%s %s)",
                                                                               fieldNameLen,
                                                                               fieldName,
                                                                               comp()->signature(),
                                                                               comp()->getHotnessName(comp()->getMethodHotness())),
                                                                               tree->getNextTreeTop());
      }

   return false;
   }
