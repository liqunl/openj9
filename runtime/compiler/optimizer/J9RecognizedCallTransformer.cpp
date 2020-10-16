/*******************************************************************************
* Copyright (c) 2017, 2020 IBM Corp. and others
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

#include "optimizer/RecognizedCallTransformer.hpp"

#include "compile/ResolvedMethod.hpp"
#include "env/CompilerEnv.hpp"
#include "env/VMJ9.h"
#include "env/jittypes.h"
#include "il/Block.hpp"
#include "il/Node.hpp"
#include "il/Node_inlines.hpp"
#include "il/StaticSymbol.hpp"
#include "il/TreeTop.hpp"
#include "il/TreeTop_inlines.hpp"
#include "il/ILOpCodes.hpp"
#include "il/ILOps.hpp"
#include "ilgen/IlGenRequest.hpp"
#include "ilgen/IlGeneratorMethodDetails.hpp"
#include "ilgen/IlGeneratorMethodDetails_inlines.hpp"
#include "optimizer/CallInfo.hpp"
#include "optimizer/Structure.hpp"
#include "codegen/CodeGenerator.hpp"
#include "optimizer/TransformUtil.hpp"
#include "env/j9method.h"
#include "env/VMAccessCriticalSection.hpp"
#include "optimizer/Optimization_inlines.hpp"
#include "optimizer/PreExistence.hpp"
#include "il/ParameterSymbol.hpp"

void J9::RecognizedCallTransformer::processIntrinsicFunction(TR::TreeTop* treetop, TR::Node* node, TR::ILOpCodes opcode)
   {
   TR::Node::recreate(node, opcode);
   TR::TransformUtil::removeTree(comp(), treetop);
   }

void J9::RecognizedCallTransformer::process_java_lang_Class_IsAssignableFrom(TR::TreeTop* treetop, TR::Node* node)
   {
   auto toClass = node->getChild(0);
   auto fromClass = node->getChild(1);
   auto nullchk = comp()->getSymRefTab()->findOrCreateNullCheckSymbolRef(comp()->getMethodSymbol());
   treetop->insertBefore(TR::TreeTop::create(comp(), TR::Node::createWithSymRef(TR::NULLCHK, 1, 1, TR::Node::create(node, TR::PassThrough, 1, toClass), nullchk)));
   treetop->insertBefore(TR::TreeTop::create(comp(), TR::Node::createWithSymRef(TR::NULLCHK, 1, 1, TR::Node::create(node, TR::PassThrough, 1, fromClass), nullchk)));

   TR::Node::recreate(treetop->getNode(), TR::treetop);
   node->setSymbolReference(comp()->getSymRefTab()->findOrCreateRuntimeHelper(TR_checkAssignable, false, false, false));
   node->setAndIncChild(0, TR::Node::createWithSymRef(TR::aloadi, 1, 1, toClass, comp()->getSymRefTab()->findOrCreateClassFromJavaLangClassSymbolRef()));
   node->setAndIncChild(1, TR::Node::createWithSymRef(TR::aloadi, 1, 1, fromClass, comp()->getSymRefTab()->findOrCreateClassFromJavaLangClassSymbolRef()));
   node->swapChildren();

   toClass->recursivelyDecReferenceCount();
   fromClass->recursivelyDecReferenceCount();
   }

void J9::RecognizedCallTransformer::process_java_lang_StringUTF16_toBytes(TR::TreeTop* treetop, TR::Node* node)
   {
   TR_J9VMBase* fej9 = static_cast<TR_J9VMBase*>(comp()->fe());

   TR::Node* valueNode = node->getChild(0);
   TR::Node* offNode = node->getChild(1);
   TR::Node* lenNode = node->getChild(2);

   anchorAllChildren(node, treetop);
   prepareToReplaceNode(node);

   int32_t byteArrayType = fej9->getNewArrayTypeFromClass(fej9->getByteArrayClass());

   TR::Node::recreateWithoutProperties(node, TR::newarray, 2,
      TR::Node::create(TR::ishl, 2,
         lenNode,
         TR::Node::iconst(1)),
      TR::Node::iconst(byteArrayType),

      getSymRefTab()->findOrCreateNewArraySymbolRef(node->getSymbolReference()->getOwningMethodSymbol(comp())));

   TR::Node* newByteArrayNode = node;
   newByteArrayNode->setCanSkipZeroInitialization(true);
   newByteArrayNode->setIsNonNull(true);

   TR::Node* newCallNode = TR::Node::createWithSymRef(node, TR::call, 5,
      getSymRefTab()->methodSymRefFromName(comp()->getMethodSymbol(), "java/lang/String", "decompressedArrayCopy", "([CI[BII)V", TR::MethodSymbol::Static));
   newCallNode->setAndIncChild(0, valueNode);
   newCallNode->setAndIncChild(1, offNode);
   newCallNode->setAndIncChild(2, newByteArrayNode);
   newCallNode->setAndIncChild(3, TR::Node::iconst(0));
   newCallNode->setAndIncChild(4, lenNode);

   treetop->insertAfter(TR::TreeTop::create(comp(), TR::Node::create(node, TR::treetop, 1, newCallNode)));
   }

void J9::RecognizedCallTransformer::process_java_lang_StrictMath_and_Math_sqrt(TR::TreeTop* treetop, TR::Node* node)
   {
   TR::Node* valueNode = node->getLastChild();

   anchorAllChildren(node, treetop);
   prepareToReplaceNode(node);

   TR::Node::recreate(node, TR::dsqrt);
   node->setNumChildren(1);
   node->setAndIncChild(0, valueNode);

   TR::TransformUtil::removeTree(comp(), treetop);
   }
/*
Transform an Unsafe atomic call to diamonds with equivalent semantics

                          yes
isObjectNull ------------------------------------------>
    |                                                  |
    | no                                               |
    |                     yes                          |
isNotLowTagged ---------------------------------------->
    |                                                  |
    |  no                                              |
    |           no                                     |
isFinal ---------------------->                        |
    |                         |                        |
    | yes                     |                        |
    |                         |                        |
call the                calculate address      calculate address
original method         for static field       for instance field
    |                         |                and absolute address
    |                         |                        |
    |                         |________________________|
    |                                     |
    |                         xcall atomic method helper
    |                                     |
    |_____________________________________|
                    |
      program after the original call

Block before the transformation: ===>

start Block_A
  ...
xcall Unsafe.xxx
  ...
end Block_A

Blocks after the transformation: ===>

start Block_A
...
ifacmpeq -> <Block_E>
  object
  aconst null
end Block_A

start Block_B
iflcmpne -> <Block_E>
  land
    lload <offset>
    lconst J9_SUN_STATIC_FIELD_OFFSET_TAG
  lconst J9_SUN_STATIC_FIELD_OFFSET_TAG
end Block_B

start Block_C
iflcmpeq -> <Block_F>
  land
    lload <offset>
    lconst J9_SUN_FINAL_FIELD_OFFSET_TAG
  lconst J9_SUN_FINAL_FIELD_OFFSET_TAG
end Block_C

start Block_D
astore <object>
  aloadi ramStaticsFromClass
   ...
lstore <offset>
  land
    lload <offset>
    lconst ~J9_SUN_FIELD_OFFSET_MASK
end Block_D

start Block_E
xcall atomic method helper
  aladd
    aload <object>
    lload <offset>
  xload value
end Block_E

...

start Block_F
call jitReportFinalFieldModified
go to <Block_E>
end Block_F
*/
void J9::RecognizedCallTransformer::processUnsafeAtomicCall(TR::TreeTop* treetop, TR::SymbolReferenceTable::CommonNonhelperSymbol helper, bool needsNullCheck)
   {
   bool enableTrace = trace();
   bool isNotStaticField = !strncmp(comp()->getCurrentMethod()->classNameChars(), "java/util/concurrent/atomic/", strlen("java/util/concurrent/atomic/"));
   bool fixupCommoning = true;
   TR::Node* unsafeCall = treetop->getNode()->getFirstChild();
   TR::Node* objectNode = unsafeCall->getChild(1);
   TR::Node* offsetNode = unsafeCall->getChild(2);
   TR::Node* address = NULL;

   // Preserve null check on the unsafe object
   if (treetop->getNode()->getOpCode().isNullCheck())
      {
      TR::Node *passthrough = TR::Node::create(unsafeCall, TR::PassThrough, 1);
      passthrough->setAndIncChild(0, unsafeCall->getFirstChild());
      TR::Node * checkNode = TR::Node::createWithSymRef(treetop->getNode(), TR::NULLCHK, 1, passthrough, treetop->getNode()->getSymbolReference());
      treetop->insertBefore(TR::TreeTop::create(comp(), checkNode));
      TR::Node::recreate(treetop->getNode(), TR::treetop);
      if (enableTrace)
         traceMsg(comp(), "Created node %p to preserve NULLCHK on unsafe call %p\n", checkNode, unsafeCall);
      }

   if (isNotStaticField)
      {
      // It is safe to skip diamond, the address can be calculated directly via [object+offset]
      address = comp()->target().is32Bit() ? TR::Node::create(TR::aiadd, 2, objectNode, TR::Node::create(TR::l2i, 1, offsetNode)) :
                                              TR::Node::create(TR::aladd, 2, objectNode, offsetNode);
      if (enableTrace)
         traceMsg(comp(), "Field is not static, use the object and offset directly\n");
      }
   else
      {
      // Otherwise, the address is [object+offset] for non-static field,
      //            or [object's ramStaticsFromClass + (offset & ~mask)] for static field

      // Save all the children to temps before splitting the block
      TR::TransformUtil::createTempsForCall(this, treetop);

      auto cfg = comp()->getMethodSymbol()->getFlowGraph();
      objectNode = unsafeCall->getChild(1);
      offsetNode = unsafeCall->getChild(2);

      // Null Check
      if (needsNullCheck)
         {
         auto NULLCHKNode = TR::Node::createWithSymRef(unsafeCall, TR::NULLCHK, 1,
                                                       TR::Node::create(TR::PassThrough, 1, objectNode->duplicateTree()),
                                                       comp()->getSymRefTab()->findOrCreateNullCheckSymbolRef(comp()->getMethodSymbol()));
         treetop->insertBefore(TR::TreeTop::create(comp(), NULLCHKNode));
         if (enableTrace)
            traceMsg(comp(), "Created NULLCHK tree %p on the first argument of Unsafe call\n", treetop->getPrevTreeTop());
         }

      // Test if object is null
      auto isObjectNullNode = TR::Node::createif(TR::ifacmpeq, objectNode->duplicateTree(), TR::Node::aconst(0), NULL);
      auto isObjectNullTreeTop = TR::TreeTop::create(comp(), isObjectNullNode);
      treetop->insertBefore(isObjectNullTreeTop);
      treetop->getEnclosingBlock()->split(treetop, cfg, fixupCommoning);
 
      if (enableTrace)
         traceMsg(comp(), "Created isObjectNull test node n%dn, non-null object will fall through to Block_%d\n", isObjectNullNode->getGlobalIndex(), treetop->getEnclosingBlock()->getNumber());

      // Test if low tag is set
      auto isNotLowTaggedNode = TR::Node::createif(TR::iflcmpne,
                                               TR::Node::create(TR::land, 2, offsetNode->duplicateTree(), TR::Node::lconst(J9_SUN_STATIC_FIELD_OFFSET_TAG)),
                                               TR::Node::lconst(J9_SUN_STATIC_FIELD_OFFSET_TAG),
                                               NULL);
      auto isNotLowTaggedTreeTop = TR::TreeTop::create(comp(), isNotLowTaggedNode);
      treetop->insertBefore(isNotLowTaggedTreeTop);
      treetop->getEnclosingBlock()->split(treetop, cfg, fixupCommoning);

      if (enableTrace)
         traceMsg(comp(), "Created isNotLowTagged test node n%dn, static field will fall through to Block_%d\n", isNotLowTaggedNode->getGlobalIndex(), treetop->getEnclosingBlock()->getNumber());

      static char *disableIllegalWriteReport = feGetEnv("TR_DisableIllegalWriteReport");
      // Test if the call is a write to a static final field
      if (!disableIllegalWriteReport
          && !comp()->getOption(TR_DisableGuardedStaticFinalFieldFolding)
          && TR_J9MethodBase::isUnsafePut(unsafeCall->getSymbol()->castToMethodSymbol()->getMandatoryRecognizedMethod()))
         {
         // If the field is static final
         auto isFinalNode = TR::Node::createif(TR::iflcmpeq,
                                                  TR::Node::create(TR::land, 2, offsetNode->duplicateTree(), TR::Node::lconst(J9_SUN_FINAL_FIELD_OFFSET_TAG)),
                                                  TR::Node::lconst(J9_SUN_FINAL_FIELD_OFFSET_TAG),
                                                  NULL /*branchTarget*/);
         auto isFinalTreeTop = TR::TreeTop::create(comp(), isFinalNode);
         auto reportFinalFieldModification = TR::TransformUtil::generateReportFinalFieldModificationCallTree(comp(), objectNode->duplicateTree());
         auto elseBlock = treetop->getEnclosingBlock();
         TR::TransformUtil::createConditionalAlternatePath(comp(), isFinalTreeTop, reportFinalFieldModification, elseBlock, elseBlock, comp()->getMethodSymbol()->getFlowGraph(), true /*markCold*/);
         if (enableTrace)
            {
            traceMsg(comp(), "Created isFinal test node n%dn, non-final-static field will fall through to Block_%d, final field goes to Block_%d\n",
                     isFinalNode->getGlobalIndex(), treetop->getEnclosingBlock()->getNumber(), reportFinalFieldModification->getEnclosingBlock()->getNumber());
            }
         TR::DebugCounter::prependDebugCounter(comp(),
                                               TR::DebugCounter::debugCounterName(comp(),
                                                                                  "illegalWriteReport/atomic/(%s %s)",
                                                                                  comp()->signature(),
                                                                                  comp()->getHotnessName(comp()->getMethodHotness())),
                                                                                  reportFinalFieldModification->getNextTreeTop());

         }

      // Calculate static address
      auto objectAdjustmentNode = TR::Node::createWithSymRef(TR::astore, 1, 1,
                                                             TR::Node::createWithSymRef(TR::aloadi, 1, 1,
                                                                                        TR::Node::createWithSymRef(TR::aloadi, 1, 1,
                                                                                                                   objectNode->duplicateTree(),
                                                                                                                   comp()->getSymRefTab()->findOrCreateClassFromJavaLangClassSymbolRef()),
                                                                                        comp()->getSymRefTab()->findOrCreateRamStaticsFromClassSymbolRef()),
                                                             objectNode->getSymbolReference());
      auto offsetAdjustmentNode = TR::Node::createWithSymRef(TR::lstore, 1, 1,
                                                             TR::Node::create(TR::land, 2,
                                                                              offsetNode->duplicateTree(),
                                                                              TR::Node::lconst(~J9_SUN_FIELD_OFFSET_MASK)),
                                                             offsetNode->getSymbolReference());

      if (enableTrace)
         traceMsg(comp(), "Created node n%dn and n%dn to adjust object and offset for static field\n", objectAdjustmentNode->getGlobalIndex(), offsetAdjustmentNode->getGlobalIndex());

      treetop->insertBefore(TR::TreeTop::create(comp(), objectAdjustmentNode));
      treetop->insertBefore(TR::TreeTop::create(comp(), offsetAdjustmentNode));
      treetop->getEnclosingBlock()->split(treetop, cfg, fixupCommoning);

      if (enableTrace)
         traceMsg(comp(), "Block_%d contains call to atomic method helper, and is the target of isObjectNull and isNotLowTagged tests\n", treetop->getEnclosingBlock()->getNumber());

      // Setup CFG edges
      isObjectNullNode->setBranchDestination(treetop->getEnclosingBlock()->getEntry());
      cfg->addEdge(TR::CFGEdge::createEdge(isObjectNullTreeTop->getEnclosingBlock(), treetop->getEnclosingBlock(), comp()->trMemory()));
      isNotLowTaggedNode->setBranchDestination(treetop->getEnclosingBlock()->getEntry());
      cfg->addEdge(TR::CFGEdge::createEdge(isNotLowTaggedTreeTop->getEnclosingBlock(), treetop->getEnclosingBlock(), comp()->trMemory()));
      address = comp()->target().is32Bit() ? TR::Node::create(TR::aiadd, 2, objectNode->duplicateTree(), TR::Node::create(TR::l2i, 1, offsetNode->duplicateTree())) :
                                              TR::Node::create(TR::aladd, 2, objectNode->duplicateTree(), offsetNode->duplicateTree());
      }

   // Transmute the unsafe call to a call to atomic method helper
   unsafeCall->getChild(0)->recursivelyDecReferenceCount(); // replace unsafe object with the address
   unsafeCall->setAndIncChild(0, address);
   unsafeCall->removeChild(2); // remove offset node
   unsafeCall->removeChild(1); // remove object node
   unsafeCall->setSymbolReference(comp()->getSymRefTab()->findOrCreateCodeGenInlinedHelper(helper));
   }


static TR::KnownObjectTable::Index
getKnownObjectIndexFrom(TR::Compilation* comp, TR::Node* node, int32_t argIndex)
   {
   TR::KnownObjectTable::Index objIndex = TR::KnownObjectTable::UNKNOWN;
   if (node->getOpCode().hasSymbolReference() &&
       node->getSymbolReference()->hasKnownObjectIndex())
      {
      objIndex = node->getSymbolReference()->getKnownObjectIndex();
      }
   else
      {
      // Look for known object from prex arginfo
      TR_PrexArgInfo *argInfo = comp->getCurrentInlinedCallArgInfo();
      if (argInfo && argInfo->getNumArgs() > argIndex)
         {
         TR_PrexArgument *arg = argInfo->get(argIndex);
         if (arg && arg->getKnownObjectIndex() != TR::KnownObjectTable::UNKNOWN)
            {
            objIndex = arg->getKnownObjectIndex();
            }
         }
      }
   return objIndex;
   }

void J9::RecognizedCallTransformer::processInvokeBasic(TR::TreeTop* treetop, TR::Node* node)
   {
   TR_J9VMBase* fej9 = comp()->fej9();
   TR_OpaqueMethodBlock* targetMethod = NULL;
   // If the first argument is known object, refine the call
   auto mhNode = node->getFirstArgument();
   auto objIndex = getKnownObjectIndexFrom(comp(), mhNode, 0);
   targetMethod = fej9->targetMethodFromMethodHandle(comp(), objIndex);

   if (!targetMethod) return;

   auto symRef = node->getSymbolReference();
   // Refine the call
   auto refinedMethod = fej9->createResolvedMethod(comp()->trMemory(), targetMethod, symRef->getOwningMethod(comp()));
   if (trace())
      traceMsg(comp(), "%sspecialize and devirtualize invokeBasic [%p] with known MH object\n", optDetailString(), node);

   refinedMethod->convertToMethod()->setAdapterOrLambdaForm();
   // Preserve NULLCHK
   TR::TransformUtil::separateNullCheck(comp(), treetop, trace());

   TR::SymbolReference *newSymRef =
       getSymRefTab()->findOrCreateMethodSymbol
       (symRef->getOwningMethodIndex(), -1, refinedMethod, TR::MethodSymbol::Static);

   // Should probably use recreate
   TR::Node::recreateWithSymRef(node, refinedMethod->directCallOpCode(), newSymRef);
   }

TR::MethodSymbol::Kinds getTargetMethodCallKind(TR::RecognizedMethod rm)
   {
   TR::MethodSymbol::Kinds callKind;
   switch (rm)
      {
      case TR::java_lang_invoke_MethodHandle_invokeBasic:
      case TR::java_lang_invoke_MethodHandle_linkToStatic:
         callKind = TR::MethodSymbol::Static; break;
      case TR::java_lang_invoke_MethodHandle_linkToSpecial:
         callKind = TR::MethodSymbol::Special; break;
      case TR::java_lang_invoke_MethodHandle_linkToVirtual:
         callKind = TR::MethodSymbol::Virtual; break;
      case TR::java_lang_invoke_MethodHandle_linkToInterface:
         callKind = TR::MethodSymbol::Interface; break;
      default:
         TR_ASSERT(0, "Unsupported method");
      }
   return callKind;
   }

// TODO: use TR::Method*
// Use getIndirectCall(datatype), pass in return type
TR::ILOpCodes getTargetMethodCallOpCode(TR::RecognizedMethod rm, TR::DataType type)
   {
   switch (rm)
      {
      case TR::java_lang_invoke_MethodHandle_invokeBasic:
      case TR::java_lang_invoke_MethodHandle_linkToStatic:
      case TR::java_lang_invoke_MethodHandle_linkToSpecial:
         return TR::ILOpCode::getDirectCall(type);
      case TR::java_lang_invoke_MethodHandle_linkToVirtual:
      case TR::java_lang_invoke_MethodHandle_linkToInterface:
         return TR::ILOpCode::getIndirectCall(type);
      default:
         TR_ASSERT(0, "Unsupported method");
      }
   return TR::BadILOp;
   }

// Scan backwards the trees to find call to DirectMethodHandle.internalMemberName
//

TR::TreeTop* findInternalMemberNameCall(TR::TreeTop* treetop)
   {
   while (treetop)
      {
      auto ttNode = treetop->getNode();
      if (ttNode->getOpCodeValue() == TR::BBStart) return NULL;

      if (ttNode->getNumChildren() == 1 &&
          ttNode->getFirstChild()->getOpCode().isCall())
         {
         auto callNode = treetop->getNode()->getFirstChild();
         auto callSymRef = callNode->getSymbolReference();
         if (callSymRef->getSymbol()->castToMethodSymbol()->isHelper()) continue;

         auto rm = callSymRef->getSymbol()->castToMethodSymbol()->getRecognizedMethod();
         if (rm == TR::java_lang_invoke_DirectMethodHandle_internalMemberName)
            return treetop;
         }
      treetop = treetop->getPrevTreeTop();
      }

   return NULL;
   }

TR::Node*
defToAutoOrParm(TR::Compilation* comp, TR::TreeTop* treetop, TR::SymbolReference* symRef)
   {
   while (treetop)
      {
      auto ttNode = treetop->getNode();
      if (ttNode->getOpCodeValue() == TR::BBStart) return NULL;

      if (ttNode->getOpCode().isStoreDirect() &&
          ttNode->getSymbolReference() == symRef)
         {
         return ttNode->getFirstChild();
         }
      treetop = treetop->getPrevTreeTop();
      }

   return NULL;
   }

TR::KnownObjectTable::Index
getKnownMemberNameForLinkTo(TR::Compilation* comp, TR::TreeTop* treetop, TR::Node* mnNode)
   {
   TR::KnownObjectTable::Index objIndex = TR::KnownObjectTable::UNKNOWN;

   TR_ASSERT(mnNode->getOpCode().hasSymbolReference(), "MemberName node must have symbol reference");

   auto symRef = mnNode->getSymbolReference();
   if (symRef->hasKnownObjectIndex())
      {
      return symRef->getKnownObjectIndex();
      }

   auto callerMethodSymbol = comp->getMethodSymbol();
   if (!callerMethodSymbol->getMethod()->isAdapterOrLambdaForm())
      return TR::KnownObjectTable::UNKNOWN;

   auto memberNameCallTree = findInternalMemberNameCall(treetop->getPrevTreeTop());
   if (!memberNameCallTree)
      {
      traceMsg(comp, "Can't find call to internalMemberName\n");
      return TR::KnownObjectTable::UNKNOWN;
      }

   // Get the MethodHandle object of DirectMethodHandle.internalMemberName
   auto memberNameCallNode = memberNameCallTree->getNode()->getFirstChild();
   auto mhNode = memberNameCallNode->getFirstChild();
   auto mhSymRef = mhNode->getSymbolReference();
   TR::KnownObjectTable::Index mhIndex = mhSymRef->getKnownObjectIndex();

   traceMsg(comp, "mhNode n%dn %p\n", mhNode->getGlobalIndex(), mhNode);

   if (mhIndex == TR::KnownObjectTable::UNKNOWN)
      {
      if (mhSymRef->getSymbol()->isParm() &&
          !callerMethodSymbol->isParmVariant(mhSymRef->getSymbol()->getParmSymbol()))
         {
         int32_t argIndex = mhSymRef->getSymbol()->getParmSymbol()->getOrdinal();
         TR_PrexArgInfo *argInfo = comp->getCurrentInlinedCallArgInfo();
         // Get it from prex arg
         if (argInfo && argInfo->getNumArgs() > argIndex)
            {
            TR_PrexArgument *arg = argInfo->get(argIndex);
            if (arg && arg->getKnownObjectIndex() != TR::KnownObjectTable::UNKNOWN)
               {
               mhIndex = arg->getKnownObjectIndex();
               traceMsg(comp, "DirectMethodHandle from prex arginfo known object %d\n", mhIndex);
               }
            }
         }
      else if (mhSymRef->getSymbol()->isAutoOrParm())
         {
         auto defNodeOfMH = defToAutoOrParm(comp, memberNameCallTree->getPrevTreeTop(), mhSymRef);
         traceMsg(comp, "Def to MethodHandle is %p\n", defNodeOfMH);
         if (defNodeOfMH && defNodeOfMH->getOpCode().hasSymbolReference())
            mhIndex = defNodeOfMH->getSymbolReference()->getKnownObjectIndex();
         }
      }

   // get DirectMethodHandle.member
   if (mhIndex != TR::KnownObjectTable::UNKNOWN)
      {
      auto knot = comp->getKnownObjectTable();
      TR::VMAccessCriticalSection dereferenceKnownObjectField(comp->fej9());
      uintptr_t mhObjectAddress = knot->getPointer(mhIndex);
      uintptr_t memberAddress = comp->fej9()->getReferenceField(mhObjectAddress, "member", "Ljava/lang/invoke/MemberName;");
      objIndex = knot->getOrCreateIndex(memberAddress);
      traceMsg(comp, "Get DirectMethodHandle.member known object %d\n", objIndex);
      }

   return objIndex;
   }

// liqun: MemberName of linkTo is usually a aload of auto slot, whose value is from
// the call to DirectMethodHandle.internalMemberName. So we won't have known object
// on the auto slot without folding DirectMethodHandle.internalMemberName. However,
// we don't have to fold this call, we can calculate its return value like InterpreterEmulator
//
// We can't use this hack for linkTo, especially for linkToStatic, because we use linkToStatic
// for unresolved invokedynamic and invokehandle
// First, let's find the call to DirectMethodHandle.internalMemberName
// Get its MethodHandle, the MethodHandle should be from parm0. If parm0 is variant, find
// the last lef of it. If it's invariant, find known object from prex argInfo
//
void J9::RecognizedCallTransformer::processLinkTo(TR::TreeTop* treetop, TR::Node* node)
   {
   // Get j9method from MemberName
   TR_J9VMBase* fej9 = comp()->fej9();
   TR_OpaqueMethodBlock* targetMethod = NULL;
   auto memberNameNode = node->getLastChild();
   // memberName is from an auto slot, it won't have a prex arg info in the inlining stack
   auto objIndex = getKnownMemberNameForLinkTo(comp(), treetop, memberNameNode);
   targetMethod = fej9->targetMethodFromMemberName(comp(), objIndex);

   if (!targetMethod) return;

   if (trace())
      traceMsg(comp(), "%sspecialize and devirtualize linkTo [%p] with known MH object\n", optDetailString(), node);

   comp()->dumpMethodTrees("Trees before recognized call transformer", comp()->getMethodSymbol());

   auto symRef = node->getSymbolReference();
   auto rm = node->getSymbol()->castToMethodSymbol()->getMandatoryRecognizedMethod();
   TR::MethodSymbol::Kinds callKind = getTargetMethodCallKind(rm);
   TR::ILOpCodes callOpCode = getTargetMethodCallOpCode(rm, node->getDataType());

   TR::SymbolReference* newSymRef = NULL;
   if (rm == TR::java_lang_invoke_MethodHandle_linkToInterface)
      {
      int32_t iTableIndex = fej9->vTableOrITableIndexFromMemberName(comp(), objIndex);
      newSymRef = getSymRefTab()->createInterfaceMethodSymbol(symRef->getOwningMethodSymbol(comp()), targetMethod, iTableIndex);
      }
   else
      {
      uint32_t vTableSlot = 0;
      if (rm == TR::java_lang_invoke_MethodHandle_linkToVirtual)
         {
         vTableSlot = fej9->vTableOrITableIndexFromMemberName(comp(), objIndex);
         }
      auto resolvedMethod = fej9->createResolvedMethod(comp()->trMemory(), vTableSlot, targetMethod, symRef->getOwningMethod(comp()));
      newSymRef = getSymRefTab()->findOrCreateMethodSymbol(symRef->getOwningMethodIndex(), -1, resolvedMethod, callKind);

      if (rm == TR::java_lang_invoke_MethodHandle_linkToVirtual)
         newSymRef->setOffset(fej9->vTableSlotToVirtualCallOffset(vTableSlot));
      }

   bool needNullChk, needVftChild, needResolveChk;
   needNullChk = needVftChild = needResolveChk = false;
   switch (rm)
      {
      case TR::java_lang_invoke_MethodHandle_linkToInterface:
         needResolveChk = true;
      case TR::java_lang_invoke_MethodHandle_linkToVirtual:
         needVftChild = true;
      case TR::java_lang_invoke_MethodHandle_linkToSpecial:
         needNullChk = true;
      }

   // Add NULLCHK on receiver if exists, and resolve check for interface call
   if (needNullChk && needResolveChk)
      {
      TR::Node::recreateWithSymRef(treetop->getNode(), TR::ResolveAndNULLCHK, getSymRefTab()->findOrCreateNullCheckSymbolRef(symRef->getOwningMethodSymbol(comp())));
      }
  else if (needNullChk)
      {
      TR::Node::recreateWithSymRef(treetop->getNode(), TR::NULLCHK, getSymRefTab()->findOrCreateNullCheckSymbolRef(symRef->getOwningMethodSymbol(comp())));
      }

   if (needVftChild)
      {
      auto vftLoad = TR::Node::createWithSymRef(node, TR::aloadi, 1, node->getFirstArgument(), getSymRefTab()->findOrCreateVftSymbolRef());
      // Save all arguments of linkTo* to an array
      int32_t numArgs = node->getNumArguments();
      TR::Node **args= new (comp()->trStackMemory()) TR::Node*[numArgs];
      for (int32_t i = 0; i < numArgs; i++)
         args[i] = node->getArgument(i);

      // Anchor all children to a treetop before transmuting the call node
      node->removeLastChild();
      anchorAllChildren(node, treetop);
      node->removeAllChildren();
      //prepareToReplaceNode(node);
      // vtable/itable index/offset has to be stashed in refinedMethod or in newSymRef
      // Recreate the node to a indirect call node
      TR::Node::recreateWithoutProperties(node, callOpCode, numArgs, vftLoad, newSymRef);
      //
      for (int32_t i = 0; i < numArgs - 1; i++)
         node->setAndIncChild(i + 1, args[i]);
      }
   else
      {
      // VFT child is not needed, the call is direct, just need to change the symref and remove MemberName arg
      node->setSymbolReference(newSymRef);
      // Remove MemberName arg
      node->removeLastChild();
      }

   // The profiling info might be polluted, don't look at it
   node->getByteCodeInfo().setDoNotProfile(true);

   traceMsg(comp(), "   /--- node n%dn --------------------\n", node->getGlobalIndex());
   comp()->getDebug()->printWithFixedPrefix(comp()->getOutFile(), node, 1, true, true, "      ");
   for (int i = 0; i < node->getNumChildren(); i++)
      comp()->getDebug()->printWithFixedPrefix(comp()->getOutFile(), node->getChild(i), 1, true, true, "        ");

   comp()->dumpMethodTrees("Trees after recognized call transformer", comp()->getMethodSymbol());
   }

bool J9::RecognizedCallTransformer::isInlineable(TR::TreeTop* treetop)
   {
   auto node = treetop->getNode()->getFirstChild();
   switch(node->getSymbol()->castToMethodSymbol()->getMandatoryRecognizedMethod())
      {
      case TR::sun_misc_Unsafe_getAndAddInt:
         return !comp()->getOption(TR_DisableUnsafe) && !comp()->compileRelocatableCode() && !TR::Compiler->om.canGenerateArraylets() &&
            cg()->supportsNonHelper(TR::SymbolReferenceTable::atomicFetchAndAddSymbol);
      case TR::sun_misc_Unsafe_getAndSetInt:
         return !comp()->getOption(TR_DisableUnsafe) && !comp()->compileRelocatableCode() && !TR::Compiler->om.canGenerateArraylets() &&
            cg()->supportsNonHelper(TR::SymbolReferenceTable::atomicSwapSymbol);
      case TR::sun_misc_Unsafe_getAndAddLong:
         return !comp()->getOption(TR_DisableUnsafe) && !comp()->compileRelocatableCode() && !TR::Compiler->om.canGenerateArraylets() && comp()->target().is64Bit() &&
            cg()->supportsNonHelper(TR::SymbolReferenceTable::atomicFetchAndAddSymbol);
      case TR::sun_misc_Unsafe_getAndSetLong:
         return !comp()->getOption(TR_DisableUnsafe) && !comp()->compileRelocatableCode() && !TR::Compiler->om.canGenerateArraylets() && comp()->target().is64Bit() &&
            cg()->supportsNonHelper(TR::SymbolReferenceTable::atomicSwapSymbol);
      case TR::java_lang_Class_isAssignableFrom:
         return cg()->supportsInliningOfIsAssignableFrom();
      case TR::java_lang_Integer_rotateLeft:
      case TR::java_lang_Integer_rotateRight:
         return comp()->target().cpu.isX86() || comp()->target().cpu.isZ() || comp()->target().cpu.isPower();
      case TR::java_lang_Long_rotateLeft:
      case TR::java_lang_Long_rotateRight:
         return comp()->target().cpu.isX86() || comp()->target().cpu.isZ() || (comp()->target().cpu.isPower() && comp()->target().is64Bit());
      case TR::java_lang_Math_abs_I:
      case TR::java_lang_Math_abs_L:
      case TR::java_lang_Math_abs_F:
      case TR::java_lang_Math_abs_D:
         return comp()->target().cpu.isX86() || comp()->target().cpu.isZ() || comp()->target().cpu.isPower();
      case TR::java_lang_Math_max_I:
      case TR::java_lang_Math_min_I:
      case TR::java_lang_Math_max_L:
      case TR::java_lang_Math_min_L:
         return !comp()->getOption(TR_DisableMaxMinOptimization);
      case TR::java_lang_StringUTF16_toBytes:
         return !comp()->compileRelocatableCode();
      case TR::java_lang_StrictMath_sqrt:
      case TR::java_lang_Math_sqrt:
         return comp()->target().cpu.getSupportsHardwareSQRT();
      case TR::java_lang_invoke_MethodHandle_invokeBasic:
      case TR::java_lang_invoke_MethodHandle_linkToStatic:
      case TR::java_lang_invoke_MethodHandle_linkToSpecial:
      case TR::java_lang_invoke_MethodHandle_linkToVirtual:
      case TR::java_lang_invoke_MethodHandle_linkToInterface:
         return true;
      default:
         return false;
      }
   }

void J9::RecognizedCallTransformer::transform(TR::TreeTop* treetop)
   {
   auto node = treetop->getNode()->getFirstChild();
   switch(node->getSymbol()->castToMethodSymbol()->getMandatoryRecognizedMethod())
      {
      case TR::sun_misc_Unsafe_getAndAddInt:
      case TR::sun_misc_Unsafe_getAndAddLong:
         processUnsafeAtomicCall(treetop, TR::SymbolReferenceTable::atomicFetchAndAddSymbol);
         break;
      case TR::sun_misc_Unsafe_getAndSetInt:
      case TR::sun_misc_Unsafe_getAndSetLong:
         processUnsafeAtomicCall(treetop, TR::SymbolReferenceTable::atomicSwapSymbol);
         break;
      case TR::java_lang_Class_isAssignableFrom:
         process_java_lang_Class_IsAssignableFrom(treetop, node);
         break;
      case TR::java_lang_Integer_rotateLeft:
         processIntrinsicFunction(treetop, node, TR::irol);
         break;
      case TR::java_lang_Integer_rotateRight:
         {
         // rotateRight(x, distance) = rotateLeft(x, -distance)
         TR::Node *distance = TR::Node::create(node, TR::ineg, 1);
         distance->setChild(0, node->getSecondChild());
         node->setAndIncChild(1, distance);

         processIntrinsicFunction(treetop, node, TR::irol);

         break;
         }
      case TR::java_lang_Long_rotateLeft:
         processIntrinsicFunction(treetop, node, TR::lrol);
         break;
      case TR::java_lang_Long_rotateRight:
         {
         // rotateRight(x, distance) = rotateLeft(x, -distance)
         TR::Node *distance = TR::Node::create(node, TR::ineg, 1);
         distance->setChild(0, node->getSecondChild());
         node->setAndIncChild(1, distance);

         processIntrinsicFunction(treetop, node, TR::lrol);

         break;
         }
      case TR::java_lang_Math_abs_I:
         processIntrinsicFunction(treetop, node, TR::iabs);
         break;
      case TR::java_lang_Math_abs_L:
         processIntrinsicFunction(treetop, node, TR::labs);
         break;
      case TR::java_lang_Math_abs_D:
         processIntrinsicFunction(treetop, node, TR::dabs);
         break;
      case TR::java_lang_Math_abs_F:
         processIntrinsicFunction(treetop, node, TR::fabs);
         break;
      case TR::java_lang_Math_max_I:
         processIntrinsicFunction(treetop, node, TR::imax);
         break;
      case TR::java_lang_Math_min_I:
         processIntrinsicFunction(treetop, node, TR::imin);
         break;
      case TR::java_lang_Math_max_L:
         processIntrinsicFunction(treetop, node, TR::lmax);
         break;
      case TR::java_lang_Math_min_L:
         processIntrinsicFunction(treetop, node, TR::lmin);
         break;
      case TR::java_lang_StringUTF16_toBytes:
         process_java_lang_StringUTF16_toBytes(treetop, node);
         break;
      case TR::java_lang_StrictMath_sqrt:
      case TR::java_lang_Math_sqrt:
         process_java_lang_StrictMath_and_Math_sqrt(treetop, node);
         break;
      case TR::java_lang_invoke_MethodHandle_invokeBasic:
         processInvokeBasic(treetop, node);
         break;
      case TR::java_lang_invoke_MethodHandle_linkToStatic:
      case TR::java_lang_invoke_MethodHandle_linkToSpecial:
      case TR::java_lang_invoke_MethodHandle_linkToVirtual:
      case TR::java_lang_invoke_MethodHandle_linkToInterface:
         processLinkTo(treetop, node);
         break;
      default:
         break;
      }
   }
