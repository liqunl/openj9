/*******************************************************************************
 * Copyright (c) 2019, 2019 IBM Corp. and others
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

#include "optimizer/MethodHandleTransformer.hpp"
#include <stddef.h>
#include <stdint.h>
#include "codegen/CodeGenerator.hpp"
#include "env/VMAccessCriticalSection.hpp"
#include "env/FrontEnd.hpp"
#include "compile/Compilation.hpp"
#include "compile/ResolvedMethod.hpp"
#include "compile/SymbolReferenceTable.hpp"
#include "control/Options.hpp"
#include "control/Options_inlines.hpp"
#include "env/CompilerEnv.hpp"
#include "env/IO.hpp"
#include "env/VMJ9.h"
#include "env/j9method.h"
#include "il/ILOpCodes.hpp"
#include "il/ILOps.hpp"
#include "il/MethodSymbol.hpp"
#include "il/Node.hpp"
#include "il/Node_inlines.hpp"
#include "il/ResolvedMethodSymbol.hpp"
#include "il/Symbol.hpp"
#include "il/SymbolReference.hpp"
#include "il/TreeTop.hpp"
#include "il/TreeTop_inlines.hpp"
#include "infra/Assert.hpp"
#include "infra/Checklist.hpp"
#include "optimizer/Optimization.hpp"
#include "optimizer/Optimization_inlines.hpp"
#include "optimizer/TransformUtil.hpp"
#include "optimizer/PreExistence.hpp"
#include "infra/Cfg.hpp"
#include "infra/ILWalk.hpp"
#include <deque>
#include <stack>

static void printObjectInfo(TR_MethodHandleTransformer::ObjectInfo *objectInfo, TR::Compilation *comp)
   {
   int localIndex = 0;
   for (auto it = objectInfo->begin(); it != objectInfo->end(); it++)
      {
      if (*it != TR::KnownObjectTable::UNKNOWN)
         {
         traceMsg(comp, "( local #%2d: obj%d )  ", localIndex, *it);
         }
      localIndex++;
      }
   }

void TR_MethodHandleTransformer::collectLocals(TR_Array<List<TR::SymbolReference>> *autosListArray)
   {
   for (int i = 0; autosListArray && i < autosListArray->size(); i++)
      {
      List<TR::SymbolReference> autosList = (*autosListArray)[i];
      ListIterator<TR::SymbolReference> autosIt(&autosList);
      for (TR::SymbolReference* symRef = autosIt.getFirst(); symRef; symRef = autosIt.getNext())
         {
         TR::AutomaticSymbol *p = symRef->getSymbol()->getAutoSymbol();
         if (p && p->getDataType() == TR::Address)
            {
            if (comp()->getOption(TR_TraceILGen))
               traceMsg(comp(), "Local #%2d is symbol %p [#n%dn]\n", _numLocals, p, symRef->getReferenceNumber());
            p->setLocalIndex(_numLocals++);
            }
         }
      }
   }

int32_t TR_MethodHandleTransformer::perform()
   {
   // Only do the opt for MethodHandle methods
   TR_ResolvedMethod* currentMethod = comp()->getCurrentMethod();
   if (!static_cast<TR_ResolvedJ9Method*>(currentMethod)->isAdapterOrLambdaForm())
      return 0;

   TR::Region currentRegion(comp()->region());

   ListIterator<TR::ParameterSymbol> parms(&comp()->getMethodSymbol()->getParameterList());
   for (TR::ParameterSymbol * p = parms.getFirst(); p; p = parms.getNext())
      {
      if (p->getDataType() == TR::Address)
         {
         if (comp()->getOption(TR_TraceILGen))
            traceMsg(comp(), "Local #%2d is symbol %p <parm %d>\n", _numLocals, p, p->getSlot());
         p->setLocalIndex(_numLocals++);
         }
      }

   collectLocals(comp()->getMethodSymbol()->getAutoSymRefs());
   collectLocals(comp()->getMethodSymbol()->getPendingPushSymRefs());

   typedef TR::typed_allocator<std::pair<const int32_t, ObjectInfo *>, TR::Region &> ResultAllocator;
   typedef std::map<int32_t, ObjectInfo *, std::less<int32_t>, ResultAllocator> BlockResultMap;
   BlockResultMap blockStartObjectInfos(std::less<int32_t>(), comp()->trMemory()->currentStackRegion());

   /*
    * Do a reverse post-order traversal of the CFG as the best effort to figure out object info in one traverse
    */

   TR::ReversePostorderSnapshotBlockIterator blockIt (comp()->getFlowGraph(), comp());
   //Initialize type info for parms for the entry block

   TR::Block *firstBlock = blockIt.currentBlock();
   if (blockIt.currentBlock())
      {
      TR_PrexArgInfo *argInfo = comp()->getCurrentInlinedCallArgInfo();
      ObjectInfo* objectInfo = NULL;
      if (argInfo)
         {
         int32_t numArgs = currentMethod->numberOfParameters();

         TR_ASSERT(argInfo->getNumArgs() == numArgs, "Number of prex arginfo %d doesn't match method parm number %d", argInfo->getNumArgs(), numArgs);

         ListIterator<TR::ParameterSymbol> parms(&comp()->getMethodSymbol()->getParameterList());
         for (TR::ParameterSymbol *p = parms.getFirst(); p != NULL; p = parms.getNext())
            {
            int32_t ordinal = p->getOrdinal();
            TR_PrexArgument *arg = argInfo->get(ordinal);
            if (arg && arg->getKnownObjectIndex() != TR::KnownObjectTable::UNKNOWN)
               {
               if (!objectInfo)
                  objectInfo = new (comp()->trMemory()->currentStackRegion()) ObjectInfo(_numLocals, TR::KnownObjectTable::UNKNOWN, comp()->trMemory()->currentStackRegion());

               (*objectInfo)[p->getLocalIndex()] = arg->getKnownObjectIndex();
               }
            }
         }

      if (objectInfo)
         {
         blockStartObjectInfos[firstBlock->getNumber()] = objectInfo;
         if (trace())
            {
            traceMsg(comp(), "Entry Block (block_%d) object Info: ", firstBlock->getNumber());
            printObjectInfo(objectInfo, comp());
            traceMsg(comp(), "\n");
            }
         }
      }

   TR::BlockChecklist visitedBlock(comp());
   while (blockIt.currentBlock())
      {
      TR::Block *block = blockIt.currentBlock();
      int32_t blockNum = block->getNumber();
      ObjectInfo *blockStartObjectInfo = blockStartObjectInfos.find(blockNum) != blockStartObjectInfos.end()? blockStartObjectInfos[blockNum]: NULL;
      // If there exist one or more predecessor unvisited, the unvisited predecessor must be from a back edge.
      // Clear the block start info as we don't know what might happen from the predecessor
      //
      if (block != firstBlock)
         {
         TR_PredecessorIterator pi(block);
         for (TR::CFGEdge *edge = pi.getFirst(); edge != NULL; edge = pi.getNext())
            {
            TR::Block *fromBlock = toBlock(edge->getFrom());
            int32_t fromBlockNum = fromBlock->getNumber();
            if (blockStartObjectInfo && !visitedBlock.contains(fromBlock))
               {
               blockStartObjectInfo = NULL;
               blockStartObjectInfos[blockNum] = NULL;
               if (trace())
                  traceMsg(comp(), "Predecessor block_%d hasn't been visited yet, clear object info for block_%d\n", fromBlockNum, blockNum);
               break;
               }
            }
         }

      ObjectInfo *blockEndObjectInfo = processBlock(block, blockStartObjectInfo);
      visitedBlock.add(block);
      TR_SuccessorIterator bi(block);
      for (TR::CFGEdge *edge = bi.getFirst(); edge != NULL; edge = bi.getNext())
         {
         TR::Block *nextBlock = toBlock(edge->getTo());
         int32_t nextBlockNum = nextBlock->getNumber();
         //propagate auto type info to successor
         //if the type info exist for the successor merge with the new one
         if (blockEndObjectInfo && !visitedBlock.contains(nextBlock))
            {
            if (blockStartObjectInfos.find(nextBlockNum) != blockStartObjectInfos.end())
               {
               if (trace())
                  traceMsg(comp(), "merging into type info of successor block_%d\n", nextBlockNum);
               mergeObjectInfo(blockStartObjectInfos[nextBlockNum], blockEndObjectInfo);
               }
            else
               blockStartObjectInfos[nextBlockNum] = new (currentRegion) ObjectInfo(*blockEndObjectInfo);
            }
         }
      ++blockIt;
      }
   return 0;
   }

void TR_MethodHandleTransformer::mergeObjectInfo(ObjectInfo *first, ObjectInfo *second)
   {
   bool traceIt = trace();
   if (traceIt)
      {
      traceMsg(comp(), "before merging: ");
      printObjectInfo(first, comp());
      traceMsg(comp(), "\n");
      }

   bool changed = false;
   for (int i = 0; i < _numLocals; i++)
      {
      TR::KnownObjectTable::Index firstObj = (*first)[i];
      TR::KnownObjectTable::Index secondObj = (*second)[i];
      if (firstObj != secondObj)
         {
         (*first)[i] = TR::KnownObjectTable::UNKNOWN;
         changed = true;
         }
      }

   if (changed && traceIt)
      {
      traceMsg(comp(), "after merging: ");
      printObjectInfo(first, comp());
      traceMsg(comp(), "\n");
      }
   }

TR::KnownObjectTable::Index TR_MethodHandleTransformer::getObjectInfoOfNode(TR::Node* node, TR_MethodHandleTransformer::ObjectInfo *objectInfo)
   {
   TR_ASSERT(node->getType() == TR::Address, "Can't have object info on non-address type node n%dn %p", node->getGlobalIndex(), node);

   traceMsg(comp(), "getObjectInfoOfNode from n%dn\n", node->getGlobalIndex());
   if (objectInfo)
      printObjectInfo(objectInfo, comp());

   if (!node->getOpCode().hasSymbolReference())
      return TR::KnownObjectTable::UNKNOWN;

   auto symRef = node->getSymbolReference();
   auto symbol = symRef->getSymbol();

   if (symRef->isUnresolved())
      return TR::KnownObjectTable::UNKNOWN;

   if (symRef->hasKnownObjectIndex())
      return symRef->getKnownObjectIndex();

   auto knot = comp()->getKnownObjectTable();

   if (node->getOpCode().isLoadDirect() &&
       symbol->isAutoOrParm())
      {
      traceMsg(comp(), "getObjectInfoOfNode n%dn is load from auto or parm, local #%d\n", node->getGlobalIndex(), symbol->getLocalIndex());
      return objectInfo ? (*objectInfo)[symbol->getLocalIndex()] : TR::KnownObjectTable::UNKNOWN;
      }

   if (knot &&
       node->getOpCode().isCall() &&
       !symbol->castToMethodSymbol()->isHelper())
      {
      auto rm = symbol->castToMethodSymbol()->getMandatoryRecognizedMethod();
      switch (rm)
        {
        case TR::java_lang_invoke_DirectMethodHandle_internalMemberName:
        case TR::java_lang_invoke_DirectMethodHandle_internalMemberNameEnsureInit:
           {
           auto mhIndex = getObjectInfoOfNode(node->getFirstArgument(), objectInfo);
           if (mhIndex != TR::KnownObjectTable::UNKNOWN && !knot->isNull(mhIndex))
              {
              TR::VMAccessCriticalSection dereferenceKnownObjectField(comp()->fej9());
              uintptr_t mhObject = knot->getPointer(mhIndex);
              uintptr_t mnObject = comp()->fej9()->getReferenceField(mhObject, "member", "Ljava/lang/invoke/MemberName;");
              auto mnIndex = knot->getOrCreateIndex(mnObject);
              if (trace())
                 traceMsg(comp(), "Get DirectMethodHandle.member known object %d\n", mnIndex);
              return mnIndex;
              }
           }
        case TR::java_lang_invoke_DirectMethodHandle_constructorMethod:
           {
           auto mhIndex = getObjectInfoOfNode(node->getFirstArgument(), objectInfo);
           if (mhIndex != TR::KnownObjectTable::UNKNOWN && !knot->isNull(mhIndex))
              {
              TR::VMAccessCriticalSection dereferenceKnownObjectField(comp()->fej9());
              uintptr_t mhObject = knot->getPointer(mhIndex);
              uintptr_t mnObject = comp()->fej9()->getReferenceField(mhObject, "initMethod", "Ljava/lang/invoke/MemberName;");
              auto mnIndex = knot->getOrCreateIndex(mnObject);
              if (trace())
                 traceMsg(comp(), "Get DirectMethodHandle.initMethod known object %d\n", mnIndex);
              return mnIndex;
              }
           }
        }
      }

   return TR::KnownObjectTable::UNKNOWN;
   }

// Store to local variable will change object info
// return the updated object info
TR_MethodHandleTransformer::ObjectInfo *
TR_MethodHandleTransformer::visitStoreToLocalVariable(TR::TreeTop* tt, TR::Node* node, TR_MethodHandleTransformer::ObjectInfo *currentObjectInfo)
   {
   TR::Node *rhs = node->getFirstChild();
   TR::Symbol *local = node->getSymbolReference()->getSymbol();
   if (rhs->getDataType().isAddress())
      {
      // Get object info of the rhs
      TR::KnownObjectTable::Index newObject = getObjectInfoOfNode(rhs, currentObjectInfo);
      traceMsg(comp(), "rhs of store n%dn is obj%d\n", node->getGlobalIndex(), newObject);

      if (newObject != TR::KnownObjectTable::UNKNOWN || currentObjectInfo)
         {
         if (!currentObjectInfo)
            currentObjectInfo = new (comp()->trMemory()->currentStackRegion()) ObjectInfo(_numLocals, TR::KnownObjectTable::UNKNOWN, comp()->trMemory()->currentStackRegion());
         if (trace())
            {
            TR::KnownObjectTable::Index oldObject = (*currentObjectInfo)[local->getLocalIndex()];
            traceMsg(comp(), "Local #%2d obj%d -> obj%d at node n%dn\n", local->getLocalIndex(), oldObject, newObject,  node->getGlobalIndex());
            }
         (*currentObjectInfo)[local->getLocalIndex()] = newObject;
         }
      }
   return currentObjectInfo;
   }

void TR_MethodHandleTransformer::visitIndirectLoad(TR::TreeTop* tt, TR::Node* node, TR_MethodHandleTransformer::ObjectInfo *objectInfo)
   {
   auto symRef = node->getSymbolReference();
   auto symbol = node->getSymbol();
   if (!symRef->isUnresolved() && symbol && (symbol->isFinal() ||
       symbol->isArrayShadowSymbol()))
      {
      auto baseNode = symbol->isArrayShadowSymbol() ? node->getFirstChild()->getFirstChild() : node->getFirstChild();
      if (!baseNode->getOpCode().hasSymbolReference() ||
          baseNode->hasUnresolvedSymbolReference())
         return;

      auto baseSymRef = baseNode->getSymbolReference();
      TR::KnownObjectTable::Index baseObj = baseSymRef->getKnownObjectIndex();
      if (baseObj == TR::KnownObjectTable::UNKNOWN && baseNode->getSymbol()->isAutoOrParm())
         {
         // Get object info for the auto or parm
         baseObj = objectInfo ? (*objectInfo)[baseNode->getSymbol()->getLocalIndex()] : TR::KnownObjectTable::UNKNOWN;
         }

      auto knot = comp()->getKnownObjectTable();
      traceMsg(comp(), "base object for indirect load n%dn is obj%d objectInfo %p\n", baseNode->getGlobalIndex(), baseObj, objectInfo);
      if (baseObj != TR::KnownObjectTable::UNKNOWN && !knot->isNull(baseObj))
         {
         // Have to improve the regular array-shadow to immutable-array-shadow in order to fold it
         if (symbol->isArrayShadowSymbol() && knot->isArrayWithConstantElements(baseObj))
            {
            TR::SymbolReference* improvedSymRef = comp()->getSymRefTab()->findOrCreateImmutableArrayShadowSymbolRef(symbol->getDataType());
            node->setSymbolReference(improvedSymRef);
            traceMsg(comp(), "Improve regular array-shadow to immutable-array-shadow for n%dn\n", node->getGlobalIndex());
            }

         TR::TransformUtil::transformIndirectLoadChain(comp(), node, baseNode, baseObj, NULL);
         }
      }
   }

void TR_MethodHandleTransformer::visitCall(TR::TreeTop* tt, TR::Node* node, TR_MethodHandleTransformer::ObjectInfo *currentObjectInfo)
   {
   auto callNode = node;
   traceMsg(comp(), "Call node n%dn recognized mthod %d\n", callNode->getGlobalIndex(), callNode->getSymbol()->castToMethodSymbol()->getMandatoryRecognizedMethod());
   auto knot = comp()->getKnownObjectTable();
   switch (callNode->getSymbol()->castToMethodSymbol()->getMandatoryRecognizedMethod())
      {
      case TR::java_lang_invoke_MethodHandle_invokeBasic:
         {
         auto mhNode = callNode->getFirstArgument();
         TR::KnownObjectTable::Index objIndex = getObjectInfoOfNode(mhNode, currentObjectInfo);
         traceMsg(comp(), "MH is obj%d\n", objIndex);
         if (knot && objIndex != TR::KnownObjectTable::UNKNOWN && !knot->isNull(objIndex))
            TR::TransformUtil::refineMethodHandleInvokeBasic(comp(), tt, callNode, objIndex, trace());
         else
            {
            TR::DebugCounter::prependDebugCounter(comp(),
                                                  TR::DebugCounter::debugCounterName(comp(),
                                                                                     "MHUnknownObj/invokeBasic/(%s %s)",
                                                                                     comp()->signature(),
                                                                                     comp()->getHotnessName(comp()->getMethodHotness())),
                                                                                     tt);
            }
         break;
         }
      case TR::java_lang_invoke_MethodHandle_linkToSpecial:
      case TR::java_lang_invoke_MethodHandle_linkToVirtual:
      case TR::java_lang_invoke_MethodHandle_linkToStatic:
         {
         auto mnNode = callNode->getLastChild();
         TR::KnownObjectTable::Index objIndex = getObjectInfoOfNode(mnNode, currentObjectInfo);
         if (knot && objIndex != TR::KnownObjectTable::UNKNOWN && !knot->isNull(objIndex))
            TR::TransformUtil::refineMethodHandleLinkTo(comp(), tt, callNode, objIndex, trace());
         else
            {
            TR::DebugCounter::prependDebugCounter(comp(),
                                                  TR::DebugCounter::debugCounterName(comp(),
                                                                                     "MHUnknownObj/linkTo/(%s %s)",
                                                                                     comp()->signature(),
                                                                                     comp()->getHotnessName(comp()->getMethodHotness())),
                                                                                     tt);
            }
         break;
         }
      }
   }

// Visit a node may change the object info
//
TR_MethodHandleTransformer::ObjectInfo *
TR_MethodHandleTransformer::visitNode(TR::TreeTop* tt, TR::Node* node, TR::NodeChecklist &visitedNodes, TR_MethodHandleTransformer::ObjectInfo *currentObjectInfo)
   {
   if (visitedNodes.contains(node)) return currentObjectInfo;
   visitedNodes.add(node);

   for (int32_t i = 0; i < node->getNumChildren(); i++)
       visitNode(tt, node->getChild(i), visitedNodes, currentObjectInfo);

   traceMsg(comp(), "Looking at ttNode n%dn\n", node->getGlobalIndex());

   if (node->getOpCode().isStoreDirect() && node->getSymbolReference()->getSymbol()->isAutoOrParm() && node->getType() == TR::Address)
      {
      currentObjectInfo = visitStoreToLocalVariable(tt, node, currentObjectInfo);
      }
   else if (node->getOpCode().isLoadIndirect() && node->getType() == TR::Address)
      {
      visitIndirectLoad(tt, node, currentObjectInfo);
      }
   else if (node->getOpCode().isCall())
      {
      visitCall(tt, node, currentObjectInfo);
      }
   return currentObjectInfo;
   }

TR_MethodHandleTransformer::ObjectInfo * TR_MethodHandleTransformer::processBlock(TR::Block *block, TR_MethodHandleTransformer::ObjectInfo *blockStartObjectInfo)
   {
   TR_MethodHandleTransformer::ObjectInfo *currentObjectInfo = blockStartObjectInfo;
   TR::NodeChecklist visitedNodes(comp());

   if (trace())
      {
      traceMsg(comp(), "start processing block_%d: ", block->getNumber());
      if (currentObjectInfo)
         printObjectInfo(currentObjectInfo, comp());
      traceMsg(comp(), "\n");
      }

   // Find stores to auto, and calculate value of the auto after the store
   // If the value is a load of final field, try fold the final field
   // If the value is result of a call, try compute the call result
   //
   for (TR::TreeTop *tt = block->getEntry(); tt != block->getExit(); tt = tt->getNextTreeTop())
      {
      TR::Node *node = tt->getNode();
      currentObjectInfo = visitNode(tt, node, visitedNodes, currentObjectInfo);
      }

   if (trace())
      {
      traceMsg(comp(), "end processing block_%d: ", block->getNumber());
      if (currentObjectInfo)
         printObjectInfo(currentObjectInfo, comp());
      traceMsg(comp(), "\n");
      }

   return currentObjectInfo;
   }

const char *
TR_MethodHandleTransformer::optDetailString() const throw()
   {
   return "O^O METHODHANDLE TRANSFORMER: ";
   }

