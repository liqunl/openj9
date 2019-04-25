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

#include "optimizer/JSR292Opts.hpp"
#include <stddef.h>
#include <stdint.h>
#include "codegen/CodeGenerator.hpp"
#include "codegen/FrontEnd.hpp"
#include "compile/Compilation.hpp"
#include "compile/ResolvedMethod.hpp"
#include "compile/SymbolReferenceTable.hpp"
#include "control/Options.hpp"
#include "control/Options_inlines.hpp"
#include "env/CompilerEnv.hpp"
#include "exceptions/AOTFailure.hpp"
#include "exceptions/FSDFailure.hpp"
#include "env/IO.hpp"
#include "env/VMAccessCriticalSection.hpp"
#include "env/VMJ9.h"
#include "env/j9method.h"
#include "il/ILOpCodes.hpp"
#include "il/ILOps.hpp"
#include "il/Node.hpp"
#include "il/Node_inlines.hpp"
#include "il/Symbol.hpp"
#include "il/SymbolReference.hpp"
#include "il/TreeTop.hpp"
#include "il/TreeTop_inlines.hpp"
#include "il/symbol/MethodSymbol.hpp"
#include "il/symbol/ResolvedMethodSymbol.hpp"
#include "infra/Assert.hpp"
#include "optimizer/Optimization.hpp"
#include "optimizer/Optimization_inlines.hpp"
#include "optimizer/J9TransformUtil.hpp"
#include "env/JSR292Methods.h"
#include "optimizer/TransformUtil.hpp"

static bool specializeInvokeExactSymbol(TR::Node *callNode, TR::KnownObjectTable::Index receiverIndex, TR::Compilation *comp, TR::Optimization *opt)
   {
   TR::KnownObjectTable     *knot           = comp->getKnownObjectTable();
   uintptrj_t              *refLocation    = knot->getPointerLocation(receiverIndex);
   TR::SymbolReference      *symRef         = callNode->getSymbolReference();
   TR::ResolvedMethodSymbol *owningMethod   = callNode->getSymbolReference()->getOwningMethodSymbol(comp);
   TR_ResolvedMethod       *resolvedMethod = comp->fej9()->createMethodHandleArchetypeSpecimen(comp->trMemory(), refLocation, owningMethod->getResolvedMethod(), true);
   if (resolvedMethod)
      {
      TR::SymbolReference      *specimenSymRef = comp->getSymRefTab()->findOrCreateMethodSymbol(owningMethod->getResolvedMethodIndex(), -1, resolvedMethod, TR::MethodSymbol::ComputedVirtual);
      if (performTransformation(comp, "%sSubstituting more specific method symbol on %p: obj%d.%s <- %s\n", opt->optDetailString(), callNode, receiverIndex,
            specimenSymRef->getName(comp->getDebug()),
            callNode->getSymbolReference()->getName(comp->getDebug())))
         {
         callNode->setSymbolReference(specimenSymRef);
         return true;
         }
      }
      return false;
   }

void TR_JSR292Opts::processIndirectCall(TR::Node *node, TR::TreeTop *treeTop, vcount_t visitCount)
   {
   if (trace())
      traceMsg(comp(), "PREX:      [%p] %s %s\n", node, node->getOpCode().getName(), node->getSymbolReference()->getName(comp()->getDebug()));

   if (!node->getSymbol()->castToMethodSymbol()->firstArgumentIsReceiver())
      {
      if (trace())
         traceMsg(comp(), "PREX:        - First arg is not receiver\n");
      return;
      }

   TR::MethodSymbol   *methodSymbol   = node->getSymbol()->castToMethodSymbol();

   TR_ResolvedMethod *resolvedMethod = methodSymbol->getResolvedMethodSymbol()? methodSymbol->getResolvedMethodSymbol()->getResolvedMethod() : NULL;
   TR::Node *receiver = node->getChild(node->getFirstArgumentIndex());
   if (receiver->getOpCode().hasSymbolReference() &&
       receiver->getSymbolReference()->hasKnownObjectIndex() &&
       resolvedMethod &&
       methodSymbol->isComputed() &&
       !resolvedMethod->convertToMethod()->isArchetypeSpecimen())
      {
      if (methodSymbol->getRecognizedMethod() == TR::java_lang_invoke_MethodHandle_invokeExact)
         {
         specializeInvokeExactSymbol(node, receiver->getSymbolReference()->getKnownObjectIndex(), comp(), this);
         return;
         }
      }
   }

void TR_JSR292Opts::processIndirectLoad(TR::Node *node, TR::TreeTop *treeTop, vcount_t visitCount)
   {
   if (node->getSymbolReference()->hasKnownObjectIndex())
      return;

   TR::Node *ttNode       = treeTop->getNode();
   TR::Node *addressChild = node->getFirstChild();
   if (!addressChild->getOpCode().hasSymbolReference())
      return;

   if (trace())
      traceMsg(comp(), "PREX:        [%p] %s %s\n", node, node->getOpCode().getName(), node->getSymbolReference()->getName(comp()->getDebug()));

   if (addressChild->getSymbolReference()->isUnresolved())
      {
      if (trace())
         traceMsg(comp(), "PREX:          - unresolved\n");
      return;
      }

   bool somethingMayHaveChanged = false;
   TR::Node *nodeToNullCheck = NULL;
   if (  ttNode->getOpCode().isNullCheck()
      && ttNode->getFirstChild() == node
      && ttNode->getNullCheckReference() == addressChild)
      {
      nodeToNullCheck = treeTop->getNode()->getNullCheckReference();
      }

   TR::Node *removedNode = NULL;
   if (addressChild->getSymbolReference()->hasKnownObjectIndex())
      {
      somethingMayHaveChanged = TR::TransformUtil::transformIndirectLoadChain(comp(), node, addressChild, addressChild->getSymbolReference()->getKnownObjectIndex(), &removedNode);
      }
   else if (addressChild->getSymbol()->isFixedObjectRef())
      {
      somethingMayHaveChanged = TR::TransformUtil::transformIndirectLoadChainAt(comp(), node, addressChild, (uintptrj_t*)addressChild->getSymbol()->castToStaticSymbol()->getStaticAddress(), &removedNode);
      }

   if (removedNode)
      {
      if (removedNode->getOpCode().isTreeTop())
         TR::TreeTop::create(comp(), treeTop->getPrevTreeTop(), removedNode);
      else
         TR::TreeTop::create(comp(), treeTop->getPrevTreeTop(), TR::Node::create(TR::treetop, 1, removedNode));
      removedNode->decReferenceCount();
      }

   if (somethingMayHaveChanged && nodeToNullCheck)
      {
      // This node was under a NULLCHK and may no longer be a suitable child for the NULLCHK.
      // Put a passThrough there instead to be safe and correct.
      // The old shape was:
      //
      //   ttNode    // NULLCHK (or some other isNullCheck opcode) on nodeToNullCheck
      //     node
      //       nodeToNullCheck
      //
      // We'll anchor the node right after the NULLCHK, then replace it with a passThrough under the NULLCHK.
      //
      //   ttNode    // NULLCHK (or some other isNullCheck opcode) on nodeToNullCheck
      //     passThrough
      //       nodeToNullCheck
      //   treetop
      //     node
      //
      TR::TreeTop::create(comp(), treeTop, TR::Node::create(TR::treetop, 1, node));
      ttNode->getAndDecChild(0);
      ttNode->setAndIncChild(0, TR::Node::create(TR::PassThrough, 1, nodeToNullCheck));
      if (trace())
         traceMsg(comp(), "PREX:          Anchored [%p] formerly under %s [%p]\n", node, ttNode->getOpCode().getName(), ttNode);
      }
   }

void TR_JSR292Opts::processNode(TR::Node *node, TR::TreeTop *treeTop, vcount_t visitCount)
   {
   if (node->getVisitCount() == visitCount)
      return;
   else
      node->setVisitCount(visitCount);

   for (int32_t i = 0; i < node->getNumChildren(); i++)
      processNode(node->getChild(i), treeTop, visitCount);

   if (node->getOpCode().isLoadIndirect())
      processIndirectLoad(node, treeTop, visitCount);
   else if (node->getOpCode().isCallIndirect())
      processIndirectCall(node, treeTop, visitCount);

   }

int32_t TR_JSR292Opts::perform()
   {
   TR::ResolvedMethodSymbol *methodSymbol = optimizer()->getMethodSymbol();
   vcount_t visitCount = comp()->incOrResetVisitCount();
   for (TR::TreeTop* tt = methodSymbol->getFirstTreeTop(); tt; tt = tt->getNextTreeTop())
      processNode(tt->getNode(), tt, visitCount);

   return 0;
   }

const char *
TR_JSR292Opts::optDetailString() const throw()
   {
   return "O^O JSR292 TRANSFORMER: ";
   }
