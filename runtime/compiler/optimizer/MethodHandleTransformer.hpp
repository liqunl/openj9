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

#ifndef METHODHANDLETRANSFORMER_INCL
#define METHODHANDLETRANSFORMER_INCL

#include <set>
#include <vector>
#include "il/ParameterSymbol.hpp"
#include "compile/Compilation.hpp"
#include "infra/List.hpp"
#include "optimizer/Optimization.hpp"
#include "optimizer/OptimizationManager.hpp"
#include "env/KnownObjectTable.hpp"

class TR_MethodHandleTransformer : public TR::Optimization
   {
   public:
   TR_MethodHandleTransformer(TR::OptimizationManager *manager)
      : TR::Optimization(manager)
      {_numLocals = 0;}

   static TR::Optimization *create(TR::OptimizationManager *manager)
      {
      return new (manager->allocator()) TR_MethodHandleTransformer(manager);
      }

   virtual int32_t perform();
   virtual const char * optDetailString() const throw();
   virtual bool trace() { return true;}

   typedef TR::typed_allocator<TR::Node*, TR::Region &> NodeAllocator;
   typedef std::set<TR::Node*, std::less<TR::Node*>, NodeAllocator> NodeSet;


   typedef TR::typed_allocator<TR::KnownObjectTable::Index, TR::Region &> ObjectInfoAllocator;
   typedef std::vector<TR::KnownObjectTable::Index, ObjectInfoAllocator> ObjectInfo;

   ObjectInfo * processBlock(TR::Block *block, ObjectInfo *objectInfo);
   void mergeObjectInfo(ObjectInfo *first, ObjectInfo *second);
   void collectLocals(TR_Array<List<TR::SymbolReference>> *autosListArray);
   TR::KnownObjectTable::Index getObjectInfoOfNode(TR::Node* node, ObjectInfo *objectInfo);

   void visitIndirectLoad(TR::TreeTop* tt, TR::Node* node, ObjectInfo *currentObjectInfo);
   ObjectInfo * visitStoreToLocalVariable(TR::TreeTop* tt, TR::Node* node, ObjectInfo *currentObjectInfo);
   void visitCall(TR::TreeTop* tt, TR::Node* node, ObjectInfo *currentObjectInfo);
   ObjectInfo* visitNode(TR::TreeTop* tt, TR::Node* node, TR::NodeChecklist &visitedNodes, ObjectInfo *currentObjectInfo);

   private:
   uint32_t _numLocals;
   };

#endif
