/*******************************************************************************
 * Copyright (c) 2021, 2021 IBM Corp. and others
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
      : TR::Optimization(manager),
      _numLocals(0),
      _currentObjectInfo(NULL)
      {}

   static TR::Optimization *create(TR::OptimizationManager *manager)
      {
      return new (manager->allocator()) TR_MethodHandleTransformer(manager);
      }

   virtual int32_t perform();
   virtual const char * optDetailString() const throw();

   typedef TR::typed_allocator<TR::Node*, TR::Region &> NodeAllocator;
   typedef std::set<TR::Node*, std::less<TR::Node*>, NodeAllocator> NodeSet;


   // LocalObjectInfo is a super set of TR::KnownObjectTable::Index, with -2
   // added to represent UNUSED status
   typedef int32_t LocalObjectInfo;
   static const LocalObjectInfo UNUSED = -2;
   static const LocalObjectInfo UNKNOWN = TR::KnownObjectTable::UNKNOWN;

   typedef TR::typed_allocator<LocalObjectInfo, TR::Region &> ObjectInfoAllocator;
   typedef std::vector<LocalObjectInfo, ObjectInfoAllocator> ObjectInfo;

   ObjectInfo * processBlock(TR::Block *block, ObjectInfo *objectInfo);
   // Merge ObjectInfo from second into first
   void mergeObjectInfo(ObjectInfo *first, ObjectInfo *second);
   // Assign local index to autos
   void collectLocals(TR_Array<List<TR::SymbolReference>> *autosListArray);
   LocalObjectInfo getObjectInfoOfNode(TR::Node* node);

   void visitIndirectLoad(TR::TreeTop* tt, TR::Node* node);
   void visitStoreToLocalVariable(TR::TreeTop* tt, TR::Node* node);
   void visitCall(TR::TreeTop* tt, TR::Node* node);
   void visitNode(TR::TreeTop* tt, TR::Node* node, TR::NodeChecklist &visitedNodes);

   private:
   uint32_t _numLocals;
   ObjectInfo * _currentObjectInfo;
   };

#endif
