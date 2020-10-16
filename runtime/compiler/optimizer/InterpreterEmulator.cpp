/*******************************************************************************
 * Copyright (c) 2000, 2020 IBM Corp. and others
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
#include "optimizer/InterpreterEmulator.hpp"
#include "optimizer/J9EstimateCodeSize.hpp"
#include "env/VMAccessCriticalSection.hpp"
#include "optimizer/PreExistence.hpp"
#include "optimizer/J9CallGraph.hpp"
#include "ilgen/IlGenRequest.hpp"
#include "jilconsts.h"
#include "il/ParameterSymbol.hpp"
#include "optimizer/PreExistence.hpp"
#if defined(J9VM_OPT_JITSERVER)
#include "control/CompilationRuntime.hpp"
#include "env/j9methodServer.hpp"
#endif /* defined(J9VM_OPT_JITSERVER) */

char*
ClassOperand::getSignature(TR::Compilation *comp, TR_Memory *trMemory)
   {
   if (!_signature)
      _signature = TR::Compiler->cls.classSignature(comp, _clazz, trMemory);
   return _signature;
   }

void
InterpreterEmulator::maintainStackForIf(TR_J9ByteCode bc)
   {
   TR_ASSERT_FATAL(_iteratorWithState, "has to be called when the iterator has state!");
   TR_ASSERT_FATAL(bc == J9BCificmpeq || bc == J9BCificmpne, "InterpreterEmulator::maintainStackForIf can only be called with J9BCificmpeq and J9BCificmpne\n");
   int32_t branchBC = _bcIndex + next2BytesSigned();
   int32_t fallThruBC = _bcIndex + 3;
   IconstOperand * second = pop()->asIconst();
   IconstOperand * first = pop()->asIconst();
   bool canBranch = true;
   bool canFallThru = true;
   if (second && first)
      {
      switch (bc)
         {
         case J9BCificmpeq:
            canBranch = second->intValue == first->intValue;
            debugTrace(tracer(), "maintainStackForIf ifcmpeq %d == %d\n", second->intValue, first->intValue);
            break;
         case J9BCificmpne:
            canBranch = second->intValue != first->intValue;
            debugTrace(tracer(), "maintainStackForIf ifcmpne %d != %d\n", second->intValue, first->intValue);
            break;
         }
      canFallThru = !canBranch;
      }

   if (canBranch)
      {
      debugTrace(tracer(), "maintainStackForIf canBranch to bcIndex=%d\n", branchBC);
      genTarget(branchBC);
      }

   if (canFallThru)
      {
      debugTrace(tracer(), "maintainStackForIf canFallThrough to bcIndex=%d\n", fallThruBC);
      genTarget(fallThruBC);
      }
   }

void
InterpreterEmulator::maintainStackForGetField()
   {
   TR_ASSERT_FATAL(_iteratorWithState, "has to be called when the iterator has state!");
   bool isVolatile, isPrivate, isUnresolvedInCP, isFinal;
   TR::DataType type = TR::NoType;
   uint32_t fieldOffset;
   int32_t cpIndex = next2Bytes();
   Operand *newOperand = _unknownOperand;
   bool resolved = _calltarget->_calleeMethod->fieldAttributes(comp(), cpIndex, &fieldOffset, &type, &isVolatile, &isFinal, &isPrivate, false, &isUnresolvedInCP, false);
   if (top()->getKnownObjectIndex() != TR::KnownObjectTable::UNKNOWN && type == TR::Address)
      {
      TR::Symbol::RecognizedField recognizedField = TR::Symbol::searchRecognizedField(comp(), _calltarget->_calleeMethod, cpIndex, false);
      TR::Symbol *fieldSymbol = NULL;
      if (recognizedField != TR::Symbol::UnknownField)
         fieldSymbol = TR::Symbol::createRecognizedShadow(trStackMemory(),type, recognizedField);
      else
         fieldSymbol = TR::Symbol::createShadow(trStackMemory(),type);
      if (isFinal)
         fieldSymbol->setFinal();

      if ((resolved || !isUnresolvedInCP) && comp()->fej9()->canDereferenceAtCompileTimeWithFieldSymbol(fieldSymbol, cpIndex, _calltarget->_calleeMethod))
         {
         TR::KnownObjectTable *knot = comp()->getKnownObjectTable();
         if (knot)
            {
#if defined(J9VM_OPT_JITSERVER)
            if (comp()->isOutOfProcessCompilation())
               {
               TR_ResolvedJ9JITServerMethod *serverMethod = static_cast<TR_ResolvedJ9JITServerMethod*>(_calltarget->_calleeMethod);
               TR_ResolvedMethod *clientMethod = serverMethod->getRemoteMirror();
               TR::KnownObjectTable::Index baseObjectIndex = top()->getKnownObjectIndex();

               auto stream = TR::CompilationInfo::getStream();
               stream->write(JITServer::MessageType::KnownObjectTable_dereferenceKnownObjectField,
                     baseObjectIndex, clientMethod, cpIndex, fieldOffset);

               auto recv = stream->read<TR::KnownObjectTable::Index, uintptr_t*, uintptr_t, uintptr_t>();
               TR::KnownObjectTable::Index resultIndex = std::get<0>(recv);
               uintptr_t *objectPointerReference = std::get<1>(recv);
               uintptr_t fieldAddress = std::get<2>(recv);
               uintptr_t baseObjectAddress = std::get<3>(recv);

               if (resultIndex != TR::KnownObjectTable::UNKNOWN)
                  {
                  knot->updateKnownObjectTableAtServer(resultIndex, objectPointerReference);

                  newOperand = new (trStackMemory()) KnownObjOperand(resultIndex);
                  int32_t len = 0;
                  debugTrace(tracer(), "dereference obj%d (%p)from field %s(offset = %d) of base obj%d(%p)\n",
                        newOperand->getKnownObjectIndex(), (void *)fieldAddress, _calltarget->_calleeMethod->fieldName(cpIndex, len, this->trMemory()),
                        fieldOffset, baseObjectIndex, baseObjectAddress);
                  }
               }
            else
#endif /* defined(J9VM_OPT_JITSERVER) */
               {
               TR::VMAccessCriticalSection dereferenceKnownObjectField(comp()->fej9());
               TR::KnownObjectTable::Index baseObjectIndex = top()->getKnownObjectIndex();
               uintptr_t baseObjectAddress = knot->getPointer(baseObjectIndex);
               TR_OpaqueClassBlock *baseObjectClass = comp()->fej9()->getObjectClass(baseObjectAddress);
               TR_OpaqueClassBlock *fieldDeclaringClass = _calltarget->_calleeMethod->getDeclaringClassFromFieldOrStatic(comp(), cpIndex);
               if (fieldDeclaringClass && comp()->fej9()->isInstanceOf(baseObjectClass, fieldDeclaringClass, true) == TR_yes)
                  {
                  uintptr_t fieldAddress = comp()->fej9()->getReferenceFieldAtAddress(baseObjectAddress + fieldOffset);
                  newOperand = new (trStackMemory()) KnownObjOperand(knot->getOrCreateIndex(fieldAddress));
                  int32_t len = 0;
                  debugTrace(tracer(), "dereference obj%d (%p)from field %s(offset = %d) of base obj%d(%p)\n",
                        newOperand->getKnownObjectIndex(), (void *)fieldAddress, _calltarget->_calleeMethod->fieldName(cpIndex, len, this->trMemory()),
                        fieldOffset, baseObjectIndex, baseObjectAddress);
                  }
               }
            }
         }
      else
         debugTrace(tracer(), "unresolved field or can't derefence in thunk archetype resolved %d isUnresolvedInCP %d\n", resolved, isUnresolvedInCP);
      }
   pop();
   push(newOperand);
   }

void
InterpreterEmulator::saveStack(int32_t targetIndex)
   {
   if (_stack->isEmpty())
      return;
   bool createTargetStack = (targetIndex >= 0 && !_stacks[targetIndex]);
   if (createTargetStack)
      _stacks[targetIndex] = new (trStackMemory()) ByteCodeStack(this->trMemory(), std::max<uint32_t>(20, _stack->size()));
   }

int32_t
InterpreterEmulator::numberOfBlocks()
   {
   int32_t numBlocks = 0;
   TR_J9ByteCode bc = first();
   while (bc != J9BCunknown)
      {
      if (_InterpreterEmulatorFlags[_bcIndex].testAny(InterpreterEmulator::BytecodePropertyFlag::bbStart))
         numBlocks++;
      bc = next();
      }
   return numBlocks;
   }

void
InterpreterEmulator::checkMaintainableSlot()
   {
   int32_t numParmSlots = method()->numberOfParameterSlots();
   int32_t numSlots = numParmSlots + method()->numberOfTemps();
   if (numSlots == 0) return;

   _localVariables = new (trStackMemory()) TR_Array<Operand*>(this->trMemory(), numSlots);
   _maintainableSlot = new (trStackMemory()) bool[numSlots];
   memset(_maintainableSlot, 1, numSlots * sizeof(bool));

   for (uint32_t i = 0; i < numSlots; i++)
      {
      (*_localVariables)[i] = _unknownOperand;
      }

   // Slots of method without control flow are maintainable
   if (numberOfBlocks() == 1)
      return;

   int32_t *numWritesToSlot = new (trStackMemory()) int32_t[numSlots];
   memset(numWritesToSlot, 0, numSlots * sizeof(int32_t));

   TR_J9ByteCode bc = first();
   while (bc != J9BCunknown)
      {
      switch (bc)
         {
         case J9BCistore: case J9BClstore: case J9BCfstore: case J9BCdstore: case J9BCastore:
            numWritesToSlot[nextByte()]++; break;
         case J9BCistorew: case J9BClstorew: case J9BCfstorew: case J9BCdstorew: case J9BCastorew:
            numWritesToSlot[next2Bytes()]++; break;
         case J9BCistore0: case J9BClstore0: case J9BCfstore0: case J9BCdstore0: case J9BCastore0:
            numWritesToSlot[0]++; break;
         case J9BCistore1: case J9BClstore1: case J9BCfstore1: case J9BCdstore1: case J9BCastore1:
            numWritesToSlot[1]++; break;
         case J9BCistore2: case J9BClstore2: case J9BCfstore2: case J9BCdstore2: case J9BCastore2:
            numWritesToSlot[2]++; break;
         case J9BCistore3: case J9BClstore3: case J9BCfstore3: case J9BCdstore3: case J9BCastore3:
            numWritesToSlot[3]++; break;
         }
      bc = next();
      }

   for (int32_t i = 0; i < numSlots; i++)
      {
      if (i < numParmSlots && numWritesToSlot[i] > 0)
         _maintainableSlot[i] = false;
      else if ( i>= numParmSlots && numWritesToSlot[i] > 1)
         _maintainableSlot[i] = false;
      }
   }

void
InterpreterEmulator::initializeIteratorWithState()
   {
   _iteratorWithState = true;
   _unknownOperand = new (trStackMemory()) Operand();
   uint32_t size = this->maxByteCodeIndex() + 5;
   _flags  = (flags8_t *) this->trMemory()->allocateStackMemory(size * sizeof(flags8_t));
   _stacks = (ByteCodeStack * *) this->trMemory()->allocateStackMemory(size * sizeof(ByteCodeStack *));
   memset(_flags, 0, size * sizeof(flags8_t));
   memset(_stacks, 0, size * sizeof(ByteCodeStack *));
   _stack = new (trStackMemory()) TR_Stack<Operand *>(this->trMemory(), 20, false, stackAlloc);

   // Get an array of bool for each slot, initialize it with parms
   // Check if there is a write to parm slot
   // check if there is two writes to auto slot
   checkMaintainableSlot();

   TR_PrexArgInfo *argInfo = _calltarget->_ecsPrexArgInfo;

   if (_maintainableSlot && argInfo)
      {
      TR_ASSERT_FATAL(argInfo->getNumArgs() == method()->numberOfParameters(), "Prex arg number should match parm number");

      if (tracer()->heuristicLevel())
         {
         debugTrace(tracer(), "Save argInfo to slot state array\n");
         argInfo->dumpTrace();
         }

      // save prex arg into local var arrays
      // liqun: there may be a problem creating parameter list now?
      // create the list such that we know what slot an arg uses
      method()->makeParameterList(_methodSymbol);

      ListIterator<TR::ParameterSymbol> parms(&_methodSymbol->getParameterList());
      for (TR::ParameterSymbol *p = parms.getFirst(); p != NULL; p = parms.getNext())
          {
          int32_t ordinal = p->getOrdinal();
          int32_t slotIndex = p->getSlot();
          TR_PrexArgument *prexArgument = argInfo->get(ordinal);
          if (!prexArgument) continue;

          if (TR_PrexArgument::knowledgeLevel(prexArgument) == KNOWN_OBJECT)
             {
             debugTrace(tracer(), "aload known obj%d from slot %d\n", prexArgument->getKnownObjectIndex(), slotIndex);
             (*_localVariables)[slotIndex] = new (trStackMemory()) KnownObjOperand(prexArgument->getKnownObjectIndex());
             }
          else if (TR_PrexArgument::knowledgeLevel(prexArgument) == FIXED_CLASS)
             {
             (*_localVariables)[slotIndex] = new (trStackMemory()) FixedClassOperand(prexArgument->getClass());
             debugTrace(tracer(), "aload fixed class %s from slot %d\n", (*_localVariables)[slotIndex]->getSignature(comp(), this->trMemory()), slotIndex);
             }
          else if (TR_PrexArgument::knowledgeLevel(prexArgument) == PREEXISTENT)
             {
             (*_localVariables)[slotIndex] = new (trStackMemory()) PrexClassOperand(prexArgument->getClass());
             debugTrace(tracer(), "aload prex class %s from slot %d\n", (*_localVariables)[slotIndex]->getSignature(comp(), this->trMemory()), slotIndex);
             }
          else if (prexArgument->getClass())
             {
             (*_localVariables)[slotIndex] = new (trStackMemory()) ClassOperand(prexArgument->getClass());
             debugTrace(tracer(), "aload class %s from slot %d\n", (*_localVariables)[slotIndex]->getSignature(comp(), this->trMemory()), slotIndex);
             }
          }
      }

   genBBStart(0);
   setupBBStartContext(0);
   this->setIndex(0);
   }

bool
InterpreterEmulator::maintainStack(TR_J9ByteCode bc)
   {
   TR_ASSERT_FATAL(_iteratorWithState, "has to be called when the iterator has state!");
   int slotIndex = -1;
   switch (bc)
      {
      case J9BCgetfield: maintainStackForGetField(); break;
      case J9BCaload0: slotIndex = 0; maintainStackForAload(slotIndex); break;
      case J9BCaload1: slotIndex = 1; maintainStackForAload(slotIndex); break;
      case J9BCaload2: slotIndex = 2; maintainStackForAload(slotIndex); break;
      case J9BCaload3: slotIndex = 3; maintainStackForAload(slotIndex); break;
      case J9BCaload:  slotIndex = nextByte(); maintainStackForAload(slotIndex); break;
      case J9BCaloadw: slotIndex = next2Bytes(); maintainStackForAload(slotIndex); break;

      case J9BCinvokespecial:
      case J9BCinvokespecialsplit:
         maintainStackForDirectCall(_calltarget->_calleeMethod);
         break;
      case J9BCiconstm1: push (new (trStackMemory()) IconstOperand(-1)); break;
      case J9BCiconst0:  push (new (trStackMemory()) IconstOperand(0)); break;
      case J9BCiconst1:  push (new (trStackMemory()) IconstOperand(1)); break;
      case J9BCiconst2:  push (new (trStackMemory()) IconstOperand(2)); break;
      case J9BCiconst3:  push (new (trStackMemory()) IconstOperand(3)); break;
      case J9BCiconst4:  push (new (trStackMemory()) IconstOperand(4)); break;
      case J9BCiconst5:  push (new (trStackMemory()) IconstOperand(5)); break;
      case J9BCifne:
         push (new (trStackMemory()) IconstOperand(0));
         maintainStackForIf(J9BCificmpne);
         break;
      case J9BCifeq:
         push (new (trStackMemory()) IconstOperand(0));
         maintainStackForIf(J9BCificmpeq);
         break;
      case J9BCgoto:
         genTarget(bcIndex() + next2BytesSigned());
         break;
      case J9BCpop:
      case J9BCputfield:
      case J9BCputstatic:
         pop();
         break;
      case J9BCladd:
      case J9BCiadd:
      case J9BCisub:
         popn(2);
         pushUnknownOperand();
         break;
      case J9BCistore: case J9BClstore: case J9BCfstore: case J9BCdstore: case J9BCastore:
         maintainStackForStoreAuto(nextByte()); break;
      case J9BCistorew: case J9BClstorew: case J9BCfstorew: case J9BCdstorew: case J9BCastorew:
         maintainStackForStoreAuto(next2Bytes()); break;
      case J9BCistore0: case J9BClstore0: case J9BCfstore0: case J9BCdstore0: case J9BCastore0:
         maintainStackForStoreAuto(0); break;
      case J9BCistore1: case J9BClstore1: case J9BCfstore1: case J9BCdstore1: case J9BCastore1:
         maintainStackForStoreAuto(1); break;
      case J9BCistore2: case J9BClstore2: case J9BCfstore2: case J9BCdstore2: case J9BCastore2:
         maintainStackForStoreAuto(2); break;
      case J9BCistore3: case J9BClstore3: case J9BCfstore3: case J9BCdstore3: case J9BCastore3:
         maintainStackForStoreAuto(3); break;
      // liqun: TODO: maintain stack for the following load auto
      case J9BCiload0: case J9BCiload1: case J9BCiload2: case J9BCiload3:
      case J9BCdload0: case J9BCdload1: case J9BCdload2: case J9BCdload3:
      case J9BClload0: case J9BClload1: case J9BClload2: case J9BClload3:
      case J9BCfload0: case J9BCfload1: case J9BCfload2: case J9BCfload3:
      case J9BCiloadw: case J9BClloadw: case J9BCfloadw: case J9BCdloadw:
      case J9BCiload:  case J9BClload:  case J9BCfload:  case J9BCdload:
      case J9BCgetstatic:
         pushUnknownOperand();
         break;
      case J9BCgenericReturn:
      case J9BCi2l:
         break;
      //following bytecodes has been handled when creating callsites
      case J9BCinvokevirtual:
      case J9BCinvokestatic:
      case J9BCinvokestaticsplit:
         break;
      case J9BCcheckcast:
         break;
      case J9BCdup:
         push(top());
         break;
      case J9BCldc:
         maintainStackForldc(nextByte()); break;
      default:
         static const bool assertfatal = feGetEnv("TR_AssertFatalForUnexpectedBytecodeInMethodHandleThunk") ? true: false;
         if (!assertfatal)
            debugTrace(tracer(), "unexpected bytecode in thunk archetype %s (%p) at bcIndex %d %s (%d)\n", _calltarget->_calleeMethod->signature(comp()->trMemory()), _calltarget, bcIndex(), comp()->fej9()->getByteCodeName(nextByte(0)), bc);
         else
            TR_ASSERT_FATAL(0, "unexpected bytecode in thunk archetype %s (%p) at bcIndex %d %s (%d)\n", _calltarget->_calleeMethod->signature(comp()->trMemory()), _calltarget, bcIndex(), comp()->fej9()->getByteCodeName(nextByte(0)), bc);

         TR::DebugCounter::incStaticDebugCounter(comp(),
            TR::DebugCounter::debugCounterName(comp(),
               "InterpreterEmulator.unexpectedBytecode/(root=%s)/(%s)/bc=%d/%s",
               comp()->signature(),
               _calltarget->_calleeMethod->signature(comp()->trMemory()),
               _bcIndex,
               comp()->fej9()->getByteCodeName(nextByte(0)))
            );
         return false;
      }
   return true;
   }

void
InterpreterEmulator::maintainStackForldc(int32_t cpIndex)
   {
   TR::DataType type = method()->getLDCType(cpIndex);
   switch (type)
      {
      case TR::Address:
         // liqun: TODO: should add a function to check if cp entry is unresolved for constant
         // not just for string
         if (method()->isStringConstant(cpIndex) && !method()->isUnresolvedString(cpIndex))
            {
            uintptr_t * location = (uintptr_t *)method()->stringConstant(cpIndex);
            TR::KnownObjectTable *knot = comp()->getKnownObjectTable();
            if (knot)
               {
               TR::KnownObjectTable::Index koi = knot->getOrCreateIndexAt(location);
               push(new (trStackMemory()) KnownObjOperand(koi));
               debugTrace(tracer(), "aload known obj%d from ldc %d\n", koi, cpIndex);
               return;
               }
            }
         break;
      default:
         break;
      }

   pushUnknownOperand();
   }

void
InterpreterEmulator::maintainStackForStoreAuto(int slotIndex)
   {
   TR_ASSERT_FATAL(_iteratorWithState, "has to be called when the iterator has state!");
   if (_maintainableSlot[slotIndex])
      {
      (*_localVariables)[slotIndex] = pop();
      }
   else
      pop();
   }

void
InterpreterEmulator::maintainStackForAload(int slotIndex)
   {
   TR_ASSERT_FATAL(_iteratorWithState, "has to be called when the iterator has state!");
   if (_maintainableSlot[slotIndex])
      {
      push((*_localVariables)[slotIndex]);
      return;
      }

   TR_PrexArgInfo *argInfo = _calltarget->_ecsPrexArgInfo;
   TR_ASSERT_FATAL(argInfo, "thunk archetype target doesn't have _ecsPrexArgInfo %p\n", _calltarget);
   if (slotIndex < argInfo->getNumArgs())
      {
      TR_PrexArgument *prexArgument = argInfo->get(slotIndex);
      if (prexArgument && TR_PrexArgument::knowledgeLevel(prexArgument) == KNOWN_OBJECT)
         {
         debugTrace(tracer(), "aload known obj%d from slot %d\n", prexArgument->getKnownObjectIndex(), slotIndex);
         push(new (trStackMemory()) KnownObjOperand(prexArgument->getKnownObjectIndex()));
         return;
         }
      }
   pushUnknownOperand();
   }

void
InterpreterEmulator::maintainStackForCall(TR_ResolvedMethod *callerMethod, Operand *result, int32_t numArgs, TR::DataType returnType)
   {
   TR_ASSERT_FATAL(_iteratorWithState, "has to be called when the iterator has state!");

   for (int i = 1; i <= numArgs; i++)
      pop();

   if (result)
      push(result);
   else if (returnType != TR::NoType)
      pushUnknownOperand();
   }

void
InterpreterEmulator::maintainStackForCall(TR_ResolvedMethod *callerMethod, Operand *result, bool isDirect)
   {
   TR_ASSERT_FATAL(_iteratorWithState, "has to be called when the iterator has state!");
   // liqun: can't use cpIndex to get callee. This is the initial callee, it can be
   // refined to a method that takes different number of arguments
   int32_t cpIndex = next2Bytes();
   TR::Method * calleeMethod = comp()->fej9()->createMethod(trMemory(), callerMethod->containingClass(), cpIndex);
   int32_t argNum = calleeMethod->numberOfExplicitParameters() + (isDirect ? 0: 1);

   for (int i = 1; i <= argNum; i++)
      pop();

   if (result)
      push(result);
   else if (calleeMethod->returnType() != TR::NoType)
      pushUnknownOperand();
   }

void
InterpreterEmulator::dumpStack()
   {
   debugTrace(tracer(), "operandStack after %d : %s ", _bcIndex, comp()->fej9()->getByteCodeName(nextByte(0)));
   for (int i = 0; i < _stack->size(); i++ )
      {
      Operand *x = (*_stack)[i];
      char buffer[20];
      x->printToString(buffer);
      debugTrace(tracer(), "[%d]=%s, ", i, buffer);
      }
   debugTrace(tracer(),"\n");
   }

Operand *
InterpreterEmulator::getReturnValueForInvokestatic(TR_ResolvedMethod *callee)
   {
   if (!callee)
      return NULL;
   Operand *result = NULL;
   TR::RecognizedMethod recognizedMethod = callee->getRecognizedMethod();
   TR::IlGeneratorMethodDetails & details = comp()->ilGenRequest().details();
   if (details.isMethodHandleThunk())
      {
      J9::MethodHandleThunkDetails & thunkDetails = static_cast<J9::MethodHandleThunkDetails &>(details);
      if (!thunkDetails.isCustom())
         recognizedMethod = TR::unknownMethod;
      }

   switch (recognizedMethod)
      {
      case TR::java_lang_invoke_ILGenMacros_isCustomThunk:
         result = new (trStackMemory()) IconstOperand(1);
         break;
      case TR::java_lang_invoke_ILGenMacros_isShareableThunk:
         result = new (trStackMemory()) IconstOperand(0);
         break;
      case TR::java_lang_invoke_DirectMethodHandle_internalMemberName:
         {
         Operand* mh = top();
         TR::KnownObjectTable::Index mhIndex = top()->getKnownObjectIndex();
         debugTrace(tracer(), "Known DirectMethodHandle koi %d\n", mhIndex);
         TR::KnownObjectTable *knot = comp()->getKnownObjectTable();
         if (mhIndex != TR::KnownObjectTable::UNKNOWN)
            {
            TR::VMAccessCriticalSection dereferenceKnownObjectField(comp()->fej9());
            uintptr_t mhObjectAddress = knot->getPointer(mhIndex);
            uintptr_t memberAddress = comp()->fej9()->getReferenceField(mhObjectAddress, "member", "Ljava/lang/invoke/MemberName;");
            TR::KnownObjectTable::Index memberIndex = knot->getOrCreateIndex(memberAddress);
            debugTrace(tracer(), "Known internal member name koi %d\n", memberIndex);
            result = new (trStackMemory()) KnownObjOperand(memberIndex);
            }
         break;
         }
      }
   return result;
   }

Operand *
InterpreterEmulator::getReturnValueForInvokevirtual(TR_ResolvedMethod *callee)
   {
   if (!callee)
      return NULL;
   Operand *result = NULL;
   TR::KnownObjectTable *knot = comp()->getKnownObjectTable();
   if (callee->getRecognizedMethod() == TR::java_lang_invoke_MutableCallSite_getTarget &&
      knot)
      {
      int argNum = callee->numberOfExplicitParameters();
      TR::KnownObjectTable::Index receiverIndex = topn(argNum)->getKnownObjectIndex();
      if (receiverIndex == TR::KnownObjectTable::UNKNOWN)
         return NULL;

      TR::KnownObjectTable::Index resultIndex = TR::KnownObjectTable::UNKNOWN;
      TR_OpaqueClassBlock *mutableCallsiteClass = callee->classOfMethod();
      debugTrace(tracer(), "java_lang_invoke_MutableCallSite_target receiver obj%d(*%p) mutableCallsiteClass %p\n", receiverIndex, knot->getPointerLocation(receiverIndex), mutableCallsiteClass);
      if (mutableCallsiteClass)
         {
#if defined(J9VM_OPT_JITSERVER)
         if (comp()->isOutOfProcessCompilation())
            {
            auto stream = TR::CompilationInfo::getStream();
            stream->write(JITServer::MessageType::KnownObjectTable_dereferenceKnownObjectField2, mutableCallsiteClass, receiverIndex);

            auto recv = stream->read<TR::KnownObjectTable::Index, uintptr_t*>();
            resultIndex = std::get<0>(recv);
            uintptr_t *objectPointerReference = std::get<1>(recv);

            if (resultIndex != TR::KnownObjectTable::UNKNOWN)
               {
               knot->updateKnownObjectTableAtServer(resultIndex, objectPointerReference);
               }
            result = new (trStackMemory()) MutableCallsiteTargetOperand(resultIndex, receiverIndex);
            }
         else
#endif /* defined(J9VM_OPT_JITSERVER) */
            {
            TR::VMAccessCriticalSection dereferenceKnownObjectField(comp()->fej9());
            int32_t targetFieldOffset = comp()->fej9()->getInstanceFieldOffset(mutableCallsiteClass, "target", "Ljava/lang/invoke/MethodHandle;");
            uintptr_t receiverAddress = knot->getPointer(receiverIndex);
            TR_OpaqueClassBlock *receiverClass = comp()->fej9()->getObjectClass(receiverAddress);
            TR_ASSERT_FATAL(comp()->fej9()->isInstanceOf(receiverClass, mutableCallsiteClass, true) == TR_yes, "receiver of mutableCallsite_getTarget must be instance of MutableCallSite (*%p)", knot->getPointerLocation(receiverIndex));
            uintptr_t fieldAddress = comp()->fej9()->getReferenceFieldAt(receiverAddress, targetFieldOffset);
            resultIndex = knot->getOrCreateIndex(fieldAddress);
            result = new (trStackMemory()) MutableCallsiteTargetOperand(resultIndex, receiverIndex);
            }
         }
      }
   return result;
   }

void
InterpreterEmulator::refineResolvedCalleeForInvokestatic(TR_ResolvedMethod *&callee, TR::KnownObjectTable::Index & mcsIndex, TR::KnownObjectTable::Index & mhIndex, bool &isIndirectCall)
   {
   TR_ASSERT_FATAL(_iteratorWithState, "has to be called when the iterator has state!");
   if (!comp()->getOrCreateKnownObjectTable())
      return;

   bool isVirtual = false;
   bool isInterface = false;
   TR::RecognizedMethod rm = callee->getRecognizedMethod();
   switch (rm)
      {
      // refine the ILGenMacros_invokeExact* callees
      case TR::java_lang_invoke_ILGenMacros_invokeExact:
      case TR::java_lang_invoke_ILGenMacros_invokeExact_X:
      case TR::java_lang_invoke_ILGenMacros_invokeExactAndFixup:
         {
         int argNum = callee->numberOfExplicitParameters();
         if (argNum > 0)
            {
            Operand *operand = topn(argNum-1); // for the ILGenMacros_invokeExact* methods, the first argument is always the methodhandle object
            MutableCallsiteTargetOperand * mcsOperand = operand->asMutableCallsiteTargetOperand();
            if (mcsOperand)
               {
               mhIndex = mcsOperand->getMethodHandleIndex();
               mcsIndex = mcsOperand->getMutableCallsiteIndex();
               }
            else
               mhIndex = operand->getKnownObjectIndex();
            }

         if (mhIndex != TR::KnownObjectTable::UNKNOWN)
            {
            debugTrace(tracer(), "refine java_lang_invoke_MethodHandle_invokeExact with obj%d to archetype specimen at bcIndex=%d\n", mhIndex, _bcIndex);
            callee = comp()->fej9()->createMethodHandleArchetypeSpecimen(this->trMemory(), comp()->getKnownObjectTable()->getPointerLocation(mhIndex), _calltarget->_calleeMethod);
            }
         return;
         }
      // refine the leaf method handle callees
      case TR::java_lang_invoke_InterfaceHandle_interfaceCall:
         isInterface = true;
      case TR::java_lang_invoke_VirtualHandle_virtualCall:
         isVirtual = !isInterface;
         isIndirectCall = true;
      case TR::java_lang_invoke_DirectHandle_directCall:
         {
         isIndirectCall = false;
         TR_OpaqueMethodBlock *j9method;
         int64_t vmSlot = 0;
         uintptr_t jlClass = 0;
         TR_J9VMBase *fej9 = comp()->fej9();
            {
            TR::KnownObjectTable *knot = comp()->getOrCreateKnownObjectTable();
#if defined(J9VM_OPT_JITSERVER)
            if (comp()->isOutOfProcessCompilation())
               {
               bool knotEnabled = (knot != NULL);
               uintptr_t *methodHandleLocation = _calltarget->_calleeMethod->getMethodHandleLocation();
               auto stream = TR::CompilationInfo::getStream();
               stream->write(JITServer::MessageType::KnownObjectTable_invokeDirectHandleDirectCall, methodHandleLocation, knotEnabled);

               auto recv = stream->read<int64_t, uintptr_t, TR::KnownObjectTable::Index, uintptr_t*>();
               vmSlot = std::get<0>(recv);
               jlClass = std::get<1>(recv);
               TR::KnownObjectTable::Index resultIndex = std::get<2>(recv);
               uintptr_t *objectPointerReference = std::get<3>(recv);

               if (knot && (resultIndex != TR::KnownObjectTable::UNKNOWN))
                  {
                  knot->updateKnownObjectTableAtServer(resultIndex, objectPointerReference);
                  }

               debugTrace(tracer(), "refine resolved method for leaf methodHandle [obj%d]\n", resultIndex);
               }
            else
#endif /* defined(J9VM_OPT_JITSERVER) */
               {
               TR::VMAccessCriticalSection invokeDirectHandleDirectCall(fej9);
               uintptr_t methodHandle = *_calltarget->_calleeMethod->getMethodHandleLocation();
               vmSlot = fej9->getInt64Field(methodHandle, "vmSlot");
               jlClass = fej9->getReferenceField(methodHandle, "defc", "Ljava/lang/Class;");
               debugTrace(tracer(), "refine resolved method for leaf methodHandle [obj%d]\n", knot ? knot->getOrCreateIndex(methodHandle) : -1);
               }

            if (isInterface)
               {
               TR_OpaqueClassBlock *clazz = fej9->getClassFromJavaLangClass(jlClass);
               j9method = (TR_OpaqueMethodBlock*)&(((J9Class *)clazz)->ramMethods[vmSlot]);
               }
            else if (isVirtual)
               {
               TR_OpaqueMethodBlock **vtable = (TR_OpaqueMethodBlock**)(((uintptr_t)fej9->getClassFromJavaLangClass(jlClass)) + J9JIT_INTERP_VTABLE_OFFSET);
               int32_t index = (int32_t)((vmSlot - J9JIT_INTERP_VTABLE_OFFSET) / sizeof(vtable[0]));
               j9method = vtable[index];
               }
            else
               {
               j9method = (TR_OpaqueMethodBlock*)(intptr_t)vmSlot;
               }
            }
         TR_ASSERT(j9method, "Must have a j9method to generate a custom call");
         callee = fej9->createResolvedMethod(this->trMemory(), j9method);
         return;
         }
      case TR::java_lang_invoke_MethodHandle_linkToStatic:
      case TR::java_lang_invoke_MethodHandle_linkToSpecial:
      case TR::java_lang_invoke_MethodHandle_linkToVirtual:
         {
         TR::KnownObjectTable::Index memberNameIndex = top()->getKnownObjectIndex();
         TR_J9VMBase* fej9 = comp()->fej9();
         auto targetMethod = fej9->targetMethodFromMemberName(comp(), memberNameIndex);
         if (!targetMethod) return;

         uint32_t vTableSlot = 0;
         if (rm == TR::java_lang_invoke_MethodHandle_linkToVirtual)
            vTableSlot = fej9->vTableOrITableIndexFromMemberName(comp(), memberNameIndex);

         callee = fej9->createResolvedMethod(comp()->trMemory(), vTableSlot, targetMethod, _calltarget->_calleeMethod);
         isIndirectCall = rm == TR::java_lang_invoke_MethodHandle_linkToVirtual || rm == TR::java_lang_invoke_MethodHandle_linkToInterface;
         heuristicTrace(tracer(), "Refined linkTo\n");
         // The refined method doesn't take MemberName as an argument
         pop();
         }
      }
   }

bool InterpreterEmulator::hasByteCodeRequireState()
   {
   TR_J9ByteCode bc = first();
   while (bc != J9BCunknown)
      {
      switch (bc)
         {
         case J9BCinvokedynamic:
         case J9BCinvokehandle:
            // liqun: TODO: only return true if call is resolved
            return true;
         }
      bc = next();
      }
   return false;
   }

bool
InterpreterEmulator::findAndCreateCallsitesFromBytecodes(bool wasPeekingSuccessfull, bool withState)
   {
   debugTrace(tracer(),"With state %d\n", withState);
   TR::Region findCallsitesRegion(comp()->region());
   if (withState || hasByteCodeRequireState())
      initializeIteratorWithState();
   _wasPeekingSuccessfull = wasPeekingSuccessfull;
   _currentInlinedBlock = NULL;
   TR_J9ByteCode bc = first();
   while (bc != J9BCunknown)
      {
      if (_InterpreterEmulatorFlags[_bcIndex].testAny(InterpreterEmulator::BytecodePropertyFlag::bbStart))
         {
         _currentInlinedBlock = TR_J9EstimateCodeSize::getBlock(comp(), _blocks, _calltarget->_calleeMethod, _bcIndex, *_cfg);
         debugTrace(tracer(),"Found current block %p, number %d for bci %d\n", _currentInlinedBlock, (_currentInlinedBlock) ? _currentInlinedBlock->getNumber() : -1, _bcIndex);
         }


      TR_ASSERT_FATAL(!isGenerated(_bcIndex), "InterpreterEmulator::findCallsitesFromBytecodes bcIndex %d has been generated\n", _bcIndex);
      _newBCInfo->setByteCodeIndex(_bcIndex);

      switch (bc)
         {
         case J9BCinvokedynamic: visitInvokedynamic(); break;
         case J9BCinvokevirtual: visitInvokevirtual(); break;
         case J9BCinvokespecial:
         case J9BCinvokespecialsplit: visitInvokespecial(); break;
         case J9BCinvokestatic:
         case J9BCinvokestaticsplit: visitInvokestatic(); break;
         case J9BCinvokeinterface: visitInvokeinterface(); break;
         }

      if (_iteratorWithState)
         {
         if (maintainStack(bc))
            dumpStack();
         else
            return false;
         }

      _pca.updateArg(bc);
      bc = findNextByteCodeToVisit();
      }
   return true;
   }

TR_J9ByteCode
InterpreterEmulator::findNextByteCodeToVisit()
   {
   if (!_iteratorWithState)
      next();
   else
      {
      setIsGenerated(_bcIndex);
      if (_InterpreterEmulatorFlags[_bcIndex].testAny(InterpreterEmulator::BytecodePropertyFlag::isBranch))
         {
         setIndex(Base::findNextByteCodeToGen());
         debugTrace(tracer(), "current bc is branch next bytecode to generate is %d\n", _bcIndex);
         }
      else next();
      }

   if (_InterpreterEmulatorFlags[_bcIndex].testAny(InterpreterEmulator::BytecodePropertyFlag::bbStart))
      {
      if (isGenerated(_bcIndex))
         setIndex(Base::findNextByteCodeToGen());
      }
   return current();
   }

void
InterpreterEmulator::prepareToFindAndCreateCallsites(TR::Block **blocks, flags8_t * flags, TR_CallSite ** callSites, TR::CFG *cfg, TR_ByteCodeInfo *newBCInfo, int32_t recursionDepth, TR_CallStack *callStack)
   {
   _blocks = blocks;
   _InterpreterEmulatorFlags = flags;
   _callSites = callSites;
   _cfg = cfg;
   _newBCInfo = newBCInfo;
   _recursionDepth = recursionDepth;
   _callStack = callStack;
   _nonColdCallExists = false;
   _inlineableCallExists = false;
   }

void
InterpreterEmulator::visitInvokedynamic()
   {
   int32_t cpIndex = next2Bytes();
   bool isInterface = false;
   bool isIndirectCall = false;
   TR::Method *interfaceMethod = 0;
   TR::TreeTop *callNodeTreeTop = 0;
   TR::Node *parent = 0;
   TR::Node *callNode = 0;
   TR::ResolvedMethodSymbol *resolvedSymbol = 0;
   Operand *result = NULL;

   TR_ResolvedMethod * owningMethod = _methodSymbol->getResolvedMethod();
   TR::KnownObjectTable *knot = comp()->getOrCreateKnownObjectTable();
   if (knot && !owningMethod->isUnresolvedCallSiteTableEntry(cpIndex))
      {
      isIndirectCall = true;
      uintptr_t *entryLocation = (uintptr_t*)owningMethod->callSiteTableEntryAddress(cpIndex);
      // Add callsite handle to known object table
      knot->getOrCreateIndexAt((uintptr_t*)entryLocation);
      TR_ResolvedMethod * resolvedMethod = comp()->fej9()->createMethodHandleArchetypeSpecimen(this->trMemory(), entryLocation, owningMethod);
      bool allconsts= false;

      heuristicTrace(tracer(),"numberOfExplicitParameters = %d  _pca.getNumPrevConstArgs = %d\n", resolvedMethod->numberOfExplicitParameters() , _pca.getNumPrevConstArgs(resolvedMethod->numberOfExplicitParameters()));
      if (resolvedMethod->numberOfExplicitParameters() > 0 && resolvedMethod->numberOfExplicitParameters() <= _pca.getNumPrevConstArgs(resolvedMethod->numberOfExplicitParameters()))
         allconsts = true;

      TR_CallSite *callsite = new (comp()->trHeapMemory()) TR_J9MethodHandleCallSite(_calltarget->_calleeMethod, callNodeTreeTop,   parent,
                                                                        callNode, interfaceMethod, resolvedMethod->classOfMethod(),
                                                                        -1, cpIndex, resolvedMethod,
                                                                        resolvedSymbol, isIndirectCall, isInterface, *_newBCInfo, comp(),
                                                                        _recursionDepth, allconsts);

      findTargetAndUpdateInfoForCallsite(callsite);
      }
   }

#if defined(J9VM_OPT_OPENJDK_METHODHANDLE)
void
InterpreterEmulator::visitInvokehandle()
   {

   bool isInterface = false;
   bool isIndirectCall = false;
   TR::Method *interfaceMethod = 0;
   TR::TreeTop *callNodeTreeTop = 0;
   TR::Node *parent = 0;
   TR::Node *callNode = 0;
   TR::ResolvedMethodSymbol *resolvedSymbol = 0;
   Operand *result = NULL;
   int32_t cpIndex = next2Bytes();
   TR_ResolvedMethod * owningMethod = _methodSymbol->getResolvedMethod();

   J9InvokeCacheEntry *invokeCache = (J9InvokeCacheEntry *) owningMethod->methodTypeTableEntryAddress(cpIndex);
   if (!invokeCache) return; // unresolved

   // add appendix object to knot and push to stack
   TR::KnownObjectTable *knot = comp()->getOrCreateKnownObjectTable();
   if (knot) push(new (trStackMemory()) KnownObjOperand(knot->getOrCreateIndexAt((uintptr_t*) (&invokeCache->appendix))));

   TR_J9VMBase *fej9 = comp()->fej9();
   TR_OpaqueMethodBlock * targetMethodObj = 0;
      {
      TR::VMAccessCriticalSection vmAccess(fej9);
      targetMethodObj = fej9->targetMethodFromMemberName((uintptr_t) invokeCache->target);
      }
   TR_ResolvedMethod * targetMethod = fej9->createResolvedMethod(this->trMemory(), targetMethodObj, owningMethod);
   targetMethod->convertToMethod()->setAdapterOrLambdaForm();

   bool allconsts = false;
   if (targetMethod->numberOfExplicitParameters() > 0 && targetMethod->numberOfExplicitParameters() <= _pca.getNumPrevConstArgs(targetMethod->numberOfExplicitParameters()))
         allconsts = true;
   TR_CallSite *callsite = new (comp()->trHeapMemory()) TR_DirectCallSite(_calltarget->_calleeMethod, callNodeTreeTop,   parent,
                                                                        callNode, interfaceMethod, targetMethod->classOfMethod(),
                                                                        -1, cpIndex, targetMethod,
                                                                        resolvedSymbol, isIndirectCall, isInterface, *_newBCInfo, comp(),
                                                                        _recursionDepth, allconsts);

   findTargetAndUpdateInfoForCallsite(callsite);

>>>>>>> ec40b8d9e0... Inline MethodHandle chain
   }

bool
InterpreterEmulator::isCurrentCallUnresolvedOrCold(TR_ResolvedMethod *resolvedMethod, bool isUnresolvedInCP)
   {
   bool isIndirectCall = false;
   if (current() == J9BCinvokevirtual)
      isIndirectCall = true;
   return (!resolvedMethod || isUnresolvedInCP || resolvedMethod->isCold(comp(), isIndirectCall));
   }

void
InterpreterEmulator::debugUnresolvedOrCold(TR_ResolvedMethod *resolvedMethod)
   {
   int32_t cpIndex = next2Bytes();
   if(tracer()->heuristicLevel())
      {
      if (resolvedMethod)
         heuristicTrace(tracer(), "Depth %d: Call at bc index %d is Cold.  Not searching for targets. Signature %s", _recursionDepth, _bcIndex, resolvedMethod->signature(comp()->trMemory()));
      else
         {
         switch (current())
            {
            case J9BCinvokespecialsplit:
               cpIndex |= J9_SPECIAL_SPLIT_TABLE_INDEX_FLAG;
               break;
            case J9BCinvokestaticsplit:
               cpIndex |= J9_STATIC_SPLIT_TABLE_INDEX_FLAG;
               break;
            }
         TR::Method *meth = comp()->fej9()->createMethod(this->trMemory(), _calltarget->_calleeMethod->containingClass(), cpIndex);
         heuristicTrace(tracer(), "Depth %d: Call at bc index %d is Cold.  Not searching for targets. Signature %s", _recursionDepth, _bcIndex, meth->signature(comp()->trMemory()));
         }
      }
   }

// liqun: TODO: merge this with refineResolvedCalleeForInvokestatic
TR_ResolvedMethod*
InterpreterEmulator::refineCall(TR_ResolvedMethod* resolvedMethod)
   {
   if (resolvedMethod->getRecognizedMethod() == TR::java_lang_invoke_MethodHandle_invokeBasic)
      {
      heuristicTrace(tracer(), "Refining invokeBasic\n");
      int argNum = resolvedMethod->numberOfExplicitParameters();
      TR::KnownObjectTable::Index receiverIndex = topn(argNum)->getKnownObjectIndex();
      TR_J9VMBase* fej9 = comp()->fej9();
      auto targetMethod = fej9->targetMethodFromMethodHandle(comp(), receiverIndex);
      if (!targetMethod) return NULL;

      auto refinedMethod = fej9->createResolvedMethod(comp()->trMemory(), targetMethod, _calltarget->_calleeMethod);
      refinedMethod->convertToMethod()->setAdapterOrLambdaForm();
      heuristicTrace(tracer(), "Refined invokeBasic\n");
      return refinedMethod;
      }

   return NULL;
   }

void
InterpreterEmulator::visitInvokevirtual()
   {
   int32_t cpIndex = next2Bytes();
   auto calleeMethod = (TR_ResolvedJ9Method*)_calltarget->_calleeMethod;
   bool isUnresolvedInCP;
   TR_ResolvedMethod * resolvedMethod = calleeMethod->getResolvedPossiblyPrivateVirtualMethod(comp(), cpIndex, true, &isUnresolvedInCP);
   Operand *result = NULL;
   if (isCurrentCallUnresolvedOrCold(resolvedMethod, isUnresolvedInCP))
      {
      debugUnresolvedOrCold(resolvedMethod);
      }
   else if (resolvedMethod)
      {
      auto refinedMethod = refineCall(resolvedMethod);
      if (refinedMethod)
         resolvedMethod = refinedMethod;

      bool allconsts= false;
      heuristicTrace(tracer(),"numberOfExplicitParameters = %d  _pca.getNumPrevConstArgs = %d\n",resolvedMethod->numberOfExplicitParameters() ,_pca.getNumPrevConstArgs(resolvedMethod->numberOfExplicitParameters()));
      if ( resolvedMethod->numberOfExplicitParameters() > 0 && resolvedMethod->numberOfExplicitParameters() <= _pca.getNumPrevConstArgs(resolvedMethod->numberOfExplicitParameters()))
         allconsts = true;

      TR_CallSite *callsite;
      bool isIndirectCall = resolvedMethod->isStatic() ? false :
                                                         resolvedMethod == NULL || (!resolvedMethod->isFinal() && !resolvedMethod->isPrivate());
      bool isInterface = false;
      TR::Method *interfaceMethod = 0;
      TR::TreeTop *callNodeTreeTop = 0;
      TR::Node *parent = 0;
      TR::Node *callNode = 0;
      TR::ResolvedMethodSymbol *resolvedSymbol = 0;

      if (resolvedMethod->convertToMethod()->isArchetypeSpecimen() && resolvedMethod->getMethodHandleLocation())
         {
         callsite = new (comp()->trHeapMemory()) TR_J9MethodHandleCallSite(_calltarget->_calleeMethod, callNodeTreeTop,   parent,
                                                                        callNode, interfaceMethod, resolvedMethod->classOfMethod(),
                                                                        -1, cpIndex, resolvedMethod,
                                                                        resolvedSymbol, isIndirectCall, isInterface, *_newBCInfo, comp(),
                                                                        _recursionDepth, allconsts);
         }
      else if (resolvedMethod->getRecognizedMethod() == TR::java_lang_invoke_MethodHandle_invokeExact)
         {
         callsite = new (comp()->trHeapMemory()) TR_J9MutableCallSite(_calltarget->_calleeMethod, callNodeTreeTop,   parent,
                                                      callNode, interfaceMethod, resolvedMethod->classOfMethod(),
                                                      (int32_t) resolvedMethod->virtualCallSelector(cpIndex), cpIndex, resolvedMethod,
                                                      resolvedSymbol, isIndirectCall, isInterface, *_newBCInfo, comp(),
                                                      _recursionDepth, allconsts);
         }
      else if (isIndirectCall)
         {
         callsite = new (comp()->trHeapMemory()) TR_J9VirtualCallSite(_calltarget->_calleeMethod, callNodeTreeTop, parent,
                                                                        callNode, interfaceMethod, resolvedMethod->classOfMethod(),
                                                                        (int32_t) resolvedMethod->virtualCallSelector(cpIndex), cpIndex, resolvedMethod,
                                                                        resolvedSymbol, isIndirectCall, isInterface, *_newBCInfo, comp(),
                                                                        _recursionDepth, allconsts);

         }
      else
         {
         callsite = new (comp()->trHeapMemory()) TR_DirectCallSite(_calltarget->_calleeMethod, callNodeTreeTop, parent,
                                                                        callNode, interfaceMethod, resolvedMethod->classOfMethod(),
                                                                        -1, cpIndex, resolvedMethod,
                                                                        resolvedSymbol, isIndirectCall, isInterface, *_newBCInfo, comp(),
                                                                        _recursionDepth, allconsts);

         }

      if(tracer()->debugLevel())
         _pca.printIndexes(comp());
      findTargetAndUpdateInfoForCallsite(callsite);
      }

   if (_iteratorWithState)
      maintainStackForCall(_calltarget->_calleeMethod, getReturnValueForInvokestatic(resolvedMethod), resolvedMethod->numberOfParameters(), resolvedMethod->returnType());
   }

void
InterpreterEmulator::visitInvokespecial()
   {
   int32_t cpIndex = next2Bytes();
   bool isUnresolvedInCP;
   TR_ResolvedMethod *resolvedMethod = _calltarget->_calleeMethod->getResolvedSpecialMethod(comp(), (current() == J9BCinvokespecialsplit)?cpIndex |= J9_SPECIAL_SPLIT_TABLE_INDEX_FLAG:cpIndex, &isUnresolvedInCP);
   if (isCurrentCallUnresolvedOrCold(resolvedMethod, isUnresolvedInCP))
      {
      debugUnresolvedOrCold(resolvedMethod);
      }
   else
      {
      bool allconsts= false;
      heuristicTrace(tracer(),"numberOfExplicitParameters = %d  _pca.getNumPrevConstArgs = %d\n",resolvedMethod->numberOfExplicitParameters() ,_pca.getNumPrevConstArgs(resolvedMethod->numberOfExplicitParameters()));
      if (resolvedMethod->numberOfExplicitParameters() > 0 && resolvedMethod->numberOfExplicitParameters() <= _pca.getNumPrevConstArgs(resolvedMethod->numberOfExplicitParameters()))
         allconsts = true;

      bool isIndirectCall = false;
      bool isInterface = false;
      TR::Method *interfaceMethod = 0;
      TR::TreeTop *callNodeTreeTop = 0;
      TR::Node *parent = 0;
      TR::Node *callNode = 0;
      TR::ResolvedMethodSymbol *resolvedSymbol = 0;
      TR_CallSite *callsite = new (comp()->trHeapMemory()) TR_DirectCallSite(_calltarget->_calleeMethod, callNodeTreeTop, parent,
                                                                        callNode, interfaceMethod, resolvedMethod->classOfMethod(), -1, cpIndex,
                                                                        resolvedMethod, resolvedSymbol, isIndirectCall, isInterface, *_newBCInfo, comp(),
                                                                        _recursionDepth, allconsts);
      findTargetAndUpdateInfoForCallsite(callsite);
      }
   }

void
InterpreterEmulator::visitInvokestatic()
   {
   int32_t cpIndex = next2Bytes();
   bool isUnresolvedInCP;
   TR_ResolvedMethod *resolvedMethod = _calltarget->_calleeMethod->getResolvedStaticMethod(comp(), (current() == J9BCinvokestaticsplit) ? cpIndex |= J9_STATIC_SPLIT_TABLE_INDEX_FLAG:cpIndex, &isUnresolvedInCP);
   TR_ResolvedMethod *origResolvedMethod = resolvedMethod;
   if (isCurrentCallUnresolvedOrCold(resolvedMethod, isUnresolvedInCP))
      {
      debugUnresolvedOrCold(resolvedMethod);
      }
   else
      {
      bool allconsts= false;

      heuristicTrace(tracer(),"numberOfExplicitParameters = %d  _pca.getNumPrevConstArgs = %d\n",resolvedMethod->numberOfExplicitParameters() ,_pca.getNumPrevConstArgs(resolvedMethod->numberOfExplicitParameters()));
      if (resolvedMethod->numberOfExplicitParameters() > 0 && resolvedMethod->numberOfExplicitParameters() <= _pca.getNumPrevConstArgs(resolvedMethod->numberOfExplicitParameters()))
         allconsts = true;

      TR::KnownObjectTable::Index mhIndex = TR::KnownObjectTable::UNKNOWN;
      TR::KnownObjectTable::Index mcsIndex = TR::KnownObjectTable::UNKNOWN;
      bool isIndirectCall = false;
      if (_iteratorWithState)
         refineResolvedCalleeForInvokestatic(resolvedMethod, mcsIndex, mhIndex, isIndirectCall);

      bool isInterface = false;
      TR_CallSite *callsite = NULL;
      TR::Method *interfaceMethod = 0;
      TR::TreeTop *callNodeTreeTop = 0;
      TR::Node *parent = 0;
      TR::Node *callNode = 0;
      TR::ResolvedMethodSymbol *resolvedSymbol = 0;

      if (resolvedMethod->convertToMethod()->isArchetypeSpecimen() &&
            resolvedMethod->getMethodHandleLocation() &&
            mcsIndex == TR::KnownObjectTable::UNKNOWN)
         {
         callsite = new (comp()->trHeapMemory()) TR_J9MethodHandleCallSite( _calltarget->_calleeMethod, callNodeTreeTop,   parent,
               callNode, interfaceMethod, resolvedMethod->classOfMethod(),
               -1, cpIndex, resolvedMethod,
               resolvedSymbol, isIndirectCall, isInterface, *_newBCInfo, comp(),
               _recursionDepth, allconsts);
         }
      else if (resolvedMethod->convertToMethod()->isArchetypeSpecimen() &&
            resolvedMethod->getMethodHandleLocation() &&
            mcsIndex != TR::KnownObjectTable::UNKNOWN)
         {
         TR_J9MutableCallSite *mcs = new (comp()->trHeapMemory()) TR_J9MutableCallSite( _calltarget->_calleeMethod, callNodeTreeTop,   parent,
               callNode, interfaceMethod, resolvedMethod->classOfMethod(),
               (int32_t) resolvedMethod->virtualCallSelector(cpIndex), cpIndex, resolvedMethod,
               resolvedSymbol, isIndirectCall, isInterface, *_newBCInfo, comp(),
               _recursionDepth, allconsts);
         if (mcsIndex != TR::KnownObjectTable::UNKNOWN)
            {
            if (comp()->getKnownObjectTable())
               mcs->setMCSReferenceLocation(comp()->getKnownObjectTable()->getPointerLocation(mcsIndex));
            }
         callsite = mcs;
         }
      else if (isIndirectCall)
         {
         callsite = new (comp()->trHeapMemory()) TR_J9VirtualCallSite(
               _calltarget->_calleeMethod, callNodeTreeTop, parent, callNode,
               interfaceMethod, resolvedMethod->classOfMethod(), (int32_t) resolvedMethod->virtualCallSelector(cpIndex), cpIndex,
               resolvedMethod, resolvedSymbol, isIndirectCall, isInterface,
               *_newBCInfo, comp(), _recursionDepth, allconsts);
         }
      else
         {
         callsite = new (comp()->trHeapMemory()) TR_DirectCallSite(_calltarget->_calleeMethod, callNodeTreeTop, parent, callNode, interfaceMethod,
               resolvedMethod->classOfMethod(), -1, cpIndex, resolvedMethod, resolvedSymbol,
               isIndirectCall, isInterface, *_newBCInfo, comp(),
               _recursionDepth, allconsts);
         }
      findTargetAndUpdateInfoForCallsite(callsite);
      }

   if (_iteratorWithState)
      maintainStackForCall(_calltarget->_calleeMethod, getReturnValueForInvokestatic(resolvedMethod), resolvedMethod->numberOfParameters(), resolvedMethod->returnType());
   }

void
InterpreterEmulator::visitInvokeinterface()
   {
   int32_t cpIndex = next2Bytes();
   auto calleeMethod = (TR_ResolvedJ9Method*)_calltarget->_calleeMethod;
   TR_ResolvedMethod *resolvedMethod = calleeMethod->getResolvedImproperInterfaceMethod(comp(), cpIndex);
   bool isIndirectCall = true;
   bool isInterface = true;
   if (resolvedMethod)
      {
      isInterface = false;
      isIndirectCall = !resolvedMethod->isPrivate() &&
                       !resolvedMethod->convertToMethod()->isFinalInObject();
      }

   TR::Method * interfaceMethod = NULL;
   if (isInterface)
      interfaceMethod = comp()->fej9()->createMethod(this->trMemory(), _calltarget->_calleeMethod->containingClass(), cpIndex);

   TR::TreeTop *callNodeTreeTop = 0;
   TR::Node *parent = 0;
   TR::Node *callNode = 0;
   TR::ResolvedMethodSymbol *resolvedSymbol = 0;

   uint32_t explicitParams = 0;
   if (isInterface)
      explicitParams = interfaceMethod->numberOfExplicitParameters();
   else
      explicitParams = resolvedMethod->numberOfExplicitParameters();

   bool allconsts= false;
   heuristicTrace(tracer(), "numberOfExplicitParameters = %d  _pca.getNumPrevConstArgs = %d\n", explicitParams, _pca.getNumPrevConstArgs(explicitParams));
   if (explicitParams > 0 && explicitParams <= _pca.getNumPrevConstArgs(explicitParams))
      allconsts = true;

   TR_CallSite *callsite = NULL;
   if (isInterface)
      {
      TR_OpaqueClassBlock * thisClass = NULL;
      callsite = new (comp()->trHeapMemory()) TR_J9InterfaceCallSite(
         _calltarget->_calleeMethod, callNodeTreeTop, parent, callNode,
         interfaceMethod, thisClass, -1, cpIndex, resolvedMethod,
         resolvedSymbol, isIndirectCall, isInterface, *_newBCInfo,
         comp(), _recursionDepth, allconsts);
      }
   else if (isIndirectCall)
      {
      callsite = new (comp()->trHeapMemory()) TR_J9VirtualCallSite(
         _calltarget->_calleeMethod, callNodeTreeTop, parent, callNode,
         interfaceMethod, resolvedMethod->classOfMethod(), (int32_t) resolvedMethod->virtualCallSelector(cpIndex), cpIndex,
         resolvedMethod, resolvedSymbol, isIndirectCall, isInterface,
         *_newBCInfo, comp(), _recursionDepth, allconsts);
      }
   else
      {
      callsite = new (comp()->trHeapMemory()) TR_DirectCallSite(
         _calltarget->_calleeMethod, callNodeTreeTop, parent, callNode,
         interfaceMethod, resolvedMethod->classOfMethod(), -1, cpIndex,
         resolvedMethod, resolvedSymbol, isIndirectCall, isInterface,
         *_newBCInfo, comp(), _recursionDepth, allconsts);
      }

   if(tracer()->debugLevel())
      {
      _pca.printIndexes(comp());
      }
   findTargetAndUpdateInfoForCallsite(callsite);
   }

TR_PrexArgument*
InterpreterEmulator::createPrexArgFromOperand(Operand* operand)
   {
   if (operand->asKnownObject())
      {
      return new (comp()->trHeapMemory()) TR_PrexArgument(operand->getKnownObjectIndex(), comp());
      }
   else if (operand->asClassOperand())
      {
      TR_OpaqueClassBlock* clazz = operand->asClassOperand()->getClass();
      TR_PrexArgument::ClassKind kind = TR_PrexArgument::ClassIsUnknown;
      if (operand->asFixedClassOperand())
         kind = TR_PrexArgument::ClassIsFixed;
      else if (operand->asPrexClassOperand())
         kind = TR_PrexArgument::ClassIsPreexistent;

      return new (comp()->trHeapMemory()) TR_PrexArgument(kind, clazz);
      }

   return NULL;
   }

// liqun: can't propagate receiver for static method
// this is a problem. We should propagate arg info for any method and any arg
// we should propagate arg info even if peeking is not successfull
// Or no need to propagate, since we've walked through the bytecodes and maintained
// the stack and auto slots, we know what the arguments are
void
InterpreterEmulator::findTargetAndUpdateInfoForCallsite(TR_CallSite *callsite)
   {
   callsite->_callerBlock = _currentInlinedBlock;

   int32_t numOfArgs = 0;
   if (callsite->_isInterface)
      {
      numOfArgs = callsite->_interfaceMethod->numberOfExplicitParameters() + 1;
      }
   else if (callsite->_initialCalleeMethod)
      {
      numOfArgs = callsite->_initialCalleeMethod->numberOfParameters();
      }

   if (_iteratorWithState)
      {
      // Get arg info from stack
      if (!callsite->_ecsPrexArgInfo)
         {
         // liqun: todo: should it be stack memory?
         callsite->_ecsPrexArgInfo = new (comp()->trHeapMemory()) TR_PrexArgInfo(numOfArgs, comp()->trMemory());
         }

      for (int32_t i = 0; i < numOfArgs; i++)
         {
         int32_t posInStack = numOfArgs - i - 1;
         callsite->_ecsPrexArgInfo->set(i, createPrexArgFromOperand(topn(posInStack)));
         }

      if (tracer()->heuristicLevel())
         {
         alwaysTrace(tracer(), "argInfo from operand stack:");
         if (callsite->_ecsPrexArgInfo)
            callsite->_ecsPrexArgInfo->dumpTrace();
         }

      if (_ecs->isInlineable(_callStack, callsite))
         {
         _callSites[_bcIndex] = callsite;
         _inlineableCallExists = true;

         // Improve prex argInfo of call targets
         for (int j = 0; j < callsite->numTargets(); j++)
            {
            TR_CallTarget* callSiteTarget = callsite->getTarget(j);
            if (!callSiteTarget->_ecsPrexArgInfo)
               continue;

            TR_PrexArgInfo* targetArgInfo = callSiteTarget->_ecsPrexArgInfo;
            TR_PrexArgInfo* callSiteArgInfo = callsite->_ecsPrexArgInfo;
            callSiteTarget->_ecsPrexArgInfo = TR_PrexArgInfo::enhance(targetArgInfo, callSiteArgInfo, comp());
            }

         if (tracer()->heuristicLevel())
            {
            alwaysTrace(tracer(), "propagateArgs :");
            if (callsite->numTargets() && callsite->getTarget(0)->_ecsPrexArgInfo)
               callsite->getTarget(0)->_ecsPrexArgInfo->dumpTrace();
            }

         if (!_currentInlinedBlock->isCold())
               _nonColdCallExists = true;

         for (int i = 0; i < callsite->numTargets(); i++)
            callsite->getTarget(i)->_originatingBlock = _currentInlinedBlock;
         }
      else
         {
         //support counters
         _calltarget->addDeadCallee(callsite);
         }
     return;
      }

   // No _initialCalleeMethod means the method is interface
   if (!callsite->_initialCalleeMethod || !callsite->_initialCalleeMethod->isStatic())
      {
      if (_wasPeekingSuccessfull)
         {
         TR_PrexArgInfo::propagateReceiverInfoIfAvailable(_methodSymbol, callsite, _calltarget->_ecsPrexArgInfo, tracer());
         if (tracer()->heuristicLevel())
            {
            alwaysTrace(tracer(), "propagateReceiverInfoIfAvailable :");
            if (callsite->_ecsPrexArgInfo)
               callsite->_ecsPrexArgInfo->dumpTrace();
            }
         }
      }

   if (_ecs->isInlineable(_callStack, callsite))
      {
      _callSites[_bcIndex] = callsite;
      _inlineableCallExists = true;

      if (_wasPeekingSuccessfull)
         {
         TR_PrexArgInfo::propagateArgsFromCaller(_methodSymbol, callsite, _calltarget->_ecsPrexArgInfo, tracer());
         if (tracer()->heuristicLevel())
            {
            alwaysTrace(tracer(), "propagateArgs :");
            if (callsite->numTargets() && callsite->getTarget(0)->_ecsPrexArgInfo)
               callsite->getTarget(0)->_ecsPrexArgInfo->dumpTrace();
            }
         }

      if (!_currentInlinedBlock->isCold())
            _nonColdCallExists = true;

      for (int i = 0; i < callsite->numTargets(); i++)
         callsite->getTarget(i)->_originatingBlock = _currentInlinedBlock;
      }
   else
      {
      //support counters
      _calltarget->addDeadCallee(callsite);
      }
   }
