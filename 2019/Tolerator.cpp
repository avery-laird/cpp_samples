// Jan 28, 2021
// This code was written in 2019 for a class project. It implements the Tolerator
// module pass. It traverses an LLVM module and instruments it with certain
// instructions depending on the analysis level.
// On the stricter level, it will operate similar to a sanitizer, and the program
// will quit immediately when errors are found (checks loads, stores, frees, and
// division by 0).
// On the most tolerant level, the runtime will attempt to bypass errors and
// substitute a "reasonable" value.
// For example, if a division by 0 occurs, the runtime will return a null value
// based on the return type of the failing function (see handleDivision below).

#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/Transforms/Utils/ModuleUtils.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "Tolerator.h"
#include <list>

// Begin instructor code
using namespace llvm;
using tolerator::Tolerator;


namespace tolerator {

char Tolerator::ID = 0;

}
// End instructor code


bool
is_interesting(Instruction *inst) {
    if (isa<AllocaInst>(inst) ||
        isa<LoadInst>(inst) ||
        isa<StoreInst>(inst)  ||
        isa<SDivOperator>(inst) ||
        isa<UDivOperator>(inst))
        return true;
    if (isa<CallInst>(inst)) {
        auto called = dyn_cast<CallInst>(inst)->getCalledValue()->stripPointerCasts();
        if (called->getName().compare(StringRef("free")) == 0 ||
            called->getName().compare(StringRef("malloc")) == 0) {
            return true;
        }
    }
    return false;
}


void
handleDivision(Instruction* inst, IRBuilder<> builder, FunctionCallee handler, Module &m, Tolerator &t) {
    auto intTy = Type::getInt64Ty(m.getContext());
    auto udiv_inst = inst;
    auto* denom = udiv_inst->getOperand(1);
    auto *cast_int = builder.CreateIntCast(denom, intTy, false, "cast_to_int");
    auto *handle_div = builder.CreateCall(handler, {cast_int});


    Instruction* thenterm;
    Instruction* elseterm;
    Instruction* second_inst = inst->getNextNode();
    SplitBlockAndInsertIfThenElse(handle_div, inst->getNextNode(), &thenterm, &elseterm);

    auto* def = Constant::getNullValue(inst->getType());
    auto* func_def = Constant::getNullValue(second_inst->getFunction()->getReturnType());
    builder.SetInsertPoint(second_inst);
    PHINode* PN = builder.CreatePHI(udiv_inst->getType(), 2, "iftmp");
    switch (t.analysis) {
        case tolerator::AnalysisType::IGNORING:
        default:
            inst->moveBefore(thenterm); // allow the div
            CallInst::Create(
                    m.getOrInsertFunction("exit", intTy, intTy),
                    ConstantInt::get(intTy, -1, true), "exit", elseterm);
            udiv_inst->replaceAllUsesWith(PN);
            PN->addIncoming(udiv_inst, inst->getParent());
            PN->addIncoming(def, elseterm->getParent());
            break;
        case tolerator::AnalysisType::DEFAULTING:
            // THEN
            inst->moveBefore(thenterm); // allow valid division
            // ELSE
            inst->replaceAllUsesWith(PN);
            PN->addIncoming(inst, inst->getParent());
            PN->addIncoming(def, elseterm->getParent()); // provide defaults
            break;
        case tolerator::AnalysisType::BYPASSING:
            // THEN
            inst->moveBefore(thenterm);
            // ELSE
            ReturnInst::Create(m.getContext(), func_def, elseterm);
            elseterm->eraseFromParent();
            PN->eraseFromParent();
            break;
    }
}

// Begin instructor code
bool
Tolerator::runOnModule(Module& m) {
  auto& context = m.getContext();
  // End instructor code

  auto* ptrTy = Type::getInt64PtrTy(m.getContext());
  auto* intTy = Type::getInt64Ty(m.getContext());
  auto* voidTy = Type::getVoidTy(m.getContext());
  auto* boolTy = Type::getInt1Ty(m.getContext());
  std::vector<Instruction*> InstList;
  std::vector<Instruction*> InsertPts;
  std::vector<Instruction*> ExitPts;


  for (Function &fun: m) {
      if (fun.isDeclaration()) {
          continue;
      }
      InsertPts.push_back(fun.getEntryBlock().getFirstNonPHIOrDbg());
      for (BasicBlock &bb: fun) {
          for (Instruction &inst : bb) {
              if (is_interesting(&inst)) {
                  InstList.push_back(&inst);
              }
              if (isa<ReturnInst>(inst)) {
                  ExitPts.push_back(&inst);
              }
          }
      }
  }

  auto* allocTy = FunctionType::get(voidTy, {intTy, intTy}, false);
  auto handleAlloc = m.getOrInsertFunction("ToLeRaToR_handle_alloca", allocTy);

  auto handleMalloc = m.getOrInsertFunction("ToLeRaToR_handle_malloc", allocTy);

  auto* storeTy = FunctionType::get(boolTy, {intTy, intTy}, false);
  auto handleStore = m.getOrInsertFunction("ToLeRaToR_handle_store", storeTy);

  auto* loadTy = FunctionType::get(boolTy, {intTy, intTy}, false);
  auto handleLoad = m.getOrInsertFunction("ToLeRaToR_handle_load", loadTy);

  auto* freeTy = FunctionType::get(boolTy, {intTy}, false);
  auto handleFree = m.getOrInsertFunction("ToLeRaToR_handle_free", freeTy);

  auto* divTy = FunctionType::get(boolTy, {intTy}, false);
  auto handleDiv  = m.getOrInsertFunction("ToLeRaToR_handle_div", divTy);

  auto* stackTy = FunctionType::get(voidTy,false);
  auto handlePush = m.getOrInsertFunction("ToLeRaToR_handle_push", stackTy);

  auto handlePop = m.getOrInsertFunction("ToLeRaToR_handle_pop", stackTy);

  auto* globalTy = FunctionType::get(voidTy, {intTy, intTy}, false);
  auto handleGlobal = m.getOrInsertFunction("ToLeRaToR_handle_global", globalTy);

  auto* initGlobalTy = FunctionType::get(voidTy, false);
  auto initGlobal = m.getOrInsertFunction("ToLeRaToR_init_global", initGlobalTy);

  auto data_layout = m.getDataLayout();


  auto *block = BasicBlock::Create(m.getContext());
  IRBuilder<> gbuilder(block);
  for (auto &Global: m.getGlobalList()) {
      Type* GlobalType = Global.getType()->getElementType();
      Type* csiType = IntegerType::getInt32Ty(Global.getContext());
      unsigned TypeSize = data_layout.getTypeAllocSize(Global.getType());
      Value* AllocSize = ConstantInt::get(csiType, TypeSize);

      auto *cast_addr = gbuilder.CreatePointerCast(&Global, intTy);
      auto *cast_size = gbuilder.CreateIntCast(AllocSize, intTy, false);
      gbuilder.CreateCall(handleGlobal, {cast_addr, cast_size});
  }
  auto register_globals = Function::Create(
          FunctionType::get(voidTy, false),
          GlobalValue::LinkageTypes::ExternalLinkage, "register_globals", m);
  block->insertInto(register_globals);
  gbuilder.CreateCall(initGlobal);
  gbuilder.CreateRet(nullptr);
  appendToGlobalCtors(m, register_globals, 0);

  for (auto* inst: InsertPts) {
      IRBuilder<> builder(inst);
      builder.CreateCall(handlePush);
  }

  for (auto* inst: ExitPts) {
      IRBuilder<> builder(inst);
      builder.CreateCall(handlePop);
  }

  for (auto* inst: InstList) {
      if (isa<AllocaInst>(inst)){
          // handle AFTER instruction
          IRBuilder<> builder(inst);
          builder.SetInsertPoint(inst->getNextNode());
          auto* alloc_inst = dyn_cast<AllocaInst>(inst);
          auto* cast_addr = builder.CreatePointerCast(alloc_inst, intTy, "cast_to_int");
          auto* cast_size = builder.CreateIntCast(alloc_inst->getArraySize(), intTy, false, "");

          auto* size_obj = builder.CreateMul(cast_size, ConstantInt::get(intTy, data_layout.getTypeAllocSize(alloc_inst->getAllocatedType())));
          builder.CreateCall(handleAlloc, {cast_addr, size_obj});
          continue;
      }
      if (isa<StoreInst>(inst)) {
          // handle BEFORE instruction
          IRBuilder<> builder(inst);
          //builder.SetInsertPoint(inst->getPrevNode());
          auto *valToStore = inst->getOperand(0);
          auto *storeAddr = inst->getOperand(1);
          auto *cast_addr = builder.CreatePointerCast(storeAddr, intTy, "cast_to_int");
          auto size = data_layout.getTypeStoreSize(valToStore->getType());
          auto size_obj = ConstantInt::get(intTy, size);
          auto* result = builder.CreateCall(handleStore, {cast_addr, size_obj});

          Instruction* thenterm;
          Instruction* elseterm;
          Instruction* second_inst = inst->getNextNode();
          SplitBlockAndInsertIfThenElse(result, second_inst, &thenterm, &elseterm);

          Constant* func_def;
          if (inst->getFunction()->getReturnType() == Type::getVoidTy(m.getContext()))
              func_def = nullptr;
          else
              func_def = Constant::getNullValue(inst->getFunction()->getReturnType());

          switch (this->analysis) {
              default:
                  inst->moveBefore(thenterm); // allow the store
                  CallInst::Create(
                          m.getOrInsertFunction("exit", intTy, intTy),
                          ConstantInt::get(intTy, -1, true), "exit", elseterm);
                  break;
              case tolerator::AnalysisType::IGNORING:
              case tolerator::AnalysisType::DEFAULTING:
                  // branch to first instruction after split
                  inst->moveBefore(thenterm);
                  elseterm = second_inst;
                  break;
              case tolerator::AnalysisType::BYPASSING:
                  // THEN
                  inst->moveBefore(thenterm);
                  // ELSE
                  ReturnInst::Create(m.getContext(), func_def, elseterm);
                  elseterm->eraseFromParent();
                  break;
          }
          continue;
      }
      if (isa<LoadInst>(inst)) {
          // handle BEFORE instruction
          IRBuilder<> builder(inst);

          auto* load_inst = dyn_cast<LoadInst>(inst);

          auto* cast_addr = builder.CreatePointerCast(load_inst->getPointerOperand(), intTy, "cast_to_int");
          auto size = data_layout.getTypeStoreSize(load_inst->getType());
          auto size_obj = ConstantInt::get(intTy, size);
          auto* load_result = builder.CreateCall(handleLoad, {cast_addr, size_obj});

          Instruction* thenterm;
          Instruction* elseterm;
          Instruction* second_inst = inst->getNextNode();
          SplitBlockAndInsertIfThenElse(load_result, second_inst, &thenterm, &elseterm);

          auto* def = Constant::getNullValue(load_inst->getType());
          Constant* func_def;
          if (load_inst->getFunction()->getReturnType() == Type::getVoidTy(m.getContext()))
              func_def = nullptr;
          else
              func_def = Constant::getNullValue(load_inst->getFunction()->getReturnType());
          builder.SetInsertPoint(second_inst);
          PHINode* PN = builder.CreatePHI(load_inst->getType(), 2, "loadtmp");
          switch (this->analysis) {
              case tolerator::AnalysisType::IGNORING:
              default:
                  // THEN
                  inst->moveBefore(thenterm); // allow the load
                  // ELSE
                  CallInst::Create(
                          m.getOrInsertFunction("exit", intTy, intTy),
                          ConstantInt::get(intTy, -1, true), "exit", elseterm);

                  load_inst->replaceAllUsesWith(PN);
                  PN->addIncoming(load_inst, load_inst->getParent());
                  PN->addIncoming(def, elseterm->getParent());
                  break;
              case tolerator::AnalysisType::DEFAULTING:
                  // THEN
                  inst->moveBefore(thenterm); // allow valid stores
                  load_inst->replaceAllUsesWith(PN);
                  PN->addIncoming(load_inst, load_inst->getParent());
                  PN->addIncoming(def, elseterm->getParent());
                  break;
              case tolerator::AnalysisType::BYPASSING:
                  // THEN
                  inst->moveBefore(thenterm);
                  ReturnInst::Create(m.getContext(), func_def, elseterm);
                  elseterm->eraseFromParent();
                  PN->eraseFromParent();
                  break;
          }
          continue;
      }
      if (isa<CallInst>(inst)) {
          // free or malloc
          auto mallocCall = dyn_cast<CallInst>(inst)->getCalledValue()->stripPointerCasts();
          if (mallocCall && mallocCall->getName().compare(StringRef("malloc")) == 0) {
              // handle malloc
              IRBuilder<> builder(inst);
              builder.SetInsertPoint(inst->getNextNode());
              auto malloc_inst = dyn_cast<CallInst>(inst);
              if (!malloc_inst)
                  continue;
              auto* cast_addr = builder.CreatePointerCast(malloc_inst, intTy, "cast_to_int");
              auto size = data_layout.getTypeStoreSize(malloc_inst->getOperand(0)->getType());
              auto size_obj = ConstantInt::get(intTy, size);
              builder.CreateCall(handleMalloc, {cast_addr, size_obj});
              continue;
          }

          auto freeCall = dyn_cast<CallInst>(inst)->getCalledValue()->stripPointerCasts();
          if (freeCall && freeCall->getName().compare(StringRef("free")) == 0) {
              // handle free
              IRBuilder<> builder(inst);
              builder.SetInsertPoint(inst);
              auto free_inst = dyn_cast<CallInst>(inst);
              if (!free_inst)
                  continue;
              auto* cast_addr = builder.CreatePointerCast(free_inst->getOperand(0), intTy, "cast_to_int");
              auto* call = builder.CreateCall(handleFree, {cast_addr});


              Constant* func_def;
              if (inst->getFunction()->getReturnType() == Type::getVoidTy(m.getContext()))
                  func_def = nullptr;
              else
                  func_def = Constant::getNullValue(inst->getFunction()->getReturnType());

              Instruction* thenterm;
              Instruction* elseterm;
              SplitBlockAndInsertIfThenElse(call, inst->getNextNode(), &thenterm, &elseterm);

              switch (this->analysis) {
                  default:
                      inst->moveBefore(thenterm); // allow the free
                      CallInst::Create(
                              m.getOrInsertFunction("exit", intTy, intTy),
                              ConstantInt::get(intTy, -1, true), "exit", elseterm);
                      break;
                  case tolerator::AnalysisType::IGNORING:
                  case tolerator::AnalysisType::DEFAULTING:
                      // branch to first instruction after split
                      inst->moveBefore(thenterm);
                      elseterm = inst->getNextNode();
                      break;
                  case tolerator::AnalysisType::BYPASSING:
                      // THEN
                      inst->moveBefore(thenterm);
                      // ELSE
                      ReturnInst::Create(m.getContext(), func_def, elseterm);
                      elseterm->eraseFromParent();
                      break;
              }
              continue;
          }
      }

      // handle BEFORE instruction
      if (isa<SDivOperator>(inst) || isa<UDivOperator>(inst)) {
          IRBuilder<> builder(inst);
          handleDivision(inst, builder, handleDiv, m, *this);
      }
  }
  // Begin instructor code
  return true;
}
// End instructor code


