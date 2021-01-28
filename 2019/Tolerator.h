// This interface was provided by my instructor.

#pragma once


#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/IR/CallSite.h"
#include "llvm/IR/Module.h"
#include "llvm/Pass.h"
#include "llvm/Support/raw_ostream.h"


namespace tolerator {


enum class AnalysisType {
  LOGGING,
  IGNORING,
  DEFAULTING,
  BYPASSING
};


struct Tolerator : public llvm::ModulePass {
  static char ID;
  AnalysisType analysis;

  Tolerator(AnalysisType analysisType) : llvm::ModulePass(ID) {
      analysis = analysisType;
  }

  bool runOnModule(llvm::Module& m) override;

};


}  // namespace tolerator


