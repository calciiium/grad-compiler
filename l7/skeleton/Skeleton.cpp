#include "llvm/Pass.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Passes/PassPlugin.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Support/raw_ostream.h"

using namespace llvm;

namespace {

struct SkeletonPass : public PassInfoMixin<SkeletonPass> {
    PreservedAnalyses run(Module &M, ModuleAnalysisManager &AM) {
        for (auto &F : M) {
            for(auto &BB : F) {
                Instruction* terminator = BB.getTerminator();
                int numSuccs = terminator->getNumSuccessors();
                if(numSuccs == 2){
                    BasicBlock* bb1 = terminator->getSuccessor(0);
                    BasicBlock* bb2 = terminator->getSuccessor(1);
                    if(bb2->size() > bb1->size()){
                        errs() << "Inverting a branch instruction in function " << F.getName() << "!\n";
                        IRBuilder<> builder(terminator);
                        llvm::InvertBranch((BranchInst*)terminator, builder);
                    }
                }
            }            
        }
        return PreservedAnalyses::all();
    };
};

}

extern "C" LLVM_ATTRIBUTE_WEAK ::llvm::PassPluginLibraryInfo
llvmGetPassPluginInfo() {
    return {
        .APIVersion = LLVM_PLUGIN_API_VERSION,
        .PluginName = "Skeleton pass",
        .PluginVersion = "v0.1",
        .RegisterPassBuilderCallbacks = [](PassBuilder &PB) {
            PB.registerPipelineStartEPCallback(
                [](ModulePassManager &MPM, OptimizationLevel Level) {
                    MPM.addPass(SkeletonPass());
                });
        }
    };
}
;