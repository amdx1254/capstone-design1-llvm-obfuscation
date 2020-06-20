#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Instructions.h"
#include "llvm/Support/Alignment.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/CFG.h"
#include <fstream>
#include <iostream>
using namespace llvm;

namespace {
    struct PreProcess : public FunctionPass {
        static char ID;

        PreProcess() : FunctionPass(ID) { }
        bool runOnFunction(Function &F) override {  
            Module* mod = F.getParent();
            std::vector<Instruction *> instructions;
            std::vector<BasicBlock *> RetBlocks;
            bool inserted = false;
            std::ofstream functionFile("functions.txt", std::ios_base::app);
            if (functionFile.is_open()) {
                if (!F.getName().contains("__cxx") && !F.getName().contains("_GLOBAL"))
                    functionFile << F.getName().str() << "\n";
                functionFile.close();
            }
            if (!F.getName().contains("__cxx") && !F.getName().contains("_GLOBAL")) {
                for (auto &BB : F) {
                    for (auto &I : BB) {
                        if (I.getOpcode() == Instruction::Ret) {
                            instructions.push_back(&I);
                        }
                    }
                }
                for (auto &I : instructions) {
                    BasicBlock *BB = I->getParent();
                    // One Instruction Basic Block has only one ret instructions
                    if (!BB->size() < 2)
                    {
                        BasicBlock *retblock = BB->splitBasicBlock(I->getIterator(), "obfuscatedreturn");
                    } else {
                        BB->setName("obfuscatedreturn");
                    }
                }
            
            }
            return true;
        } 

    }; // end of struct Hello
}  // end of anonymous namespace

char PreProcess::ID = 0;

static RegisterPass<PreProcess> X("preprocess", "Hello World Pass",
                             false /* Only looks at CFG */,
                             false /* Analysis Pass */);