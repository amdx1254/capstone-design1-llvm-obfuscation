#include "ARM.h"
#include "ARMBaseInstrInfo.h"
#include "ARMSubtarget.h"
#include "ARMMachineFunctionInfo.h"
#include "llvm/ADT/SmallPtrSet.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/CodeGen/MachineBasicBlock.h"
#include "llvm/CodeGen/MachineFunctionPass.h"
#include "llvm/CodeGen/MachineInstr.h"
#include "llvm/CodeGen/MachineInstrBuilder.h"
#include "llvm/CodeGen/MachineJumpTableInfo.h"
#include "llvm/CodeGen/MachineRegisterInfo.h"
#include "llvm/CodeGen/TargetRegisterInfo.h"
#include "llvm/IR/Function.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/raw_ostream.h"
using namespace llvm;

namespace {
struct ARMReturnObfuscation : public MachineFunctionPass {
  static char ID;
  ARMReturnObfuscation() : MachineFunctionPass(ID) {
    initializeARMReturnObfuscationPass(*PassRegistry::getPassRegistry());
  }

  bool runOnMachineFunction(MachineFunction &MF) override {
    //if( MF.getFunction().getName().equals("setup") ) {
      MachineRegisterInfo *MRI = &MF.getRegInfo();
    if (true) {
          srand(time(NULL));
    ARMFunctionInfo *AFI = MF.getInfo<ARMFunctionInfo>();
    const ARMBaseInstrInfo *TII =
        static_cast<const ARMBaseInstrInfo *>(MF.getSubtarget().getInstrInfo());
    std::vector<MachineInstr *> instructions;
    std::vector<MachineInstr *> terminators;
    std::vector<MachineInstr *> returns;
    std::vector<MachineBasicBlock *> returnbbs;
    std::vector<MachineBasicBlock *> NewBasicBlocks;
    MachineJumpTableInfo *MJTI = MF.getJumpTableInfo();
    
    // Find All Instructions
    for (auto &MBB : MF) {
      for (auto &MI : MBB) {
        // if(!MI.isTerminator() )
        instructions.push_back(&MI);
      }
    }
    int i = 1;
    /*
    for (auto &MI : instructions) {
      const DebugLoc &DL = MI->getDebugLoc();
      MachineBasicBlock *OrigBB = MI->getParent();
      MachineBasicBlock *NewBB =
      MF.CreateMachineBasicBlock(OrigBB->getBasicBlock());
        
      if (i == 1 || i == instructions.size())
        MF.insert(++OrigBB->getIterator(), NewBB);
      else {
          auto ite = MF.begin();
          for (int a = 0; a < rand()%(i - 1) + 1 ; a++ ) {
              ite++;
          }
        MF.insert(ite, NewBB);
      } 
      //MF.insert(++OrigBB->getIterator(), NewBB);
      i++;
      NewBB->splice(NewBB->end(), OrigBB, MI->getIterator(), OrigBB->end());

      // TII->insertUnconditionalBranch(*OrigBB, NewBB, DebugLoc());
      NewBB->transferSuccessors(OrigBB);
      OrigBB->addSuccessor(NewBB);
  
      //NewBB->updateTerminator();
      //OrigBB->updateTerminator();
      
      if (AFI->isThumb2Function()) {
        BuildMI(*OrigBB, OrigBB->end(), DL, TII->get(ARM::t2B)).addMBB(NewBB).addImm(ARMCC::AL).addReg(0);
      } else if (AFI->isThumbFunction()) {
        BuildMI(*OrigBB, OrigBB->end(), DL, TII->get(ARM::tB)).addMBB(NewBB).addImm(ARMCC::AL).addReg(0);
      } else {
        BuildMI(*OrigBB, OrigBB->end(), DL, TII->get(ARM::B)).addMBB(NewBB);
      }
      

     
     srand(time(NULL));
     int randimm = rand()%10+1;
     
     if (AFI->isThumb2Function()) {
        BuildMI(*OrigBB, OrigBB->end(), DL, TII->get(ARM::tMOVi8), ARM::NoRegister)
        .addImm(randimm);

        BuildMI(*OrigBB, OrigBB->end(), DL, TII->get(ARM::tCMPi8))
        .addReg(ARM::NoRegister, RegState::Kill)
        .addImm(randimm);
        BuildMI(*OrigBB, OrigBB->end(), DL, TII->get(ARM::tBcc))
        .addMBB(NewBB)
        .addImm(ARMCC::EQ)
        .addReg(ARM::CPSR);
      } else if (AFI->isThumbFunction()) {
        BuildMI(*OrigBB, OrigBB->end(), DL, TII->get(ARM::tMOVi8), ARM::NoRegister)
        .addImm(randimm);

        BuildMI(*OrigBB, OrigBB->end(), DL, TII->get(ARM::tCMPi8))
        .addReg(ARM::NoRegister)
        .addImm(randimm);
        BuildMI(*OrigBB, OrigBB->end(), DL, TII->get(ARM::tBcc))
        .addMBB(NewBB)
        .addImm(ARMCC::EQ)
        .addReg(ARM::CPSR);
      } else {
        BuildMI(*OrigBB, OrigBB->end(), DL, TII->get(ARM::B)).addMBB(NewBB);
      }

      LivePhysRegs LiveRegs;
      computeAndAddLiveIns(LiveRegs, *NewBB);
      // BuildMI(MBB, MI2, DL, TII->get(ARM::B)).addMBB(BBB);
      //BuildMI(MBB, MBB.end(), DL, TII->get(ARM::MOVr), ARM::R10)
      //.addReg(ARM::R10)
      //.addImm(ARMCC::AL).addReg(0).addReg(0); 
      //outs() << "HOHOHOO: \n";
      //MI->dump();
    }
    */
    /*
    if (!returns.empty()) {

      for (auto &MI : returns) {

        const DebugLoc &DL = MI->getDebugLoc();
        MachineBasicBlock *OrigBB = MI->getParent();

        MachineBasicBlock *NewBB =
            MF.CreateMachineBasicBlock(OrigBB->getBasicBlock());
        MF.insert(++OrigBB->getIterator(), NewBB);

        NewBB->splice(NewBB->end(), OrigBB, --MI->getIterator(), OrigBB->end());
        BuildMI(*OrigBB, OrigBB->end(), DL, TII->get(ARM::B)).addMBB(NewBB);
        TII->insertUnconditionalBranch(*OrigBB, NewBB, DebugLoc());
        NewBB->transferSuccessors(OrigBB);
        OrigBB->addSuccessor(NewBB);

        NewBB->updateTerminator();
        OrigBB->updateTerminator();

        // BuildMI(MBB, MI2, DL, TII->get(ARM::B)).addMBB(BBB);
        //BuildMI(MBB, MBB.end(), DL, TII->get(ARM::MOVr), ARM::R10)
        //.addReg(ARM::R10)
        //.addImm(ARMCC::AL).addReg(0).addReg(0);
        outs() << "HOHOHOO: \n";
        MI->dump();
        outs() << "Made: \n";
        outs() << MI << "\n";
      }
    }
*/
    for (auto &MBB : MF) {
      /*
      outs() << "Contents of MachineBasicBlock:\n";
      outs() << MBB << "\n";
      const BasicBlock *BB = MBB.getBasicBlock();
      outs() << "Contents of BasicBlock corresponding to MachineBasicBlock:\n";
      outs() << BB << "\n";
      for (BasicBlock::const_iterator i = BB->begin(), e = BB->end(); i != e;
           ++i) {
        const Instruction *ii = &*i;
        errs() << *ii << "\n";
      }
      */
    }
    return true;
     }
    
    return false;
  };

  StringRef getPassName() const override {
    return "ARM Return Obfuscation pass";
  }

private:
};
char ARMReturnObfuscation::ID = 0;
} // namespace

INITIALIZE_PASS(ARMReturnObfuscation, "arm-return-obfuscation",
                "ARM Return Obfuscation pass",
                true, // is CFG only?
                true  // is analysis?
)

namespace llvm {

FunctionPass *createARMReturnObfuscationPass() {
  return new ARMReturnObfuscation();
}

} // namespace llvm