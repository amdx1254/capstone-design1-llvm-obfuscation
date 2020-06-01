#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Instructions.h"
#include "llvm/Support/Alignment.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/CFG.h"
using namespace llvm;

namespace {
    struct ReturnObfuscation : public FunctionPass {
        static char ID;
        ReturnObfuscation() : FunctionPass(ID) {}
        bool runOnFunction(Function &F) override {
            Module* mod = F.getParent();
            ArrayType* return_array = ArrayType::get(IntegerType::get(mod->getContext(), 8), 12);
            PointerType* return_array_ptr = PointerType::get(return_array, 0);
            PointerType* ret_func_ptr = PointerType::get(IntegerType::get(mod->getContext(), 8), 0);
            ConstantInt* const_int_1 = ConstantInt::get(mod->getContext(), APInt(32, StringRef("1"), 10));
            ConstantInt* const_int_0 = ConstantInt::get(mod->getContext(), APInt(32, StringRef("0"), 10));
            ConstantInt* const_int_20 = ConstantInt::get(mod->getContext(), APInt(32, StringRef("12"), 10));
            ConstantInt* const_int32_133 = ConstantInt::get(mod->getContext(), APInt(32, StringRef("133"), 10));
            AllocaInst* ptr_ret_array;
            AllocaInst* ptr_this_ret;
            AllocaInst* ret_array_ptr;
            AllocaInst* ptr_i;
            std::vector<Instruction *> instructions;
            std::vector<BasicBlock *> RetBlocks;
            bool inserted = false;
            bool splitted = false;
            for (auto &BB : F) {
                for (auto &I : BB) {
                    if(!inserted) {
                        ptr_ret_array = new AllocaInst(return_array, NULL, "ret_ptr", &I);
                        ptr_ret_array->setAlignment(MaybeAlign(1));
                        ptr_this_ret = new AllocaInst(ret_func_ptr, NULL,  "ptr", &I);
                        ret_array_ptr = new AllocaInst(ret_func_ptr, NULL, "ptr2", &I);
                        ptr_i = new AllocaInst(IntegerType::get(mod->getContext(), 32), NULL,  "i", &I);
                
                        inserted=true;
                        IndirectBrInst *a;
                        
                    }
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
                    BasicBlock *retblock = BB->splitBasicBlock(I->getIterator(), BB->getName() + ".RetBlock");
                    RetBlocks.push_back(retblock);
                } else {
                    RetBlocks.push_back(BB);
                }
                    
            }

            for (auto &BB : RetBlocks) {
                Constant* retBlockAddress = BlockAddress::get(BB);
                Module* M = F.getParent();
                
                for (auto curFref = M->getFunctionList().begin(), 
                        endFref = M->getFunctionList().end(); 
                        curFref != endFref; ++curFref) {
                    for (auto& B: curFref->getBasicBlockList()) {
                        StoreInst* asdf = new StoreInst(retBlockAddress, ptr_this_ret, false, &B);
                        asdf->setAlignment(MaybeAlign(4));
                        break;
                    }

                }
                BasicBlock* decrypt_start = BasicBlock::Create(mod->getContext(), "dec_start", &F, BB);
                for (BasicBlock* preds : predecessors(BB)) {
                    preds->getTerminator()->eraseFromParent();
                    BranchInst::Create(decrypt_start, preds);
                }
                

                std::vector<Value*> ptr_to_retarray_indices;
                ptr_to_retarray_indices.push_back(const_int_0);
                ptr_to_retarray_indices.push_back(const_int_0);
                GetElementPtrInst* ptr_to_retarray = GetElementPtrInst::Create(return_array, ptr_ret_array, ptr_to_retarray_indices, "arrayidx", decrypt_start);
                ptr_to_retarray->setIsInBounds(true);
                StoreInst* store_to_ret_ptr = new StoreInst(ptr_to_retarray, ret_array_ptr, false, decrypt_start);
                
                store_to_ret_ptr->setAlignment(MaybeAlign(4));
                
                StoreInst* void_17 = new StoreInst(retBlockAddress, ptr_this_ret, false, decrypt_start);

                ptr_this_ret->setAlignment(MaybeAlign(4));
                ret_array_ptr->setAlignment(MaybeAlign(4));
                ptr_i->setAlignment(MaybeAlign(4));
                void_17->setAlignment(MaybeAlign(4));

                

                StoreInst* store_i_0 = new StoreInst(const_int_0, ptr_i, false, decrypt_start);
                store_i_0->setAlignment(MaybeAlign(4));



                BasicBlock* decrypt_cond = BasicBlock::Create(mod->getContext(), "dec_cond", &F, BB);

                BranchInst::Create(decrypt_cond, decrypt_start);

                LoadInst* ldr_i_data = new LoadInst(ptr_i, "", false, decrypt_cond);
                ldr_i_data->setAlignment(MaybeAlign(4));
                ICmpInst* cmp_i_with_20 = new ICmpInst(*decrypt_cond, ICmpInst::ICMP_SLT, ldr_i_data, const_int_20, "cmp");
                
                BasicBlock* decrypt_ing = BasicBlock::Create(mod->getContext(), "dec_ing", &F, BB);
                BasicBlock* decrypt_add = BasicBlock::Create(mod->getContext(), "dec_add", &F, BB);
                BasicBlock* decrypt_end = BasicBlock::Create(mod->getContext(), "dec_end", &F, BB);
                BranchInst::Create(decrypt_ing, decrypt_end, cmp_i_with_20, decrypt_cond);

                LoadInst* ldr_i_data_2 = new LoadInst(ptr_i, "", false, decrypt_ing);
                ldr_i_data_2->setAlignment(MaybeAlign(4));
                LoadInst* ldr_ptr_this_ret = new LoadInst(ptr_this_ret, "", false, decrypt_ing);
                ldr_ptr_this_ret->setAlignment(MaybeAlign(4));
                GetElementPtrInst* get_func_ptr_idx = GetElementPtrInst::Create(cast<PointerType>(ldr_ptr_this_ret->getType()->getScalarType())->getElementType(), ldr_ptr_this_ret, ldr_i_data_2, "arrayidx1", decrypt_ing);
                get_func_ptr_idx->setIsInBounds(true);
                LoadInst* ldr_func_ptr_idx = new LoadInst(get_func_ptr_idx, "", false, decrypt_ing);
                ldr_func_ptr_idx->setAlignment(MaybeAlign(1));

                LoadInst* ldr_i_data_3 = new LoadInst(ptr_i, "", false, decrypt_ing);
                ldr_i_data_3->setAlignment(MaybeAlign(4));

                std::vector<Value*> ptr_retn_array_indices;
                ptr_retn_array_indices.push_back(const_int_0);
                ptr_retn_array_indices.push_back(ldr_i_data_3);
                GetElementPtrInst* get_retn_array_data_idx = GetElementPtrInst::Create(return_array, ptr_ret_array, ptr_retn_array_indices, "arrayidx2", decrypt_ing);
                get_retn_array_data_idx->setIsInBounds(true);
                StoreInst* str_retn_array_data_idx = new StoreInst(ldr_func_ptr_idx, get_retn_array_data_idx, false, decrypt_ing);
                str_retn_array_data_idx->setAlignment(MaybeAlign(1));

                LoadInst* ldr_i_data_4 = new LoadInst(ptr_i, "", false, decrypt_ing);
                ldr_i_data_4->setAlignment(MaybeAlign(4));

                std::vector<Value*> ptr_retn_array_indices2;
                ptr_retn_array_indices2.push_back(const_int_0);
                ptr_retn_array_indices2.push_back(ldr_i_data_4);
                GetElementPtrInst* get_retn_array_data_idx2 = GetElementPtrInst::Create(return_array, ptr_ret_array, ptr_retn_array_indices2, "arrayidx3", decrypt_ing);
                get_retn_array_data_idx2->setIsInBounds(true);
                LoadInst* ldr_retn_array_data_idx2 = new LoadInst(get_retn_array_data_idx2, "", false, decrypt_ing);
                ldr_retn_array_data_idx2->setAlignment(MaybeAlign(1));

                CastInst* cast_retn_array_data_idx2 = new ZExtInst(ldr_retn_array_data_idx2, IntegerType::get(mod->getContext(), 32), "conv", decrypt_ing);
                BinaryOperator* xor_retn_array_data_idx2 = BinaryOperator::Create(Instruction::Xor, cast_retn_array_data_idx2, const_int32_133, "xor", decrypt_ing);
                
                CastInst* trun_retn_array_data_idx2 = new TruncInst(xor_retn_array_data_idx2, IntegerType::get(mod->getContext(), 8), "conv4", decrypt_ing);
                

                LoadInst* ldr_i_data_5 = new LoadInst(ptr_i, "", false, decrypt_ing);
                ldr_i_data_5->setAlignment(MaybeAlign(4));

                std::vector<Value*> ptr_retn_array_indices4;
                ptr_retn_array_indices4.push_back(const_int_0);
                ptr_retn_array_indices4.push_back(ldr_i_data_5);
                GetElementPtrInst* get_retn_array_data_idx4 = GetElementPtrInst::Create(return_array, ptr_ret_array, ptr_retn_array_indices4, "arrayidx5", decrypt_ing);
                get_retn_array_data_idx4->setIsInBounds(true);
                StoreInst* str_retn_array_data_idx4 = new StoreInst(trun_retn_array_data_idx2, get_retn_array_data_idx4, false, decrypt_ing);
                str_retn_array_data_idx4->setAlignment(MaybeAlign(1));


                BranchInst::Create(decrypt_add, decrypt_ing);

                LoadInst* ldr_i_data_6 = new LoadInst(ptr_i, "", false, decrypt_add);
                ldr_i_data_6->setAlignment(MaybeAlign(4));
                BinaryOperator* add_i_data_4 = BinaryOperator::Create(Instruction::Add, ldr_i_data_6, const_int_1, "", decrypt_add);
                StoreInst* str_i_data_4 = new StoreInst(add_i_data_4, ptr_i, false, decrypt_add);   
                str_i_data_4->setAlignment(MaybeAlign(4));
                BranchInst::Create(decrypt_cond, decrypt_add);

                LoadInst* ldr_ret_array = new LoadInst(ret_array_ptr, "", false, decrypt_end);
                ldr_ret_array->setAlignment(MaybeAlign(4));

                BasicBlock* dec_jmp = BasicBlock::Create(mod->getContext(), "dec_jmp", &F, BB);
                BranchInst::Create(dec_jmp, decrypt_end);

                PHINode* ptr_40 = PHINode::Create(ret_func_ptr, 1, "", dec_jmp);
                ptr_40->addIncoming(ldr_ret_array, decrypt_end);
                IndirectBrInst *void_41 = IndirectBrInst::Create(ldr_ret_array, 1, dec_jmp);
                void_41->addDestination(BB);
                errs().write_escaped(F.getName()) << "   " <<  F.getParent()->getName() <<  '\n';
            }
            return true;
        } 

    }; // end of struct Hello
}  // end of anonymous namespace

char ReturnObfuscation::ID = 0;

static RegisterPass<ReturnObfuscation> X("rof", "Hello World Pass",
                             false /* Only looks at CFG */,
                             false /* Analysis Pass */);