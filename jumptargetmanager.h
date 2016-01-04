#ifndef _JUMPTARGETMANAGER_H
#define _JUMPTARGETMANAGER_H

// Standard includes
#include <cstdint>
#include <map>

// Forward declarations
namespace llvm {
class BasicBlock;
class Function;
class Instruction;
class LLVMContext;
class Module;
class Value;
}

class JumpTargetManager {
public:
  using BlockWithAddress = std::pair<uint64_t, llvm::BasicBlock *>;
  static const BlockWithAddress NoMoreTargets;

public:
  JumpTargetManager(llvm::Module& TheModule,
                    llvm::Value *PCReg,
                    llvm::Function *TheFunction);

  /// Handle a new program counter. We might already have a basic block for that
  /// program counter, or we could even have a translation for it. Return one
  /// of these, if appropriate.
  ///
  /// \param PC the new program counter.
  /// \param ShouldContinue an out parameter indicating whether the returned
  ///        basic block was just a placeholder or actually contains a
  ///        translation.
  ///
  /// \return the basic block to use from now on, or null if the program counter
  ///         is not associated to a basic block.
  llvm::BasicBlock *newPC(uint64_t PC, bool& ShouldContinue);

  /// Save the PC-Instruction association for future use (jump target)
  void registerInstruction(uint64_t PC, llvm::Instruction *Instruction);

  /// Save the PC-BasicBlock association for futur use (jump target)
  void registerBlock(uint64_t PC, llvm::BasicBlock *Block);

  void translateIndirectJumps();

  /// \brief Return the most recent instruction writing the program counter
  /// Note that the search is performed only in the current basic block.
  /// The function will assert if the write instruction is not found.
  ///
  /// \return a pointer to the last StoreInst writing the program counter, or
  ///         nullptr if a call to an helper has been found before the write to
  ///         the PC.
  llvm::StoreInst *getPrevPCWrite(llvm::Instruction *TheInstruction);

  llvm::Function *exitTB() { return ExitTB; }

  /// Pop from the list of program counters to explore
  ///
  /// \return a pair containing the PC and the initial block to use, or
  ///         JumpTarget::NoMoreTargets if we're done.
  BlockWithAddress peekJumpTarget();

  /// Get or create a block for the given PC
  llvm::BasicBlock *getBlockAt(uint64_t PC);

private:
  // TODO: instead of a gigantic switch case we could map the original memory
  //       area and write the address of the translated basic block at the jump
  //       target
  llvm::BasicBlock *createDispatcher(llvm::Function *OutputFunction,
                                     llvm::Value *SwitchOnPtr,
                                     bool JumpDirectly);

private:
  using BlockMap = std::map<uint64_t, llvm::BasicBlock *>;
  using InstructionMap = std::map<uint64_t, llvm::Instruction *>;

  llvm::Module &TheModule;
  llvm::LLVMContext& Context;
  llvm::Function* TheFunction;
  /// Holds the association between a PC and the last generated instruction for
  /// the previous instruction.
  InstructionMap OriginalInstructionAddresses;
  /// Holds the association between a PC and a BasicBlock.
  BlockMap JumpTargets;
  /// Queue of program counters we still have to translate.
  std::vector<BlockWithAddress> Unexplored;
  llvm::Value *PCReg;
  llvm::Function *ExitTB;
};

#endif // _JUMPTARGETMANAGER_H
