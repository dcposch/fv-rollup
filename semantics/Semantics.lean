import Solm.Notation
import Solm.Semantics
import Solm.SolidityLayout

open Solm Solm.Notation ABI

namespace Rollup.EVM

/-- Model the Solidity checks, storage order, and external call. -/
def contract : ContractDecl := solidity% contract Rollup {
  address sequencer;
  bytes32 stateRoot;
  uint256 batchNumber;
  uint256 backing;
  mapping(address => uint256) pendingDeposits;
  mapping(address => uint256) pendingWithdrawals;
  uint256 entered;

  constructor(address sequencer_, bytes32 initialRoot) {
    require(sequencer_ != address(0));
    sequencer = sequencer_;
    stateRoot = initialRoot;
  }

  function deposit(address owner) external payable {
    require(entered == 0);
    entered = 1;
    require(owner != address(0) && owner != address(this));
    require(msg.value != 0);
    uint256 nextCredit = pendingDeposits[owner] + msg.value;
    require(nextCredit < #(2 ^ 256));
    pendingDeposits[owner] = nextCredit;
    entered = 0;
  }

  function executeBatch(uint256 nextBatchNumber, bytes32 oldRoot, bytes32 newRoot,
      address depositOwner, uint256 depositAmount,
      address withdrawalOwner, uint256 withdrawalAmount) external {
    require(entered == 0);
    entered = 1;
    require(msg.sender == sequencer);
    uint256 nextNumber = batchNumber + 1;
    require(nextNumber < #(2 ^ 256));
    require(nextBatchNumber == nextNumber);
    require(oldRoot == stateRoot);
    if (depositAmount == 0) {
      require(depositOwner == address(0));
    } else {
      require(depositOwner != address(0) && depositOwner != address(this));
    }
    if (withdrawalAmount == 0) {
      require(withdrawalOwner == address(0));
    } else {
      require(withdrawalOwner != address(0) && withdrawalOwner != address(this));
    }
    uint256 depositCredit = pendingDeposits[depositOwner];
    require(depositAmount <= depositCredit);
    pendingDeposits[depositOwner] = depositCredit - depositAmount;
    uint256 available = backing + depositAmount;
    require(available < #(2 ^ 256));
    require(withdrawalAmount <= available);
    backing = available - withdrawalAmount;
    uint256 nextCredit = pendingWithdrawals[withdrawalOwner] + withdrawalAmount;
    require(nextCredit < #(2 ^ 256));
    pendingWithdrawals[withdrawalOwner] = nextCredit;
    stateRoot = newRoot;
    batchNumber = nextBatchNumber;
    entered = 0;
  }

  function withdrawPendingBalance(address owner, uint256 amount) external {
    require(entered == 0);
    entered = 1;
    require(amount != 0);
    uint256 credit = pendingWithdrawals[owner];
    require(amount <= credit);
    (bool success, bytes memory _data) = owner.call{value: amount}(new bytes(0));
    require(success);
    pendingWithdrawals[owner] = credit - amount;
    entered = 0;
  }

  function sequencer() external returns (address) { return sequencer; }
  function stateRoot() external returns (bytes32) { return stateRoot; }
  function batchNumber() external returns (uint256) { return batchNumber; }
  function backing() external returns (uint256) { return backing; }
  function pendingDeposits(address owner) external returns (uint256) { return pendingDeposits[owner]; }
  function pendingWithdrawals(address owner) external returns (uint256) { return pendingWithdrawals[owner]; }
}

def uint256 : IntType := .uint ⟨256, by decide⟩

def mapSlot (owner : KeyValue) (slot : Ethereum.UInt256) : Ethereum.UInt256 :=
  Ethereum.uInt256OfByteArray (Ethereum.KEC ((keyValueToWord owner).toByteArray ++ slot.toByteArray))

def wordLoc (slot : Ethereum.UInt256) : StorageLoc :=
  { slot := slot, offset := 0, size := 32, hbound := by decide, type := .int uint256 }

def layoutRaw : EvaledStorageRef → Ethereum.State → Option StorageLoc
  | ⟨"sequencer", []⟩, _ => some { slot := ⟨0⟩, offset := 0, size := 20, hbound := by decide, type := .address }
  | ⟨"stateRoot", []⟩, _ => some { slot := ⟨1⟩, offset := 0, size := 32, hbound := by decide, type := .bytes ⟨31, by decide⟩ }
  | ⟨"batchNumber", []⟩, _ => some (wordLoc ⟨2⟩)
  | ⟨"backing", []⟩, _ => some (wordLoc ⟨3⟩)
  | ⟨"pendingDeposits", [.mindex owner]⟩, _ => some (wordLoc (mapSlot owner ⟨4⟩))
  | ⟨"pendingWithdrawals", [.mindex owner]⟩, _ => some (wordLoc (mapSlot owner ⟨5⟩))
  | ⟨"entered", []⟩, _ => some (wordLoc ⟨6⟩)
  | _, _ => none

def config : Config :=
  { storage := solidityStorageLayout layoutRaw
    externalABI := defaultExternalCallABI
    selfDeployment := genSolidityConstructorDeployment contract.ctor.params }

end Rollup.EVM
