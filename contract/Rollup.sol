// SPDX-License-Identifier: MIT
pragma solidity 0.8.26;

/// @notice Hold ETH for a rollup. Trust the sequencer to submit valid batches.
/// @dev This test contract has no proof verifier or emergency exit.
contract Rollup {
    /// @notice Account that can execute batches.
    address public sequencer;
    /// @notice Current L2 state root.
    bytes32 public stateRoot;
    /// @notice Number of the last executed batch. Starts at zero.
    uint256 public batchNumber;
    /// @notice ETH reserved for L2 balances.
    uint256 public backing;
    /// @notice Deposit credit for each owner that batches have not consumed.
    mapping(address => uint256) public pendingDeposits;
    /// @notice ETH each owner can withdraw.
    mapping(address => uint256) public pendingWithdrawals;
    /// @notice Reentry lock: zero permits state changes; one blocks them.
    uint256 private entered;

    modifier nonReentrant() {
        require(entered == 0);
        entered = 1;
        _;
        entered = 0;
    }

    constructor(address sequencer_, bytes32 initialRoot) {
        require(sequencer_ != address(0));
        sequencer = sequencer_;
        stateRoot = initialRoot;
    }

    /// @notice Add deposit credit for owner. A batch must consume the credit.
    function deposit(address owner) external payable nonReentrant {
        require(owner != address(0) && owner != address(this));
        require(msg.value != 0);
        pendingDeposits[owner] += msg.value;
    }

    /// @notice Consume deposit credit, add withdrawal credit, and set the root.
    /// @dev Use a zero address with a zero amount to omit either credit change.
    function executeBatch(
        uint256 nextBatchNumber,
        bytes32 oldRoot,
        bytes32 newRoot,
        address depositOwner,
        uint256 depositAmount,
        address withdrawalOwner,
        uint256 withdrawalAmount
    ) external nonReentrant {
        require(msg.sender == sequencer);
        require(nextBatchNumber == batchNumber + 1);
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
        require(withdrawalAmount <= available);
        backing = available - withdrawalAmount;
        pendingWithdrawals[withdrawalOwner] += withdrawalAmount;
        stateRoot = newRoot;
        batchNumber = nextBatchNumber;
    }

    /// @notice Send ETH to owner, then debit its credit. Any caller can trigger payment.
    /// @dev Keep the lock set during the call. Revert all changes if the call fails.
    function withdrawPendingBalance(address payable owner, uint256 amount) external nonReentrant {
        require(amount != 0);
        uint256 credit = pendingWithdrawals[owner];
        require(amount <= credit);
        (bool success,) = owner.call{value: amount}("");
        require(success);
        pendingWithdrawals[owner] = credit - amount;
    }
}
