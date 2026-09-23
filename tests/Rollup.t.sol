// SPDX-License-Identifier: MIT
pragma solidity 0.8.26;

import {Rollup} from "../contract/Rollup.sol";

interface Vm {
    function deal(address, uint256) external;
    function prank(address) external;
    function expectRevert() external;
}

/// @dev Send ETH without a call to the receiver.
contract Donation {
    constructor(address payable target) payable {
        selfdestruct(target);
    }
}

/// @dev Forward a callback to test a call chain.
contract Relay {
    function forward(address target, bytes calldata data) external returns (bool) {
        (bool ok,) = target.call(data);
        return ok;
    }
}

/// @dev Try each state change during an ETH payment.
contract Receiver {
    Rollup public rollup;
    Relay public relay = new Relay();
    bool public reject;
    bool public donate;
    uint256 public observedCredit;
    uint256 public callbacks;

    function setRollup(Rollup target) external {
        rollup = target;
    }

    function setReject(bool value) external {
        reject = value;
    }

    function setDonate(bool value) external {
        donate = value;
    }

    function batch(address depositOwner, uint256 depositAmount, uint256 amount) external {
        rollup.executeBatch(
            rollup.batchNumber() + 1,
            rollup.stateRoot(),
            bytes32(uint256(9)),
            depositOwner,
            depositAmount,
            address(this),
            amount
        );
    }

    receive() external payable {
        callbacks++;
        observedCredit = rollup.pendingWithdrawals(address(this));
        (bool depositOK,) = address(rollup).call{value: 1}(abi.encodeCall(Rollup.deposit, (address(this))));
        (bool batchOK,) = address(rollup)
            .call(
                abi.encodeCall(
                    Rollup.executeBatch,
                    (rollup.batchNumber() + 1, rollup.stateRoot(), bytes32(uint256(10)), address(0), 0, address(0), 0)
                )
            );
        bool withdrawalOK =
            relay.forward(address(rollup), abi.encodeCall(Rollup.withdrawPendingBalance, (payable(address(this)), 1)));
        require(!depositOK && !batchOK && !withdrawalOK);
        if (donate) new Donation{value: 1}(payable(address(rollup)));
        require(!reject);
    }
}

contract RollupTest {
    Vm private constant vm = Vm(address(uint160(uint256(keccak256("hevm cheat code")))));
    Rollup private rollup;
    address private constant ALICE = address(0xA11CE);
    address private constant BOB = address(0xB0B);

    function setUp() public {
        vm.deal(address(this), 100 ether);
        rollup = new Rollup(address(this), bytes32(uint256(1)));
    }

    function testDepositBatchWithdrawal() public {
        rollup.deposit{value: 10 ether}(ALICE);
        rollup.executeBatch(1, bytes32(uint256(1)), bytes32(uint256(2)), ALICE, 6 ether, BOB, 4 ether);
        require(rollup.pendingDeposits(ALICE) == 4 ether);
        require(rollup.backing() == 2 ether);
        require(rollup.pendingWithdrawals(BOB) == 4 ether);
        vm.prank(ALICE);
        rollup.withdrawPendingBalance(payable(BOB), 3 ether);
        require(BOB.balance == 3 ether);
        require(rollup.pendingWithdrawals(BOB) == 1 ether);
        require(address(rollup).balance == 7 ether);
    }

    function testEmptyBatchAndSameRoot() public {
        rollup.executeBatch(1, bytes32(uint256(1)), bytes32(uint256(1)), address(0), 0, address(0), 0);
        require(rollup.batchNumber() == 1);
        vm.expectRevert();
        rollup.executeBatch(1, bytes32(uint256(1)), bytes32(uint256(1)), address(0), 0, address(0), 0);
    }

    function testUnauthorizedBatch() public {
        bytes32 root = rollup.stateRoot();
        vm.expectRevert();
        vm.prank(ALICE);
        rollup.executeBatch(1, root, bytes32(0), address(0), 0, address(0), 0);
    }

    function testWrongRoot() public {
        vm.expectRevert();
        rollup.executeBatch(1, bytes32(0), bytes32(0), address(0), 0, address(0), 0);
    }

    function testCannotSpendUnconsumedDeposit() public {
        rollup.deposit{value: 1 ether}(ALICE);
        vm.expectRevert();
        rollup.executeBatch(1, bytes32(uint256(1)), bytes32(0), address(0), 0, BOB, 1 ether);
        require(rollup.pendingDeposits(ALICE) == 1 ether);
    }

    function testCannotConsumeDepositTwice() public {
        rollup.deposit{value: 1 ether}(ALICE);
        rollup.executeBatch(1, bytes32(uint256(1)), bytes32(0), ALICE, 1 ether, address(0), 0);
        vm.expectRevert();
        rollup.executeBatch(2, bytes32(0), bytes32(0), ALICE, 1 ether, address(0), 0);
    }

    function testRejectedBatchRollsBackDepositDebit() public {
        rollup.deposit{value: 1 ether}(ALICE);
        vm.expectRevert();
        rollup.executeBatch(1, bytes32(uint256(1)), bytes32(0), ALICE, 1 ether, BOB, 2 ether);
        require(rollup.pendingDeposits(ALICE) == 1 ether);
        require(rollup.backing() == 0 && rollup.batchNumber() == 0);
        require(rollup.stateRoot() == bytes32(uint256(1)));
    }

    function testCannotPayTwice() public {
        rollup.deposit{value: 1 ether}(ALICE);
        rollup.executeBatch(1, bytes32(uint256(1)), bytes32(0), ALICE, 1 ether, BOB, 1 ether);
        rollup.withdrawPendingBalance(payable(BOB), 1 ether);
        vm.expectRevert();
        rollup.withdrawPendingBalance(payable(BOB), 1);
    }

    function testInvalidOwnersAndZeroAmounts() public {
        vm.expectRevert();
        rollup.deposit{value: 1}(address(0));
        vm.expectRevert();
        rollup.deposit{value: 1}(address(rollup));
        vm.expectRevert();
        rollup.deposit(ALICE);
        vm.expectRevert();
        rollup.withdrawPendingBalance(payable(BOB), 0);
        vm.expectRevert();
        rollup.executeBatch(1, bytes32(uint256(1)), bytes32(0), ALICE, 0, address(0), 0);
        vm.expectRevert();
        rollup.executeBatch(1, bytes32(uint256(1)), bytes32(0), address(0), 0, BOB, 0);
    }

    function receiverRollup() private returns (Receiver receiver, Rollup target) {
        receiver = new Receiver();
        target = new Rollup(address(receiver), bytes32(0));
        receiver.setRollup(target);
        target.deposit{value: 1 ether}(ALICE);
        receiver.batch(ALICE, 1 ether, 1 ether);
    }

    function testCallbackCannotReenter() public {
        (Receiver receiver, Rollup target) = receiverRollup();
        target.withdrawPendingBalance(payable(address(receiver)), 0.5 ether);
        require(receiver.callbacks() == 1);
        require(receiver.observedCredit() == 1 ether);
        require(target.pendingWithdrawals(address(receiver)) == 0.5 ether);
        require(target.batchNumber() == 1);
        require(target.pendingDeposits(address(receiver)) == 0);
        require(address(target).balance == 0.5 ether);
    }

    function testDonationDuringCallback() public {
        (Receiver receiver, Rollup target) = receiverRollup();
        receiver.setDonate(true);
        target.withdrawPendingBalance(payable(address(receiver)), 0.5 ether);
        require(address(target).balance == 0.5 ether + 1);
        require(target.pendingWithdrawals(address(receiver)) == 0.5 ether);
    }

    function testRejectedTransferRollsBackAndUnlocks() public {
        (Receiver receiver, Rollup target) = receiverRollup();
        receiver.setReject(true);
        vm.expectRevert();
        target.withdrawPendingBalance(payable(address(receiver)), 1 ether);
        require(target.pendingWithdrawals(address(receiver)) == 1 ether);
        require(receiver.callbacks() == 0);
        require(address(target).balance == 1 ether);
        receiver.setReject(false);
        target.withdrawPendingBalance(payable(address(receiver)), 1 ether);
        require(target.pendingWithdrawals(address(receiver)) == 0);
        require(address(target).balance == 0);
    }

    function testForcedETHDoesNotCreateCredit() public {
        new Donation{value: 1 ether}(payable(address(rollup)));
        require(address(rollup).balance == 1 ether && rollup.backing() == 0);
        vm.expectRevert();
        rollup.executeBatch(1, bytes32(uint256(1)), bytes32(0), address(0), 0, BOB, 1);
    }

    function testSequencerTrustBoundary() public {
        rollup.deposit{value: 1 ether}(ALICE);
        rollup.executeBatch(1, bytes32(uint256(1)), bytes32(uint256(123)), ALICE, 1 ether, BOB, 1 ether);
        rollup.withdrawPendingBalance(payable(BOB), 1 ether);
        require(BOB.balance == 1 ether);
    }

    function testFuzzAccounting(uint96 rawDeposit, uint96 rawConsume, uint96 rawCredit, uint96 rawPay) public {
        uint256 depositAmount = uint256(rawDeposit) % 10 ether + 1;
        uint256 consumed = uint256(rawConsume) % (depositAmount + 1);
        uint256 credit = uint256(rawCredit) % (consumed + 1);
        uint256 paid = uint256(rawPay) % (credit + 1);
        rollup.deposit{value: depositAmount}(ALICE);
        rollup.executeBatch(
            1,
            bytes32(uint256(1)),
            bytes32(0),
            consumed == 0 ? address(0) : ALICE,
            consumed,
            credit == 0 ? address(0) : BOB,
            credit
        );
        if (paid != 0) rollup.withdrawPendingBalance(payable(BOB), paid);
        require(rollup.pendingDeposits(ALICE) == depositAmount - consumed);
        require(rollup.backing() == consumed - credit);
        require(rollup.pendingWithdrawals(BOB) == credit - paid);
        require(address(rollup).balance == depositAmount - paid);
        require(
            address(rollup).balance == rollup.pendingDeposits(ALICE) + rollup.backing() + rollup.pendingWithdrawals(BOB)
        );
    }
}

/// @dev Submit arbitrary valid action sequences for four accounts.
contract Handler {
    Rollup public rollup;
    uint256 public deposited;
    uint256 public paid;

    constructor() {
        rollup = new Rollup(address(this), bytes32(0));
    }

    function actor(uint256 seed) public pure returns (address) {
        return address(uint160(100 + seed % 4));
    }

    function deposit(uint256 seed, uint96 raw) external {
        uint256 amount = uint256(raw) % 1 ether + 1;
        if (amount > address(this).balance) return;
        rollup.deposit{value: amount}(actor(seed));
        deposited += amount;
    }

    function batch(uint256 a, uint256 b, uint96 rawD, uint96 rawW, bytes32 root) external {
        address owner = actor(a);
        uint256 d = uint256(rawD) % (rollup.pendingDeposits(owner) + 1);
        uint256 w = uint256(rawW) % (rollup.backing() + d + 1);
        rollup.executeBatch(
            rollup.batchNumber() + 1,
            rollup.stateRoot(),
            root,
            d == 0 ? address(0) : owner,
            d,
            w == 0 ? address(0) : actor(b),
            w
        );
    }

    function withdraw(uint256 seed, uint96 raw) external {
        address owner = actor(seed);
        uint256 amount = uint256(raw) % (rollup.pendingWithdrawals(owner) + 1);
        if (amount == 0) return;
        rollup.withdrawPendingBalance(payable(owner), amount);
        paid += amount;
    }
}

contract RollupInvariantTest {
    Vm private constant vm = Vm(address(uint160(uint256(keccak256("hevm cheat code")))));
    Handler private handler;
    address[] private targets;

    function setUp() public {
        handler = new Handler();
        vm.deal(address(handler), 1_000_000 ether);
        targets.push(address(handler));
    }

    function targetContracts() public view returns (address[] memory) {
        return targets;
    }

    function invariantETHBacksAllCredits() public view {
        Rollup target = handler.rollup();
        uint256 credits = target.backing();
        for (uint256 i; i < 4; i++) {
            credits += target.pendingDeposits(handler.actor(i)) + target.pendingWithdrawals(handler.actor(i));
        }
        require(address(target).balance == credits);
        require(address(target).balance + handler.paid() == handler.deposited());
    }
}
