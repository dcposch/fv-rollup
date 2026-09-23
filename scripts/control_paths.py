#!/usr/bin/env python3
"""Generate a candidate path certificate. Lean must check the result."""

from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
CODE = bytes.fromhex((ROOT / "contract/runtime.hex").read_text().strip().removeprefix("0x"))
MASK = (1 << 256) - 1
ANY, NONZERO = "?", "!"


def signed(value):
    return value if value < 1 << 255 else value - (1 << 256)


def successors(cursor):
    pc, stored = cursor
    stack = list(stored)
    op = CODE[pc]
    following = pc + 1
    if op in (0x00, 0xF3, 0xFD, 0xFE):
        return []
    if op == 0x5F:
        stack.insert(0, 0)
    elif 0x60 <= op <= 0x7F:
        width = op - 0x5F
        stack.insert(0, int.from_bytes(CODE[following:following + width], "big"))
        following += width
    elif 0x80 <= op <= 0x8F:
        stack.insert(0, stack[op - 0x80])
    elif 0x90 <= op <= 0x9F:
        index = op - 0x8F
        stack[0], stack[index] = stack[index], stack[0]
    elif op in (0x01, 0x03, 0x10, 0x11, 0x12, 0x14, 0x16, 0x1B, 0x1C):
        left, right = stack.pop(0), stack.pop(0)
        if isinstance(left, int) and isinstance(right, int):
            operations = {
                0x01: lambda: left + right,
                0x03: lambda: left - right,
                0x10: lambda: int(left < right),
                0x11: lambda: int(left > right),
                0x12: lambda: int(signed(left) < signed(right)),
                0x14: lambda: int(left == right),
                0x16: lambda: left & right,
                0x1B: lambda: right << left if left < 256 else 0,
                0x1C: lambda: right >> left if left < 256 else 0,
            }
            stack.insert(0, operations[op]() & MASK)
        else:
            stack.insert(0, ANY)
    elif op == 0x19:
        value = stack.pop(0)
        stack.insert(0, (~value) & MASK if isinstance(value, int) else ANY)
    elif op == 0x15:
        value = stack.pop(0)
        stack.insert(0, int(value == 0) if isinstance(value, int) else 0 if value == NONZERO else ANY)
    elif op in (0x30, 0x33, 0x34, 0x36, 0x3D, 0x5A):
        stack.insert(0, ANY)
    elif op in (0x35, 0x51):
        stack[0] = ANY
    elif op == 0x20:
        stack.pop(0)
        stack[0] = ANY
    elif op == 0x54:
        stack[0] = ANY
    elif op in (0x50, 0x52, 0x55, 0x3E):
        for _ in range(1 if op == 0x50 else 3 if op == 0x3E else 2):
            stack.pop(0)
    elif op == 0xF1:
        stack = [ANY] + stack[7:]
    elif op in (0x56, 0x57):
        destination = stack.pop(0)
        if not isinstance(destination, int) or CODE[destination] != 0x5B:
            raise ValueError(f"Unresolved or invalid jump at {pc}")
        taken = (destination, tuple(stack))
        if op == 0x56:
            return [taken]
        condition = stack.pop(0)
        taken = (destination, tuple(stack))
        fallthrough = (following, tuple(stack))
        if isinstance(condition, int):
            return [fallthrough if condition == 0 else taken]
        return [taken] if condition == NONZERO else [taken, fallthrough]
    elif op != 0x5B:
        raise ValueError(f"Unsupported opcode {op:02x} at {pc}")
    return [(following, tuple(stack))]


def lean_word(value):
    if value == ANY:
        return ".any"
    if value == NONZERO:
        return ".nonzero"
    return f".exact ⟨{value}⟩"


def certificate_chunks(prefix, table, edges, count):
    ranges = [(start, min(32, count - start)) for start in range(0, count, 32)]
    output = f"private def {prefix}Chunks : List (List Nat) := [\n"
    output += ",\n".join(f"  List.range' {start} {size}" for start, size in ranges)
    output += "\n]\n\n"
    names = []
    for index, (start, size) in enumerate(ranges):
        name = f"{prefix}_chunk_{index}"
        names.append(name)
        output += f"private theorem {name} :\n"
        output += f"    (List.range' {start} {size}).all (indexedControlAt runtimeBytecode {table} {edges}) = true := by\n"
        output += "  decide +kernel\n\n"
    output += f"/-- Small kernel checks certify every row of the {prefix} table. -/\n"
    theorem = "control_indexed_closed" if prefix == "control" else "blocked_control_indexed_closed"
    output += f"theorem {theorem} : indexedControlClosed runtimeBytecode {table} {edges} = true := by\n"
    output += f"  apply indexed_control_chunks_sound {prefix}Chunks (by decide +kernel)\n"
    output += f"  simp only [{prefix}Chunks, List.all_cons, List.all_nil, Bool.true_and,\n    "
    output += ",\n    ".join(", ".join(names[start:start + 4]) for start in range(0, len(names), 4))
    output += "]\n\n"
    return output



def predicate_certificate(module, prefix, theorem, table, predicate, count):
    ranges = [(start, min(32, count - start)) for start in range(0, count, 32)]
    output = "import proofs.generated.ControlPaths\nimport proofs.generated.BlockedControlPaths\n"
    output += "import proofs.support.ControlCallBoundary\nimport proofs.ArrayPredicate\n\n"
    output += "open Ethereum Ethereum.EVM\n\nset_option maxRecDepth 1000000\nset_option maxHeartbeats 0\n\nnamespace Rollup.EVM\n\n"
    output += f"private def {prefix}Chunks : List (List Nat) := [\n"
    output += ",\n".join(f"  List.range' {start} {size}" for start, size in ranges)
    output += "\n]\n\n"
    names = []
    for index, (start, size) in enumerate(ranges):
        name = f"{prefix}_chunk_{index}"
        names.append(name)
        output += f"private theorem {name} :\n"
        output += f"    (List.range' {start} {size}).all (arrayPredicateAt {table} ({predicate})) = true := by\n"
        output += "  decide +kernel\n\n"
    output += "/-- Small kernel checks establish the predicate for every candidate row. -/\n"
    output += f"theorem {theorem} : {table}.all ({predicate}) = true := by\n"
    output += f"  apply array_predicate_chunks_sound {prefix}Chunks (by decide +kernel)\n"
    output += f"  simp only [{prefix}Chunks, List.all_cons, List.all_nil, Bool.true_and,\n    "
    output += ",\n    ".join(", ".join(names[start:start + 4]) for start in range(0, len(names), 4))
    output += "]\n\nend Rollup.EVM\n"
    path = ROOT / f"proofs/generated/{module}.lean"
    if not path.exists() or path.read_text() != output:
        path.write_text(output)


def main():
    states = [(0, ())]
    seen = set(states)
    index = 0
    while index < len(states):
        for following in successors(states[index]):
            if following not in seen:
                seen.add(following)
                states.append(following)
        index += 1
    rows = [f"  ⟨⟨{pc}⟩, [{', '.join(map(lean_word, stack))}]⟩" for pc, stack in states]
    header = """import proofs.support.ControlCursor
import semantics.Bytecode

open Ethereum Ethereum.EVM

namespace Rollup.EVM

/-- Candidate runtime paths. Generated by scripts/control_paths.py. -/
def controlPaths : Array AbstractCursor := #[
"""
    output = header + ",\n".join(rows) + "\n]\n\nend Rollup.EVM\n"
    path = ROOT / "proofs/generated/ControlPaths.lean"
    if not path.exists() or path.read_text() != output:
        path.write_text(output)
    ancestors = {state for state in states if state[0] == 935}
    while True:
        previous = {state for state in states if any(next_state in ancestors for next_state in successors(state))}
        if previous <= ancestors:
            break
        ancestors |= previous
    blocked = [state for state in states if state not in ancestors]
    blocked_rows = [f"  ⟨⟨{pc}⟩, [{', '.join(map(lean_word, stack))}]⟩" for pc, stack in blocked]
    blocked_header = header.replace("controlPaths", "blockedControlPaths").replace(
        "Candidate runtime paths.", "Candidate paths that cannot return to the withdrawal CALL.")
    blocked_output = blocked_header + ",\n".join(blocked_rows) + "\n]\n\nend Rollup.EVM\n"
    blocked_path = ROOT / "proofs/generated/BlockedControlPaths.lean"
    if not blocked_path.exists() or blocked_path.read_text() != blocked_output:
        blocked_path.write_text(blocked_output)
    def edge_rows(table):
        indices = {state: index for index, state in enumerate(table)}
        return ["  [" + ", ".join(str(indices[next_state]) for next_state in successors(state)) + "]"
                for state in table]
    edges_output = "import proofs.generated.ControlPaths\nimport proofs.generated.BlockedControlPaths\n\nnamespace Rollup.EVM\n\n"
    edges_output += "/-- Candidate successor indices. Lean checks every edge. -/\ndef controlEdges : Array (List Nat) := #[\n"
    edges_output += ",\n".join(edge_rows(states)) + "\n]\n\n"
    edges_output += "/-- Candidate edges within the region that excludes the withdrawal CALL. -/\ndef blockedControlEdges : Array (List Nat) := #[\n"
    edges_output += ",\n".join(edge_rows(blocked)) + "\n]\n\nend Rollup.EVM\n"
    edges_path = ROOT / "proofs/generated/ControlEdges.lean"
    if not edges_path.exists() or edges_path.read_text() != edges_output:
        edges_path.write_text(edges_output)
    certificate = "import proofs.generated.ControlEdges\nimport proofs.IndexedControl\n\n"
    certificate += "open Ethereum Ethereum.EVM\n\nset_option maxRecDepth 1000000\nset_option maxHeartbeats 0\n\nnamespace Rollup.EVM\n\n"
    certificate += certificate_chunks("control", "controlPaths", "controlEdges", len(states))
    certificate += certificate_chunks("blockedControl", "blockedControlPaths", "blockedControlEdges", len(blocked))
    certificate += "end Rollup.EVM\n"
    certificate_path = ROOT / "proofs/generated/ControlIndexedPaths.lean"
    if not certificate_path.exists() or certificate_path.read_text() != certificate:
        certificate_path.write_text(certificate)
    predicate_certificate("ControlChildrenCertificate", "children", "control_children_certificate",
                          "controlPaths", "controlChildAt runtimeBytecode", len(states))
    predicate_certificate("BlockedCallCertificate", "blockedCall", "blocked_call_certificate",
                          "blockedControlPaths", "fun cursor => cursor.pc != ⟨935⟩", len(blocked))
    predicate_certificate("ControlCallCertificate", "callBoundary", "control_call_certificate",
                          "controlPaths", "controlCallToTable runtimeBytecode blockedControlPaths", len(states))
    print(f"Generated {len(blocked)} candidates that cannot reach the withdrawal CALL.")
    print(f"Generated {len(states)} candidate states at {len({pc for pc, _ in states})} counters.")


if __name__ == "__main__":
    main()
