"""Shared axiom policy for pg-lean's `lean_assurance_test` targets.

Every first-party constant in this repository closes over exactly the three
axioms the Lean standard library itself relies on, and nothing else. There is
no `sorry`, no `native_decide`, and no LRAT certificate anywhere in the trusted
surface.

pg-lean previously used `bv_decide` for big-endian byte (de)composition in
`Pg.Protocol.Message` and `Pg.Types.Codec`. In Lean 4.31 `bv_decide` discharges
a goal by running a SAT solver and checking its refutation with a *natively
compiled* LRAT checker, recording the check as one axiom per call site. Those
seven call sites are gone: the recompositions are now proved at the `Nat` level
by `Nat.shiftLeft_add_eq_or_of_lt` (which turns a disjoint `|||` into `+`)
followed by `omega`, so the `Std.Tactic.BVDecide` imports are gone too.

Keeping this list at exactly three is the point: any new axiom, from any
tactic, in any module under `Pg`, fails every assurance target and forces the
choice to be made deliberately.
"""

PG_ALLOWED_AXIOMS = [
    "propext",
    "Classical.choice",
    "Quot.sound",
]
