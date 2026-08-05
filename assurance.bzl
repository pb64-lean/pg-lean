"""Shared axiom policy for pg-lean's `lean_assurance_test` targets.

Every first-party constant in this repository closes over exactly the three
axioms the Lean standard library itself relies on, and nothing else. There is
no `sorry`, no `native_decide`, and no LRAT certificate anywhere in the trusted
surface.

The big-endian byte (de)composition proofs in `Pg.Protocol.Message` and
`Pg.Types.Codec` operate at the `Nat` level. They use
`Nat.shiftLeft_add_eq_or_of_lt` (which turns a disjoint `|||` into `+`) followed
by `omega`, and do not import `Std.Tactic.BVDecide` or depend on its natively
checked LRAT certificates.

The exact three-item list makes every other axiom, from any tactic in any
module under `Pg`, fail every assurance target unless the policy is explicitly
changed.
"""

PG_ALLOWED_AXIOMS = [
    "propext",
    "Classical.choice",
    "Quot.sound",
]
