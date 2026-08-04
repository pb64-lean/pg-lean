"""Shared axiom policy for pg-lean's `lean_assurance_test` targets.

Every first-party constant in this repository must close over the three
axioms the Lean standard library itself relies on, plus the LRAT-certificate
axioms listed below and nothing else.

`bv_decide` in Lean 4.31 discharges a goal by running the SAT solver and
checking its refutation with a *natively compiled* LRAT checker; the check is
recorded as one axiom per call site, named after the enclosing declaration and
stable across rebuilds. pg-lean uses `bv_decide` only for big-endian byte
(de)composition — recomposing a `UInt32`/`UInt64` from the bytes it was split
into — in `Pg.Protocol.Message` and `Pg.Types.Codec`.

The axioms are listed individually rather than by pattern on purpose: a new
`bv_decide` call site anywhere in the repository produces an unlisted axiom and
fails every assurance target, which forces the choice to be made deliberately.
"""

PG_ALLOWED_AXIOMS = [
    # The Lean standard library's own axioms.
    "propext",
    "Classical.choice",
    "Quot.sound",
    # `Pg.Protocol.pack_unpack`: the four bytes a UInt32 is split into
    # recompose to it (three of the four halves need the solver; the fourth
    # is closed by `bv_normalize` alone and emits no axiom).
    "_private.Pg.Protocol.Message.0.Pg.Protocol.pack_unpack._native.bv_decide.ax_1_5",
    "_private.Pg.Protocol.Message.0.Pg.Protocol.pack_unpack._native.bv_decide.ax_1_10",
    "_private.Pg.Protocol.Message.0.Pg.Protocol.pack_unpack._native.bv_decide.ax_1_15",
    # `Pg.Protocol.getUInt16?_putUInt16` / `getUInt32?_putUInt32`: reading back
    # a big-endian integer yields the integer that was written.
    "_private.Pg.Protocol.Message.0.Pg.Protocol.getUInt16?_putUInt16._native.bv_decide.ax_1_9",
    "_private.Pg.Protocol.Message.0.Pg.Protocol.getUInt32?_putUInt32._native.bv_decide.ax_1_11",
    # `Pg.rdUInt64_putInt64BE` / `Pg.PgInterval.fromBinary_toBinary`: the same
    # recomposition one width up — two UInt32 halves rebuild the UInt64.
    "_private.Pg.Types.Codec.0.Pg.rdUInt64_putInt64BE._native.bv_decide.ax_1_5",
    "_private.Pg.Types.Codec.0.Pg.PgInterval.fromBinary_toBinary._native.bv_decide.ax_1_14",
]
