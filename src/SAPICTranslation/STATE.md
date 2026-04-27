# State / Cells / Locks: SAPIC+ encoding design

This document captures the design decisions for translating the cell- and
state-related IR constructs (`LRead`, `LWrite`, API agents, …) to SAPIC+.
It corresponds to the work after the `sapic-without-state` tag.

## Goal

Produce a SAPIC+ encoding of CryptoChoreo's `cells:` blocks that

1. Lets `tamarin-prover` verify state-using protocols end-to-end (parse,
   well-formedness, executability sanity lemmas pass, security lemmas
   meaningful).
2. Mirrors the *NoAxioms* memory model of the ProVerif backend: exactly
   one logical value per `(cell, address)` at a time, with mutual
   exclusion across read-modify-write critical sections.
3. Is idiomatic Tamarin/SAPIC+, using the native `lookup`/`insert`/`lock`
   primitives rather than re-implementing ProVerif's channel-based
   encoding.

## IR shape

The IR has two relevant constructors (`src/Local.hs`):

```haskell
data LAtomic f v = ...
    | LRead   String v (Term f v) (LAtomic f v)
    | LWrites (LWrites f v)

data LWrites f v
    = LWrite String (Term f v) (Term f v) (LWrites f v)
    | Local  (Local f v)
```

A typical critical section reads:

```
LRead "cell" "v" addr (
  ... compute ...
  LWrites (LWrite "cell" addr new_value (Local rest))
)
```

i.e. read, compute, write, return to plain choreography.

## Encoding table

| IR construct                         | SAPIC+                                                         |
|--------------------------------------|----------------------------------------------------------------|
| `LRead "cell" v addr a`              | `lookup <'cell', addr> as v in TR(a) else INIT_PATH(v, a)`     |
| `LWrite "cell" addr value w`         | `insert <'cell', addr>, value; TR(w)`                          |
| Read-modify-write critical section   | wrap with `lock <'cell', addr>; ...; unlock <'cell', addr>;`   |
| `[API]` agent body                   | wrap with `lock <'api'>; ...; unlock <'api'>;`                 |

`INIT_PATH(v, a)` is the cell-not-yet-written branch:

```
let v = memory_initial_value in
insert <'cell', addr>, v;
TR(a)
```

The `<'cell', addr>` key prefixes with the literal cell name so different
cells don't collide in a single global table.

## Subtle points / decisions

### A. Atomicity is explicit via `lock`/`unlock`

ProVerif's channel-based encoding is implicitly atomic per `(cell,
address)` because there's only one message in flight on the cell channel
at any time. SAPIC+ tables are *not* atomic in this sense: concurrent
sessions can `lookup` between each other's `lookup` and `insert`. A
read-modify-write executed without a lock allows lost-update style
attacks the choreography didn't intend.

**Decision.** When the syntactic continuation of an `LRead` reaches an
`LWrite` on the same `(cell, addr)`, wrap the read-through-write region
with `lock <'cell', addr>`/`unlock <'cell', addr>`. Read-only accesses
(`LRead` not followed by an `LWrite` on the same key) need no lock.

### B. Initialization via the `else` branch of `lookup`

ProVerif's backend uses a separate initializer process backed by a
"this addr has been initialized" table. SAPIC+'s `lookup ... else Q`
already gives us a place to handle the not-yet-written case.

**Decision.** Translate `LRead` so that the `else` branch
(a) binds `v = memory_initial_value`, (b) inserts that initial value so
subsequent lookups succeed, and (c) runs the same continuation as the
`in` branch. The continuation gets duplicated between the two branches,
which is acceptable for correctness (and Tamarin handles the duplication
well in practice).

### C. `UnRead` has no SAPIC+ analogue and isn't needed

ProVerif's `UnRead` puts the value back on read-but-not-written paths to
preserve the in-flight invariant. SAPIC+ `lookup` is non-destructive, so
there is nothing to put back.

**Decision.** Drop the concept entirely on the SAPIC side. Read-only
paths emit just a `lookup` with no compensating write.

### D. WithAxioms-style counter machinery is deferred

ProVerif's WithAxioms model adds per-cell counters and `write_<cell>`
events to recover monotonic-state reasoning that the Horn-clause
abstraction would otherwise lose. Tamarin's table semantics is precise
out of the box, so there is nothing equivalent to recover.

**Decision.** Implement only the NoAxioms-equivalent encoding for now.
If a future use case needs counter-style invariants (e.g. for
SAPIC+'s ProVerif export, where the same Horn-clause limitation
re-appears) we can add them as user-declared `restriction` blocks.

### E. API baton is a single global lock

ProVerif uses a private `api_call_lock` channel and a `api_call_baton`
constant to enforce that at most one API call runs at a time across the
whole system.

**Decision.** Translate to a single global lock keyed on a fixed string
constant: wrap each `[API]`-flagged agent's body with
`lock <'api'>; ...; unlock <'api'>;`. The `isAPI` bit is already plumbed
through to the per-agent local IR in `app/Main.hs`.

### F. Lock granularity: per-`(cell, address)`

Two reasonable defaults:

- **Per-cell** — block all accesses to a cell while one is in flight.
  Conservative. Matches ProVerif's "one-in-flight" semantic if cells are
  typically single-address.
- **Per-`(cell, address)`** — block only the specific address being
  modified. Permits concurrent access to other addresses of the same cell.
  Idiomatic Tamarin.

**Decision.** Per-`(cell, address)`. Choreographies with multi-address
cells (e.g. a session-state map keyed by session id) benefit from
parallelism here, and the per-(cell, address) lock matches Tamarin
patterns. Revisit if a real example needs coarser granularity.

### G. Which atomic-section primitive to use

SAPIC+ supports both `lock t; ... unlock t;` (releaseable mutex) and
`new ~l; insert <'lock', t>, ~l; ... lookup <'lock', t> as l' in (...)`
patterns. `lock`/`unlock` is the documented mutex; it's what we use.

## Implementation plan

The phases below correspond to TaskCreate items #14-#18.

1. **Phase 1 — `LWrite` standalone.** `insert <'cell', addr>, value;`.
2. **Phase 2 — `LRead` with else-branch init.** As in §B.
3. **Phase 3 — Locks around read-modify-write.** Walk the continuation;
   when an `LRead` reaches an `LWrite` for the same `(cell, addr)` before
   the IR exits the `LAtomic`, wrap with `lock`/`unlock`.
4. **Phase 4 — Test on `declassify-or-delete`** (simplest cell-using
   example, no API).
5. **Phase 5 — API baton lock.** As in §E. Test on `chat-server`.

## Future work

- **Counter-based invariants for SAPIC+'s ProVerif export.** Re-introduce
  a WithAxioms-equivalent encoding (counters, `write_<cell>` events, and
  matching `restriction` blocks) if needed for the ProVerif round-trip.
- **Cell deletion (`delete <'cell', addr>;`).** Currently no IR
  construct corresponds; add when a choreography surfaces the need.
- **Coarser lock granularity** if the per-`(cell, address)` lock proves
  too fine for some protocol.
