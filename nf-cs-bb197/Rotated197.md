# A 197-state implementation by rotating the transfer loop

## Checked result

The frozen table
`loop197_m65/candidate.tm`, SHA-256
`948492f1d299acb09b0d3464c5de7ef6e5d510bc09398324a9610c65f52cbbf3`,
has 197 states and 394 binary transition rows. Its blank run reaches the
standard source entry after exactly 72,014 transitions, with registers
`[3,0,0,0,0,0,0,0,0]`, gap 49, and 31 zero spare fields.

The independent action checker verifies 5,605 ordinary instruction domains
and 145 guarded phase domains. Those phases implement all 29 complete
`R6 → R5` transfer loops by the induction below. The certificate uses 20
literal pump lemmas; its independent replay checks 2,749,573 literal
transitions and 139,136 applications of those lemmas. These are finite
certificates for arbitrary natural register values, gap extension, and
spare count, rather than a bounded register-value test.

The primitive reference source has SHA-256
`fdb3fde1f2690cdbf37e164ecf128f6f3d8d8a2a0f173e7de2bd8d4929affa6e`.
Replacing its 29 closed transfer loops by single `M65` instructions gives
the 4,307-site source with SHA-256
`cccaeda909358991cb3a1f8882d97abcab8ab7bb3f8d503ec3030c475ba82ae8`.
The physical table implements that source from blank tape. No fresh Lean
kernel replay is claimed.

## The changed implementation

Relative to the original 198-state table, the new table identifies decoder
state `d:160` with `d:39`. Both states have the same zero arm. The surviving
state uses the former `d:160` one arm. Concretely:

| Transition | Original target | New target |
|---|---|---|
| `d:159`, read `1` | `d:160` | `d:39` |
| `d:39`, read `1` | `d:166` | `d:161` |

Both rows retain their original write bit and right move. The two rows of
`d:160` are removed. All other table rows are literal.

This changes the behavior at old primitive boundaries inside a transfer
loop. Consequently the primitive 198-state certificate cannot be reused
as if each old `CI5` and `CC2` instruction still had its old effect. The
new implementation has a different, fully checked phase interpretation.

Let the old three-instruction loop start at primitive PC `h`:

```
h:     CD6       positive → h+1; zero → h+3
h+1:   CI5       → h+2
h+2:   CC2       → h
```

The new table first performs the old `CD6`. If it was positive, the old
`CI5` address now defers the increment, provided the destination register
is initially zero. At the old `CC2` address, the machine performs a tail
phase: increment `R5`, then either decrement positive `R6` and return to
the same tail address, or exit when `R6` was zero.

In effect, the decrement test has moved from the front of each repeated
cycle to the tail phase. The initial decrement and final deferred
increment keep the total transfer exact.

## Frames and resources

Write `F(p,r,g,s)` for a canonical physical frame at source address `p`
with register vector `r`, gap parameter `g ≥ 49`, and `s ≥ 24` zero spare
fields. The field order is

```
R2, R8, R1, R4, R3, R7, R0, R5, R6.
```

Each register field is a zero followed by `r_i+2` ones. Spare fields have
the fixed word `01`. The instruction path and header match the standard
frame constructor, and the physical state is `d:0`, with the head just
after the leading guard bit. In the certificate, the nine independent
register runs and the independent gap/spare extensions are represented by
11 independent natural exponents.

The physical state `d:0` also occurs during internal work. A visit to it
is not by itself a source boundary. The action checker accepts a phase
endpoint only when the entire tape word, the head displacement, the
state, and the intended instruction address all match the claimed frame.

Let `w` be 1 when the loop's lexical successor is source PC 0, and 0
otherwise. This is the ordinary end-of-program address wrap. Its physical
effect is to move the frame origin left by one cell and add one to the
gap parameter. It adds no spare field.

## The five universal phase contracts

Every phase below preserves all unmentioned registers and all existing
spare contents. The common phase assumptions are that registers are
natural, `R0 > 0`, `R7 = 0`, `g ≥ 49`, and `s ≥ 24`. The table reports
changes to the canonical gap and spare counts.

| Phase | Input registers | Output address and registers | Gap change | Spare change |
|---|---|---|---:|---:|
| Entry zero at `h` | `R5=m`, `R6=0` | `h+3`, `R5=m`, `R6=0` | `w` | 0 |
| Entry positive at `h` | `R5=0`, `R6=N>0` | `h+1`, `R5=0`, `R6=N−1` | 1 | 0 |
| Defer at `h+1` | `R5=0`, `R6=d` | `h+2`, same registers | 0 | 0 |
| Tail positive at `h+2` | `R5=m`, `R6=d>0` | `h+2`, `R5=m+1`, `R6=d−1` | 1 | 1 |
| Tail zero at `h+2` | `R5=m`, `R6=0` | `h+3`, `R5=m+1`, `R6=0` | `w` | 1 |

An exit with `w=1` also shifts the frame head left by one; all other
phases leave its position unchanged. Addresses in this table are taken
modulo the primitive source length. In particular, the last loop's
`h+3` is PC 0.

The tail phases allow arbitrary independent `m` and `d`. They do not
assume a relation between `R1` and `R5+R6`, or any other numerical
relation between the untouched registers. The defer phase does require
`R5=0`. That requirement is essential and is supplied by the source
invariant, rather than inferred from sample runs.

`check_rotated197.py` verifies all five contracts separately at every
one of the 29 literal source-loop locations, including the last wrapped
exit. Thus there are 145 phase domains. The certificate never replaces
the address-specific decoder computation by an assumed generic macro.

## Induction completing a transfer

Consider a source-admitted M65 entry, and write its initial donor value
as `N`.

If `N=0`, the entry-zero contract exits immediately. It leaves every
register unchanged and makes only the possible standard address-wrap
adjustment.

Suppose `N>0`. The source guard gives `R5=0`. The positive entry and defer
contracts establish the first tail frame:

\[
R5=0,\quad R6=N-1,\quad g'=g+1,\quad s'=s.
\]

For each integer `k` with `0 ≤ k ≤ N−1`, induction on `k` gives a tail
frame with

\[
R5=k,\qquad R6=N-1-k,\qquad
g'=g+1+k,\qquad s'=s+k.
\]

When `k<N−1`, the donor is positive, so the checked tail-positive phase
proves the next instance of this statement. The phase preserves `R0>0`
and `R7=0`, and increases the gap and spare counts, so every premise
needed for the next phase remains true. Every phase terminates: its
certificate clock is a finite nonnegative linear expression in its
natural parameters, with a positive constant term.

At `k=N−1`, the donor is zero. The checked tail-zero phase performs the
last deferred increment and exits. The resulting values are

\[
R5=N,\qquad R6=0,\qquad
g_{\mathrm{out}}=g+N+w,\qquad
s_{\mathrm{out}}=s+N.
\]

The head displacement is `−w`. All other registers and existing spare
contents are unchanged. Combining both cases proves the exact admitted
macro contract:

\[
R5_{\mathrm{out}}=R5_{\mathrm{in}}+R6_{\mathrm{in}},\qquad
R6_{\mathrm{out}}=0.
\]

The resource change depends on the initial donor. No constant-resource
or globally linear-time claim is made. Since the gap, spare count, and
destination grow during the repeated tail phases, summing their linear
phase clocks can give a quadratic expression in `N`. This affects
running time, not termination or the register result.

## Why every actual macro call satisfies the guards

The threshold-15 source invariant is hash-bound to the collapsed source.
The independent checker verifies initial-state inclusion and all 5,621
nonhalting abstract transition images, including the saturated addition
for M65. Empty abstract states are treated as unreachable; no physical
domains are removed on that basis.

At every M65 head it proves `R0>0` and `R7=0`. At the 28 ordinary heads it
also proves `R5=0`. At the exceptional first head, primitive PC 39, it
proves `R6=0`. Thus the exceptional head uses only the entry-zero
contract, which permits arbitrary `R5`; each other head either uses that
same zero contract or meets the positive-entry and defer assumptions.

The invariant file SHA-256 is
`885c5527377d89a244f4bbef5689c4fea765dcd37ba852540df11131d9456f0f`.
The guards are proved by closure of the actual source graph, not by a
heuristic exclusion of inconvenient physical inputs.

## Remaining instructions and whole-program composition

The 29 removed source loops each have exactly the literal `CD6;CI5;CC2`
graph above. No outside source edge enters either removed interior
instruction. The checker reconstructs the whole old-to-new PC mapping,
checks the collapsed macro leaf addresses, and independently decodes
every retained source edge. Each original loop terminates by decreasing
its natural donor. Therefore replacing it by M65 preserves the original
register computation, including the unique halting event.

All instructions outside these 29 three-instruction intervals have their
ordinary primitive contract. The certificate covers all 5,605 natural
input domains, including both decrement branches wherever applicable.
It does not require the source invariant to restrict their register
values. The positive and zero decrement domains together cover every
natural value. The unique halting ordinary branch is included.

The collapsed M65 address is the parent of the old leading `CD6` leaf.
That leaf's extra address bit is zero and lies adjacent to the zero
header, so the two canonical entry tape words are identical. Every
retained nonmacro address is literal. Hence the physical phases compose
with the collapsed source at exactly the intended canonical boundaries.

The literal blank startup reaches the initial canonical frame. Ordinary
instruction proofs and the M65 induction then simulate every finite
source execution prefix. No physical phase halts prematurely or gets
stuck; the only admitted physical halt is the checked source halt. The
table therefore halts from blank tape exactly when the same numerical
goal is derivable in the already calibrated source calculus.

## How the finite certificates imply universal contracts

A symbolic tape is a word of literal bits and powers `u^n`, with each
exponent an arbitrary natural number. A pump lemma is checked by a
literal finite TM run on a small window. It proves a boundary-preserving
rewrite

\[
C\,u\longmapsto v\,C
\]

with the same finite control state at the next unit boundary. Repeating
that verified local computation gives `C u^n → v^n C` by induction on
`n`; `n=0` is the unchanged context. The checker also verifies the exact
finite transition count and displacement for one unit.

Literal transition actions, these pump applications, and cyclic word
identities for moving a known bit across a power are then replayed for
every domain. The replayer tracks the full left and right tape words,
the control state, a linear head-position expression, and a linear clock
expression. It reconstructs the claimed endpoint from the phase mode and
the independently decoded source graph, and requires exact equality
after the valid word identities. It does not import the trace producer
or accept an endpoint supplied by it.

The checker also includes every pump interior when calculating physical
coverage. The resulting warm-phase plus startup coverage uses all 197
states and all 394 arms. There is no transition to delete merely because
the source boundaries became coarser.

## Reproduction and calibration boundary

From the workspace or complete archive root:

```bash
python3 sprint_20261124_1155/audit/check_rotated197.py
```

The checker reads the frozen table, primitive and collapsed source files,
the source-invariant certificate, the exact baseline startup endpoint,
and `loop197_m65/rotated-traces.gz`. It writes its complete independent
receipt and phase-edge coverage in that same candidate directory.

The separate root audit in `sprint_20261124_1155/root_audit197` independently
checks the source collapse, invariant guards, exact table quotient, and
blank startup without importing the physical trace producer. Its checks
agree with this action audit.

This improvement preserves the calibration recorded in
`deliverables/reference_snapshot/Ground-calibration.md`, including its
distinction between stored kernel-checked results and the written reverse
comparison of R. Gutin and E. Glazer. It changes the implementation and
the physical proof decomposition. It does not alter the NF/NFU/CS
conventions, claim a fresh Lean run, or create a stronger mathematical
calibration theorem.
