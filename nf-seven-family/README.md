# A seven-family proof search for Quine NF

Seven axiom families suffice for the proof calculus used by the [180-state NF machine](../nf-bb180). The register program shrinks from 2,970 instructions to 2,840. The binary implementation here uses 220 working states. The smallest machine in this repository with the full PA proof still has 180.

## The change in the calculus

One application-congruence scheme replaces two. From `f = g` and `x = y` it gives `f·x = g·y`. Setting either pair equal recovers each old rule. Conversely, applying the two old rules in succession gives the joint rule by transitivity. [JointPA.lean](JointPA.lean) proves equivalence for every context and formula in every model of PA. The result includes nonstandard proof codes. [Projection.lean](Projection.lean) checks the register block that recovers two of the four terms from a single Cantor-paired input.

## The binary machine

[NF7-220.tm](NF7-220.tm) is the literal binary transition table. Start in `k:74` on an all-zero tape. All 220 working states are reachable in its transition graph. One transition enters the separate halt state. [NF7-220.source.sites.json](NF7-220.source.sites.json) gives its register instructions and address layout.

| Check | Result |
| --- | --- |
| Source layout | Lean checks equality of all 2,840 decoded instructions with the seven-family source. |
| Blank tape | The table reaches the clean counter-2 frame after 40,711 transitions and the clean counter-5 frame after 229,892. |
| Physical simulation | The reference kernel checks 7,460 signed branches and 20 repetition lemmas. |
| Independent replay | 136,304 full successor tapes match, with 16 halts in 95,180,798 transitions. |

The remaining proof obligation is to connect the modified seven-family command scanner to the NF refutation criterion inside PA. The [180-state release](../nf-bb180) includes that end-to-end proof for its own table.

## Reproduce the checks

Download and extract [the complete verification and search archive](NF180_further_reductions.zip). Its README gives a guide to the files. In `seven-family/physical`, run the following commands with Lean 4.35.0 and the physical verification archive extracted from the 180-state release.

```sh
python3 replay.py /path/to/extracted/NF180 --kernel --examples
python3 generate_readdressing.py
lean Readdressing.lean
bash bootproof/compile.sh
```

The archive also contains the command-language simplifications and replayable counterexamples for three proposed 179-state tables. Each of those tables fails the intended NF criterion. [SHA256SUMS](SHA256SUMS) records the digests of the files in this directory.
