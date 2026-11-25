# Proposed edits to Logical independence

Target: https://wiki.bbchallenge.org/wiki/Logical_independence

Based on revision **11626**, dated **24 November 2026, 13:40:46 UTC**.
This proposal edits that existing page. It does not create another wiki page.

The three published construction records are **NF 173**, **NF + AxCount 182**
and **NF + CS 197**. All source links below point to the published release
packages in commit `531645423e75a85b9af277d36672674fbf265dc6` or their current
repository locations.

## 1. Results by Theory: replace the three relevant rows

The table's second column is headed "Upper bound on N_T (states)". The
replacements retain its existing bound figures and show the smaller
construction counts explicitly. They do not silently assert new PA or
Zermelo transfer theorems. Leave the intervening ZF, Zermelo and PA rows
in their current positions.

### NF + CS row

```mediawiki
|-
| New Foundations (NF) + Cantorian Sets (CS)
| 199 [https://github.com/wlad-svennik/notes/tree/main/nf-cs-bb199 Source]<br />Latest construction: '''197 states''' [https://github.com/wlad-svennik/notes/tree/main/nf-cs-bb197 Release]<ref group="footnote" name="nf-implementation-records-2026">The newer figures are complete binary implementation records, with blank-tape initialization included and the terminal halt state excluded. Their release notes distinguish implementation verification from inherited logical calibration. The older independence-bound entries are retained here; this update does not assert new PA or Zermelo bounds for the reduced tables.</ref>
```

### NF + AxCount row

```mediawiki
|-
| New Foundations (NF) + Axiom of Counting (AxCount)
| 187 [https://github.com/wlad-svennik/notes/tree/main/nf-axcount-bb187 Source]<br />Latest construction: '''182 states''' [https://github.com/wlad-svennik/notes/tree/main/nf-axcount-bb182 Release]<ref group="footnote" name="nf-implementation-records-2026" />
```

### NF / Mac Lane row

```mediawiki
|-
| New Foundations (NF) / Mac Lane
| 177 [https://github.com/wlad-svennik/notes/tree/main/nf-bb177 Source]<br />Latest NF construction: '''173 states''' [https://github.com/wlad-svennik/notes/tree/main/nf-bb173 Release]<ref group="footnote" name="nf-implementation-records-2026" />
```

## 2. NF history table

Change its caption to:

```mediawiki
|+History of New Foundations (NF) refutation-search machines
```

Append this row after the 177-state entry, immediately before that table's
closing `|}`:

```mediawiki
|-
|173
|25 November 2026
|R. Gutin and E. Glazer
|[https://github.com/wlad-svennik/notes/blob/main/nf-bb173/NF_173.tm Transition table]
|[https://github.com/wlad-svennik/notes/tree/main/nf-bb173 Portable implementation certificates]; inherited NF calibration includes written arguments.<ref name="nf173-release">R. Gutin and E. Glazer, [https://github.com/wlad-svennik/notes/tree/main/nf-bb173 ''Pure NF: a 173-state binary machine''], 25 November 2026.</ref>
```

## 3. First With Rosser's Axiom of Counting subsection

In the opening paragraph of the subsection under **NF vs Mac Lane vs other
set theories**, replace its final sentence describing 187 states as the
current record with the following. Keep the preceding definition and the
following ZFC consistency sentence.

```mediawiki
On 25 November 2026, R. Gutin and E. Glazer published a '''182-state''' implementation of the NF + AxCount refutation search. It preserves the 3,397-instruction source and full Rosser Counting over internal natural numbers. The release includes portable verification, a full physical-phase and blank-start kernel replay, and a separate statement of the inherited calibration's written components.<ref name="axcount182-release">R. Gutin and E. Glazer, [https://github.com/wlad-svennik/notes/tree/main/nf-axcount-bb182 ''NF + full AxCount: 182-state binary machine''], 25 November 2026.</ref>
```

## 4. With the Axiom of Cantorian Sets subsection

Replace only its final sentence describing 199 states as current with:

```mediawiki
The latest construction has '''197 working states''', with a certificate dated 24 November 2026. Its full-CS proof-search source is preserved; the release supplies a portable certificate for universal symbolic phases, the source invariant and the complete blank-tape startup, together with the inherited calibration notes.<ref name="nfcs197-release">R. Gutin and E. Glazer, [https://github.com/wlad-svennik/notes/tree/main/nf-cs-bb197 ''NF + CS: a 197-state binary Turing machine''], certificate dated 24 November 2026.</ref>
```

## 5. Historical Counting presentation

In the later **With Rosser's Axiom of Counting** subsection, under
**Implementation theory: The combinatory calculus**, replace its first
sentence with:

```mediawiki
The earlier 187-state Counting presentation uses the same three primitives.
```

This preserves the displayed older presentation without relabelling its
formulas as the literal 182-state enumerator.

## 6. Verification-status paragraph

At the end of the NF section, immediately before **Peano Arithmetic (PA)**,
replace the final paragraph about formalization and clean builds with:

```mediawiki
The November 2026 reductions distinguish the literal-machine implementation proofs from their logical calibrations. The 173-state NF and 182-state AxCount packages include standalone Lean-kernel component certificates; the 197-state CS package includes universal symbolic phase checks and written loop-composition arguments. The inherited theory comparisons retain the written steps identified in the release notes, so these packages are not presented as one newly completed end-to-end Lean formalization. In particular, a new PA or Zermelo bound for the exact reduced tables requires the corresponding internal arithmetic transfer; the smaller state counts alone do not supply that result.<ref name="nf173-release" /><ref name="axcount182-release" /><ref name="nfcs197-release" />
```

## Suggested edit summary

Update NF-family construction records to 173, 182 and 197 states; add release
sources and verification scope; retain the existing arithmetic-bound claims.

These are proposed wiki edits. The live wiki has not been changed.
