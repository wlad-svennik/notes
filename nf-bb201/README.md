# The 201-state Counting machine

[Research note and verification files](https://github.com/wlad-svennik/notes/releases/tag/counting201-zermelo)

Let H say that the released two-symbol machine halts on blank tape, and let Z be Zermelo set theory with full Separation and without Choice or Replacement. The note proves on paper that PA proves ¬H → Con(Z), using Proposition 17.6 of *Choice and Consistency Strength in NF and NFU*, v15. By Gödel’s second incompleteness theorem, consistent Z cannot prove that this machine runs forever. The upper construction and the stronger v15 consistency comparisons supply actual nonhalting in ZF and give a 201-state Busy Beaver bound for both Z and NF with Rosser’s full Axiom of Counting.

The release contains the six-page argument, the 201-state transition table, cited manuscript excerpts, and the Lean sources and replay scripts. The new theorem `Counting201Certificate.halts_iff_numerical_certificate` identifies halting of the literal table with acceptance of a numerical derivation by the ten-row checker. The release also records the false halt that rules out the tested 200-state decoder edit.

Primary table SHA-256: `2ee8eae8b8f11975d20da71969ea4b9242d17b0e5db3789e961cd533460a38f0`.
