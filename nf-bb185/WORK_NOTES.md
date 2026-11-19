# Continuing the 185-state pure NF search

## Starting point

The incumbent binary table has SHA-256 `5504746071e10a0555754b55efc2da348ebfb1f8e8ab5bc7af474eaad81f60fe`. Extract [NF185_Research_Handoff.zip](NF185_Research_Handoff.zip) for the search programs and data named below. The complete proof archive is also included there so an extracted handoff works on its own.

The eight-schema register program first fit in 188 states. Three edits to its binary decoder reduced it through 187 and 186 to 185. Each edit preserves the register control graph. Inside the proof archive, `descent/replay.py` applies the edits from the 188 seed and reproduces the published 185 table byte for byte. The sole source instruction with a zero branch to halt is PC 2942.

## Why one promising 184-state table fails

One 184-state table passed all 141,936 one-instruction tape fixtures, across 2,957 instructions. The deletion removed two instructions that cleared the cache after the goal test. If its old value was h ≥ 4, the next stack pop added h − 4 to the popped formula code. An axiom command followed by five comparison commands reaches cache 241 with stack [122, 0]. The next two pops produce 359 and 355. Another 88 pops leave 3, and the following command halts. The 97-command word produces the halt independently of a derivation of the goal. The handoff includes the literal transition edit, numerical listing check, cache trace and Lean proof in `carry/`.

A second family balanced the four decrements that identify code 3. On 61 starting layouts, the factoring scan recorded 3,064 smaller table proposals, including overlap across hosts. The 722 register programs counted separately within those hosts all accepted both 1 and 3 among inputs 0 through 15. Code 1 means J = J, a derivable equality. Code 3 means (JJ) = J, the intended contradiction. Compare the acceptance condition when changing the shape of the decoder.

## Search coverage and next experiments

The handoff contains 60 alternative 185-state tables, with their prefix-addressed sources and finite receipts in `equivalent-layouts/`. Each has the baseline register control graph. The main table has the complete end-to-end proof. A new table needs a physical simulation and blank-tape startup argument. A changed register program also needs a proof that its halting condition still characterizes an NF refutation.

The new local merger search tried bringing the predecessors of two different states into one common state. It tested 16,836 pairs, allowing a separate write and head movement on each incoming edge. At radius 7 and bounded join depth 18, 329 pairs survived the sampled-window screen and none survived all computed windows. This rules out those bounded witnesses on this table. The source, numeric table and settings are included.

Two alternatives furnish smaller register programs and independent physical seeds. A seven-schema fused program has a 186-state table that passed 143,232 frames. An exact 2,839-instruction program has a 190-state table that passed 136,272 frames. The handoff also contains a separate cross-diagonal 186-state table with its complete pure NF halting proof. `pure-alternatives.md` records exactly which links are proved for each. `theory/README.md` lists additional proven congruence reductions and their measured costs.

## First commands

After extracting the handoff, run

```sh
cd NF185_Research_Handoff
sha256sum -c SHA256SUMS
python3 search/continue.py --seed 198 --rounds 5000 --output /tmp/nf184-candidate.tm
python3 carry/replay.py
```

For the shared-state search, use GCC with C++20 support.

```sh
g++ -O3 -std=c++20 search/local-merger/windows.cpp -o /tmp/nf185-windows
g++ -O3 -std=c++20 search/local-merger/helpers.cpp -o /tmp/nf185-helpers
/tmp/nf185-windows 7 1 /tmp/nf185-windows.bin < data185-eight/alternate.in
/tmp/nf185-helpers data185-eight/alternate.in /tmp/nf185-windows.bin 18 28
```

The factoring scan can be replayed for the first host with `python3 search/factoring/scan.py 0 1`, or for all 61 with `python3 search/factoring/scan.py 0 61`. It writes its results in the current directory. The archive contains the original per-host receipts in `receipts/`. There is no minimality claim for 185.
