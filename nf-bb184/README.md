# The 184-state variable-marker table for pure NF

On a blank tape the machine halts exactly if pure Quine NF proves a contradiction. The literal transition table is [NF184.tm](NF184.tm). It has 184 reachable working states, 368 binary transitions, blank symbol 0, and start state `k:64`. The separate terminal state is called `halt`. Its SHA-256 is `7764cc84dd1989604d7653b111406419b6bbd601a9294ef01ea2eb297cb58798`.

The default Lean kernel accepted all 7,794 signed register-branch theorems. Lean checked the exact signed-register conclusion in NF184RegisterConclusion.lean, including both implications. [Proof status](proof-status.txt) records this snapshot.

The [verification checkpoint](NF184_verification_checkpoint.zip) contains the Lean sources in `lean/`, the replay scripts in `checks/`, the recorded results in `receipts/`, and the upstream source snapshot. The archived copy of [NF184.tm](NF184.tm) is `machines/variable184/candidate.tm`.

## What changed

The original tester compared its outputs with a fixed constant. The new row compares them with its first argument. Write $D(x,y)=(J(Kx))y$. The emitted formula is

$$((D(x,y)=x)\to(D(x,x)=x))\to y=x.$$

If $x\ne y$, this forces $D(x,y)=x$ and $D(x,x)\ne x$. The construction of a fixed two-valued tester from these varying values and the reverse construction in an NF model appear in [marker-argument.md](marker-argument.md). Reordering the eight rows and sharing physical decoder states took the new table from 186 to 185 to 184. The last emitted row is extensionality and is independent of the batch counter.

## Evidence for the literal table

* The independent simulator passed 48 complete input frames at each of the 2,971 source addresses, totalling 142,608 trials and 88,555,587 binary steps. The finite receipt includes both outcomes at the halt gate.
* The signed program has 2,809 axiom-emitter instructions and 162 other instructions. The register-binding checker reconstructs all 2,809 instructions from the eight emitted words, checking operands and branch destinations. The other 162 match the former program after relocation. The Lean sources give the batch effect, the scanner and its signed start.
* The blank run first reaches the signed start at step 17,265. After exactly 80 more register instructions it reaches PC 111 at binary step 50,923, with header gap 51, 32 zero spare blocks, and register vector $(-1,0,0,2,0,0,0,1,0)$. This is in the domain of the symbolic frame certificates.
* Each symbolic branch quantifies over its variable register widths, gap, spare count and both exterior rays. The complete set treats every applicable normal or signed decrement outcome. Each trace has a positive constant time term, at least 26. An ordinary source step carries a covered frame to its next covered frame. A halting source step reaches the unique absorbing terminal state. Induction along the deterministic source execution therefore transfers a finite halt to the tape. If source execution continues forever, successive live tape boundaries occur at strictly increasing integer times and preclude an intervening tape halt. The universal branch theorems and the concrete blank-to-frame calculations were kernel-checked separately. This last assembly is an ordinary mathematical argument. The package includes no new PA-internal Busy Beaver theorem.

## Replay

Extract the verification checkpoint and run these commands from its root. The first four need Python 3, and the blank replay also needs a C++20 compiler.

```sh
python3 checks/verify.py
python3 checks/register_binding.py machines/variable184/source.sites.json upstream185.zip
python3 checks/boot_verify.py
python3 checks/symbolic_frames.py machines/variable184 --write /tmp/nf184-traces.json.gz
```

For the universal tape proofs, put the pinned toolchain (leanprover/lean4:v4.35.0) on PATH, including its `leanchecker-paranoid`. Read the exact upstream pin from the included upstream release before rebuilding. The command regenerates the full proof terms in temporary batches and passes them to the default Lean kernel.

```sh
python3 checks/check_all.py machines/variable184 machines/variable184/traces.json.gz /tmp/nf184-kernel.json --jobs 2
```

For the ordinary Lean source modules, build the pinned `NF_Eight_Row_185` release in `upstream185.zip` using its replay instructions. From that release's Lake environment, run `lake env python3 /absolute/path/to/checks/check_lean.py /absolute/path/to/upstream-build`. The script sorts local imports and stops on a compiler error or a reported `sorryAx` dependency.

## Other results

* `machines/collapsed183` executes its altered register program on 142,032 independently tested frames. `CollapsedRows.no_goal` exhibits a three-element countermodel to its numerical goal.
* `machines/load187` implements a swap-free proof search. When the top is empty it loads the cache. On a nonempty top it checks for goal 3. Its receipt contains 7,704 default-kernel-checked physical branches.
* `machines/seven192` is a seven-row physical design. `ObservedSeven.goal_iff_nf_refutation` checks the corresponding numerical calculus. See its finite frame receipt for the literal implementation.
* `machines/variable186` is the earlier physical layout for the same source as the 184 table.
* In the original scanner, any positive arithmetic progression of candidate numbers suffices, even with sound replacement of the proof registers at each refill. The statement for pure NF is `ProgressionEnumeration.progression_scanner_iff_nf_refutation`.

The other folders preserve supporting checks and the prior 185-state source release. Each machine's receipt states the checks actually completed on that table.
