# Ground calibration of the 198-state NF+CS candidate

The two endpoints are kernel-checked. In `Unshifted198Calibration.lean`, syntactic consistency of pure NF with its full CS sentence implies the new numerical goal is underivable. Underivability of that same goal implies an A₀ model. A₀ is bare NFU with Dedekind Infinity and full CS. R. Gutin and E. Glazer, *Choice and Consistency Strength in NF and NFU*, v15, Proposition 17.37 and Theorem 21.1 give the written consistency comparison from A₀ to pure NF+CS. Consequently the numerical goal is derivable exactly if NF+CS is inconsistent. The credits and theory-comparison boundary follow the 199-state calibration.

The edited register source emits `row9(a,b)` after the CS strength row, where 199 emitted `row9(a+1,b)`. During proof extraction the first seven rows are available for all indicated parameters. The last two are needed only at b>0. `Unshifted198.rowList` repeats the ordinary K row in their positions at b=0. `Unshifted198.fullRows` lists the nine actual unshifted raw formulas with all b permitted.

## The shared witness

In the ground syntax the CS representative for s is the term w=H(J,Js). The unshifted extensionality row requires (Js)w=Jw to imply J=Js for this same w. This additional obligation can be satisfied in the canonical normalized algebra of a pure NF+CS model. Here B is the abstraction combinator and K produces constant functions. The explicit letter J takes Kt to δₜ, with δₜ(t)=KB and δₜ(x)=B away from t. J takes every nonconstant input to B.

If s=Kt choose w=Ks. Its readback equation (wx)s=sx holds at every x. Also Jw=δₛ differs from both possible values of (Js)w, namely KB and B. If s is nonconstant, take the ordinary CS readback witness and use the fact that Jw differs from Bw at every w. For w=Kt, the operators δₜ and B(Kt) differ: choose Kv≠t, so their respective values there are B and K(tv). For nonconstant w, the required fact is Bw≠B. If Bw=B, applying both sides successively to u,y,x and then replacing u by K(uy) implies (uy)(yx)=(u(Kx))(yx). Taking u to be the identity gives y(yx)=x for all x,y. Substituting y=x=KB contradicts KB≠B. These arguments are checked in `NormalizedSeparation.lean`.

The resulting valuation validates every raw strength instance and every raw extensionality instance, including those with b=0. Conversely, any valuation for the reduced calculus yields an extensional quotient. For the representative of s given by a, the surviving extensionality row with b=app(0,a)>0 uses exactly the CS witness w. This gives the separated-witness law in the quotient. Positive K-equivalent representatives (Kb)0 cover the censored read argument. The quotient therefore gives a valuation for all raw rows. The kernel-checked equivalences are `Unshifted198.nonderiv_iff_separated` and `Unshifted198.nonderiv_iff_full_ground`.

`Unshifted198.new_of_original` directly proves that a derivation of the 199-state numerical goal gives a derivation of the 198-state goal. For the equiconsistency comparison in the other direction the proof uses the pure NF+CS upper model and the A₀ comparison above.

## Replay

Use Lean 4.35.0 and the supplied package pins. Run `lake exe cache get` and `lake env python3 replay.py --jobs 2`. The script checks dependency hashes, recompiles all included non-Mathlib modules, and audits the endpoint axioms. The new modules have individually passed Lean against precompiled dependencies. Their logs are in `receipts/`. Signed binary-table and scanner verification are separate parts of the machine certificate.
