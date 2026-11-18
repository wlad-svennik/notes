import NFUInterpretsNF
import NFSpecker

set_option autoImplicit false

/-!
# NF and NFU + Infinity are mutually interpretable

Both directions, in the form "the interpreted structure is a model, uniformly in the model".
The first half is `nfu_inf_interprets_nf` (the term model on a cut). The second half is the
identity interpretation: a model of NF, with every object declared a set, is a model of NFU, and
Infinity holds in it by Specker's theorem (`nf_interprets_nfu_inf`).
-/

namespace NFUCut

open ConNF.NF (IsNF)

/-- **NF and NFU + Infinity are mutually interpretable.**

(1) There are formulas `δ`, `ε`, `η` of the language of NFU, without parameters, such that in
every model of NFU + Infinity the objects satisfying `δ`, with `ε` as membership and `η` as
equality, form a model of NF.

(2) Every model of NF, with membership unchanged and every object declared a set, is a model
of NFU + Infinity. -/
theorem nf_nfu_inf_mutually_interpretable :
    (∃ δ ε η : Fml, ∀ (V : Type) [Nonempty V] (M : Model V) [Fact M.Infinity],
      ∃ (W : Type) (mem : W → W → Prop)
        (π : {x : V // Sat M.mem M.isSet δ (fun _ => x)} → W),
        IsNF W mem ∧ Function.Surjective π ∧
        (∀ x y, π x = π y ↔ Sat M.mem M.isSet η (Function.update (fun _ => x.1) 103 y.1)) ∧
        (∀ x y, mem (π x) (π y) ↔
          Sat M.mem M.isSet ε (Function.update (fun _ => x.1) 103 y.1))) ∧
    (∀ (V : Type) (mem : V → V → Prop), IsNF V mem →
      ∃ (_ : Nonempty V) (M : Model V), M.mem = mem ∧ (∀ x, M.isSet x) ∧ M.Infinity) :=
  ⟨nfu_inf_interprets_nf, fun _ _ h => nf_interprets_nfu_inf h⟩

end NFUCut
