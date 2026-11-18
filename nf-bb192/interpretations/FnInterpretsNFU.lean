import FnInfinity
import NFUJensen
import NFUConsistent

set_option autoImplicit false

/-!
# FunctionNF interprets NFU + Infinity

* The translation `nfuTranslation` of the language of set theory into FunctionNF: the domain is
  everything, equality is equality, and `x ∈ y` is "all values of `y` are `⊤` or `⊥`, and
  `y · x = ⊤`".
* In a model `M` of `𝗙𝗡𝗙` the interpreted structure is `(M, Mem)`, which satisfies NFU
  (`FnBool.lean`) and has a universe that is not finite (`FnInfinity.lean`).
* **Results**: `fnInterpretsNFUI : 𝗙𝗡𝗙 ⊳ 𝗡𝗙𝗨𝗜`, and by composition with `𝗡𝗙𝗨𝗜 ⊳ 𝗡𝗙`,
  `fnInterpretsNF : 𝗙𝗡𝗙 ⊳ 𝗡𝗙`.
-/

namespace FFL.FirstOrder.FNF

open JensenNFU (TFm IsNFU UnivInfinite)
open DirectTranslation

/-! ### Transport of NFU and of Infinity along a bijection -/

section transport

variable {N M : Type} {memN : N → N → Prop} {memM : M → M → Prop} (e : N → M)

theorem sat_map (hinj : Function.Injective e) (hsurj : Function.Surjective e)
    (hmem : ∀ a b, memN a b ↔ memM (e a) (e b)) (φ : TFm) :
    ∀ env : List N, TFm.Sat memN φ env ↔ TFm.Sat memM φ (env.map e) := by
  induction φ with
  | mem i j =>
    intro env
    simp only [TFm.Sat, List.getElem?_map]
    constructor
    · rintro ⟨a, b, ha, hb, h⟩
      exact ⟨e a, e b, by rw [ha]; rfl, by rw [hb]; rfl, (hmem a b).mp h⟩
    · rintro ⟨a, b, ha, hb, h⟩
      cases hi : env[i]? with
      | none => rw [hi] at ha; exact absurd ha (by simp)
      | some a' =>
        cases hj : env[j]? with
        | none => rw [hj] at hb; exact absurd hb (by simp)
        | some b' =>
          rw [hi] at ha
          rw [hj] at hb
          have ea : e a' = a := by simpa using ha
          have eb : e b' = b := by simpa using hb
          exact ⟨a', b', rfl, rfl, (hmem a' b').mpr (by rw [ea, eb]; exact h)⟩
  | eq i j =>
    intro env
    simp only [TFm.Sat, List.getElem?_map]
    constructor
    · rintro ⟨a, b, ha, hb, h⟩
      exact ⟨e a, e b, by rw [ha]; rfl, by rw [hb]; rfl, by rw [h]⟩
    · rintro ⟨a, b, ha, hb, h⟩
      cases hi : env[i]? with
      | none => rw [hi] at ha; exact absurd ha (by simp)
      | some a' =>
        cases hj : env[j]? with
        | none => rw [hj] at hb; exact absurd hb (by simp)
        | some b' =>
          rw [hi] at ha
          rw [hj] at hb
          have ea : e a' = a := by simpa using ha
          have eb : e b' = b := by simpa using hb
          exact ⟨a', b', rfl, rfl, hinj (by rw [ea, eb]; exact h)⟩
  | neg φ ih => intro env; simp only [TFm.Sat, ih env]
  | and φ ψ ih1 ih2 => intro env; simp only [TFm.Sat, ih1 env, ih2 env]
  | all t φ ih =>
    intro env
    simp only [TFm.Sat]
    constructor
    · intro h a
      obtain ⟨a', rfl⟩ := hsurj a
      exact (ih (a' :: env)).mp (h a')
    · intro h a
      exact (ih (a :: env)).mpr (h (e a))

theorem isNFU_of_equiv (hinj : Function.Injective e) (hsurj : Function.Surjective e)
    (hmem : ∀ a b, memN a b ↔ memM (e a) (e b)) (h : IsNFU M memM) : IsNFU N memN where
  ext x y hne hxy := hinj (h.ext (e x) (e y)
    (by obtain ⟨z, hz⟩ := hne; exact ⟨e z, (hmem z x).mp hz⟩) fun z => by
      obtain ⟨z', rfl⟩ := hsurj z
      rw [← hmem, ← hmem]
      exact hxy z')
  comprehension t Γ φ hs params hp := by
    obtain ⟨y, hy⟩ := h.comprehension t Γ φ hs (params.map e) (by simpa using hp)
    obtain ⟨y', rfl⟩ := hsurj y
    exact ⟨y', fun x => (hmem x y').trans ((hy (e x)).trans
      (sat_map e hinj hsurj hmem φ (x :: params)).symm)⟩

theorem univInfinite_of_equiv (hinj : Function.Injective e) (hsurj : Function.Surjective e)
    (hmem : ∀ a b, memN a b ↔ memM (e a) (e b)) (h : UnivInfinite memM) :
    UnivInfinite memN := by
  obtain ⟨F, h1, h2, h3⟩ := h
  obtain ⟨F', rfl⟩ := hsurj F
  refine ⟨F', fun x hx => (hmem _ _).mpr (h1 (e x) fun z hz => ?_),
    fun a ha b a' ha' => (hmem _ _).mpr (h2 (e a) ((hmem _ _).mp ha) (e b) (e a') fun z => ?_),
    fun u hu hF => h3 (e u) (fun z => ?_) ((hmem _ _).mp hF)⟩
  · obtain ⟨z', rfl⟩ := hsurj z
    exact hx z' ((hmem _ _).mpr hz)
  · obtain ⟨z', rfl⟩ := hsurj z
    rw [← hmem, ← hmem, ha' z']
    exact or_congr Iff.rfl ⟨fun h => by rw [h], fun h => hinj h⟩
  · obtain ⟨z', rfl⟩ := hsurj z
    exact (hmem _ _).mp (hu z')

end transport

/-- `Jensen.models_nfui_of_isNFU` for a structure given with its relation symbols, not through
its membership relation. -/
theorem models_nfui' {W : Type} [SetStructure W] [Nonempty W] [s : Tarski.Structure ℒₛₑₜ W]
    [Tarski.Structure.Eq ℒₛₑₜ W] [Tarski.Structure.Mem ℒₛₑₜ W]
    (h : IsNFU W (fun a b : W => a ∈ b)) (hinf : UnivInfinite (fun a b : W => a ∈ b)) :
    W↓[ℒₛₑₜ] ⊧* 𝗡𝗙𝗨𝗜 := by
  rcases SetTheory.standardStructure_unique W s
  exact SetTheory.Jensen.models_nfui_of_isNFU h hinf

/-! ### The translation -/

/-- The formula for membership: all values of `y` are `⊤` or `⊥`, and `y · x = ⊤`.
Variable `0` is `x` and variable `1` is `y`. -/
def memφ : Semisentence ℒλ 2 :=
  (∀¹ (eqF (appT #2 #0) ttT ⋎ eqF (appT #2 #0) ffT)) ⋏ eqF (appT #1 #0) ttT

lemma memφ_val {M : Type} [Tarski.Structure ℒλ M] [Tarski.Structure.Eq ℒλ M] (x y : M) :
    (⟨memφ⟩ : Semiformula.Operator ℒλ 2).val ![x, y] ↔ Mem x y := by
  simp [Semiformula.Operator.val, memφ, eval_eqF, val_appT, val_ttT, val_ffT, Mem, IsSet]

/-- The interpretation of the relation symbols. -/
def nfuRel : {k : ℕ} → (ℒₛₑₜ).Rel k → Semiformula.Operator ℒλ k
  | _, Language.Set.Rel.eq => Semiformula.Operator.Eq.eq
  | _, Language.Set.Rel.mem => ⟨memφ⟩

/-- **The translation of the language of set theory into FunctionNF.** -/
def nfuTranslation : DirectTranslation 𝗙𝗡𝗙 ℒₛₑₜ where
  domain := ⟨⊤⟩
  rel := nfuRel
  func := fun f ↦ Empty.elim f
  domain_nonempty := by
    apply Theory.Proof.complete_on_eq_models.{_, 0}
    intro M _ _ _ _
    simp [models_iff, Semiformula.Operator.val]
  func_defined := fun f ↦ Empty.elim f
  preserve_eq := by
    apply Theory.Proof.complete_on_eq_models.{_, 0}
    intro M _ _ _ _
    have : nfuRel (Language.Eq.eq : (ℒₛₑₜ).Rel 2) = Semiformula.Operator.Eq.eq := rfl
    simp [models_iff, this, Semiformula.Operator.val, Semiformula.Operator.Eq.sentence_eq]

section model

variable {M : Type} [Tarski.Structure ℒλ M] [Tarski.Structure.Eq ℒλ M] [Nonempty M]
  [hM : M↓[ℒλ] ⊧* 𝗙𝗡𝗙]

/-- The membership relation of the interpreted structure. -/
instance nfuModel_setStructure : SetStructure (nfuTranslation.Model M) :=
  ⟨fun y x ↦ Mem (x : M) (y : M)⟩

lemma nfuModel_mem_iff (a b : nfuTranslation.Model M) : a ∈ b ↔ Mem (a : M) (b : M) := Iff.rfl

instance nfuModel_mem : Tarski.Structure.Mem ℒₛₑₜ (nfuTranslation.Model M) where
  mem a b := by
    have h1 : (Semiformula.Operator.Mem.mem : Semiformula.Operator ℒₛₑₜ 2).val ![a, b] ↔
        Tarski.Structure.rel (L := ℒₛₑₜ) Language.Mem.mem ![a, b] := by
      simp [Semiformula.Operator.val, Semiformula.Operator.Mem.sentence_eq, Semiformula.eval_rel,
        Matrix.fun_eq_vec_two]
    rw [h1, Model.rel_iff]
    have h2 : (fun i ↦ ((![a, b] i : nfuTranslation.Model M) : M)) = ![(a : M), (b : M)] := by
      funext i; fin_cases i <;> rfl
    rw [h2]
    exact memφ_val _ _

/-- An object of the model, as an object of the interpreted structure. -/
def toModel (a : M) : nfuTranslation.Model M :=
  ⟨a, by simp [DirectTranslation.Dom, nfuTranslation, Semiformula.Operator.val]⟩

/-- **In a model of `𝗙𝗡𝗙`, the interpreted structure is a model of `𝗡𝗙𝗨𝗜`.** -/
theorem nfuModel_models : (nfuTranslation.Model M)↓[ℒₛₑₜ] ⊧* 𝗡𝗙𝗨𝗜 := by
  have hinj : Function.Injective (fun a : nfuTranslation.Model M => (a : M)) :=
    fun a b h => by cases a; cases b; cases h; rfl
  have hsurj : Function.Surjective (fun a : nfuTranslation.Model M => (a : M)) :=
    fun a => ⟨toModel a, rfl⟩
  exact models_nfui' (isNFU_of_equiv _ hinj hsurj (fun a b => nfuModel_mem_iff a b) isNFU)
    (univInfinite_of_equiv _ hinj hsurj (fun a b => nfuModel_mem_iff a b) univInfinite)

end model

/-- **FunctionNF interprets NFU + Infinity.** -/
instance fnInterpretsNFUI : 𝗙𝗡𝗙 ⊳ 𝗡𝗙𝗨𝗜 where
  trln := nfuTranslation
  interpret_theory φ hφ := by
    apply Theory.Proof.complete_on_eq_models.{_, 0}
    intro M _ _ _ _
    exact DirectTranslation.Model.translate_iff.mpr
      (models_theory_iff.mp nfuModel_models φ hφ)

/-- **FunctionNF interprets NF**, by composition with `𝗡𝗙𝗨𝗜 ⊳ 𝗡𝗙`. -/
instance fnInterpretsNF : 𝗙𝗡𝗙 ⊳ 𝗡𝗙 :=
  DirectInterpretation.comp SetTheory.nfuInterpretsNF fnInterpretsNFUI

/-- **The syntactic transformation.** The translation of a theorem of `𝗡𝗙𝗨𝗜` is a theorem of
`𝗙𝗡𝗙`. -/
theorem fn_provable_translate_of_nfui {σ : Sentence ℒₛₑₜ} (h : 𝗡𝗙𝗨𝗜 ⊢ σ) :
    𝗙𝗡𝗙 ⊢ fnInterpretsNFUI σ :=
  DirectInterpretation.sound fnInterpretsNFUI h

end FFL.FirstOrder.FNF

#print axioms FFL.FirstOrder.FNF.fnInterpretsNFUI
#print axioms FFL.FirstOrder.FNF.fnInterpretsNF
