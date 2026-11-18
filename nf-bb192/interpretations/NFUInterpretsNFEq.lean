import MutualInterpretability

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

/-!
# The interpretation of NF in NFU + Infinity with equality interpreted by equality

In `nfu_inf_interprets_nf` the equality of NF is interpreted by a formula `η`. Here the domain
is cut down to the least member of each `η`-class, so that equality is interpreted by equality.
This is the form of interpretation used in the library `Foundation` (`DirectTranslation`).
-/

namespace ConNF.NF

/-- `IsNF` is invariant under isomorphism. -/
theorem IsNF.of_bijective {A W : Type} {memA : A → A → Prop} {mem : W → W → Prop} (e : A → W)
    (he : Function.Bijective e) (hmem : ∀ a b, memA a b ↔ mem (e a) (e b)) (h : IsNF W mem) :
    IsNF A memA := by
  have hsat : ∀ (φ : Fm) (env : List A), Sat memA φ env ↔ Sat mem φ (env.map e) := by
    intro φ
    induction φ with
    | mem i j =>
      intro env
      simp only [Sat, List.getElem?_map]
      constructor
      · rintro ⟨a, b, ha, hb, hab⟩
        exact ⟨e a, e b, by rw [ha]; rfl, by rw [hb]; rfl, (hmem a b).mp hab⟩
      · rintro ⟨a', b', ha, hb, hab⟩
        cases hi : env[i]? with
        | none => rw [hi] at ha; exact absurd ha (by simp)
        | some a =>
          cases hj : env[j]? with
          | none => rw [hj] at hb; exact absurd hb (by simp)
          | some b =>
            rw [hi] at ha
            rw [hj] at hb
            have ea : e a = a' := Option.some.inj ha
            have eb : e b = b' := Option.some.inj hb
            rw [← ea, ← eb] at hab
            exact ⟨a, b, rfl, rfl, (hmem a b).mpr hab⟩
    | eq i j =>
      intro env
      simp only [Sat, List.getElem?_map]
      constructor
      · rintro ⟨a, b, ha, hb, hab⟩
        exact ⟨e a, e b, by rw [ha]; rfl, by rw [hb]; rfl, by rw [hab]⟩
      · rintro ⟨a', b', ha, hb, hab⟩
        cases hi : env[i]? with
        | none => rw [hi] at ha; exact absurd ha (by simp)
        | some a =>
          cases hj : env[j]? with
          | none => rw [hj] at hb; exact absurd hb (by simp)
          | some b =>
            rw [hi] at ha
            rw [hj] at hb
            have ea : e a = a' := Option.some.inj ha
            have eb : e b = b' := Option.some.inj hb
            rw [← ea, ← eb] at hab
            exact ⟨a, b, rfl, rfl, he.1 hab⟩
    | neg φ ih =>
      intro env
      simp only [Sat]
      rw [ih env]
    | and φ ψ ih1 ih2 =>
      intro env
      simp only [Sat]
      rw [ih1 env, ih2 env]
    | all t φ ih =>
      intro env
      simp only [Sat]
      constructor
      · intro hall w
        obtain ⟨a, rfl⟩ := he.2 w
        have := (ih (a :: env)).mp (hall a)
        simpa using this
      · intro hall a
        exact (ih (a :: env)).mpr (by simpa using hall (e a))
  refine ⟨fun x y hxy => he.1 (h.ext _ _ fun w => ?_), fun t Γ φ hs params hp => ?_⟩
  · obtain ⟨a, rfl⟩ := he.2 w
    rw [← hmem, ← hmem]
    exact hxy a
  · obtain ⟨y, hy⟩ := h.comprehension t Γ φ hs (params.map e) (by simpa using hp)
    obtain ⟨a, rfl⟩ := he.2 y
    refine ⟨a, fun x => ?_⟩
    rw [hmem, hy (e x), hsat φ (x :: params)]
    rfl

end ConNF.NF

namespace NFUCut

/-- "The number `0` is in the cut of the terms and no smaller number is `η`-equal to it", as a
formula of two-sorted arithmetic. -/
def minTm2 : BFml :=
  .and (inIF (.var 0))
    (.all 1 (BFml.imp (.le (.add (.var 1) .one) (.var 0)) (.neg (etaF (.var 1) (.var 0)))))

/-- **The domain of the interpretation with true equality**: a formula in the variable
`100`. -/
def nfDom : Fml := closeP (.and (.mem 100 2) (trB minTm2))

namespace Model

variable {V : Type} [Nonempty V] (M : Model V) [hinf : Fact M.Infinity]

theorem isPred_memFn {F : M.Num → M.Num} (hF : M.NatFn F) (S : V) :
    M.IsPred (fun n => M.mem (F n).1 S) := by
  obtain ⟨f, hf⟩ := hF
  obtain ⟨s, -, hs⟩ := M.comp (σW [(1, 5), (2, 3)])
    (Fml.ex 3 (.and (fApp 1 0 3) (.mem 3 2))) 0 rfl
    (Function.update (Function.update (fun _ => dflt) 1 f) 2 S)
  have hs' : ∀ v, M.mem v s ↔ ∃ u, M.mem (M.op v u) f ∧ M.mem u S := by
    intro v
    rw [hs v]
    simp [M.sat_ex, Sat, M.sat_fApp, Function.update_apply]
  refine ⟨s, fun v => ?_⟩
  rw [hs']
  constructor
  · rintro ⟨u, h1, h2⟩
    obtain ⟨n, hn, hu⟩ := (hf _ _).mp h1
    rw [← hu] at h2
    exact ⟨n, hn, h2⟩
  · rintro ⟨n, hn, h⟩
    rw [← hn]
    exact ⟨(F n).1, M.graph_app hf n, h⟩

/-- The least number principle for conditions given by sets. -/
theorem exists_least {P : M.Num → Prop} (hP : M.IsPred P) {n : M.Num} (hn : P n) :
    ∃ m, P m ∧ ∀ m', P m' → m ≤ m' := by
  obtain ⟨s, hs⟩ := hP
  have hs' : ∀ k : M.Num, M.mem k.1 s ↔ P k := fun k =>
    (hs k.1).trans ⟨fun ⟨k', e, h⟩ => by rwa [← Subtype.ext e], fun h => ⟨k, rfl, h⟩⟩
  obtain ⟨a, ha, hmin⟩ := M.nat_least (X := s) ⟨n, (hs' n).mpr hn⟩
  exact ⟨a, (hs' a).mp ha, fun m' hm' => hmin m' ((hs' m').mpr hm')⟩

theorem aEq_mono_left {s t : M.Num} (h : s ≤ t) : aEq s t ≤ aEq t t := by
  unfold aEq npair
  gcongr

/-- `s` is the least member of its `η`-class, and lies in the cut of the terms. -/
def MinTm (s : M.Num) : Prop := M.InI s ∧ ∀ s' : M.Num, s' + 1 ≤ s → ¬ M.Eta s' s

/-- Every term in the cut is `η`-equal to a least one. -/
theorem exists_minTm {t : M.Num} (ht : M.InI t) : ∃ s, M.MinTm s ∧ M.Eta s t := by
  have hk : M.InI (aEq t t + 1) := M.i_add (M.i_aEq ht ht) M.i_one
  obtain ⟨-, S, hS⟩ := M.i_sub hk
  have key : ∀ s : M.Num, s ≤ t → (M.Eta s t ↔ M.mem (aEq s t).1 S) := fun s hs =>
    M.val_iff hS (add_le_add_left (M.aEq_mono_left hs) 1)
  have hF : M.NatFn (fun s : M.Num => aEq s t) := by
    have h1 : M.NatFn (fun s : M.Num => npair s t) :=
      M.fnAdd (M.fnMul (M.fnAdd M.natFn_id (M.natFn_const t)) (M.fnAdd M.natFn_id (M.natFn_const t)))
        M.natFn_id
    exact M.fnAdd (M.fnAdd h1 h1) (M.natFn_const 1)
  have hP : M.IsPred (fun s : M.Num => s ≤ t ∧ M.mem (aEq s t).1 S) :=
    M.isPred_and (M.isPred_le M.natFn_id (M.natFn_const t)) (M.isPred_memFn hF S)
  obtain ⟨s0, ⟨hs0t, hs0S⟩, hmin⟩ :=
    M.exists_least hP (n := t) ⟨le_refl t, (key t (le_refl t)).mp (M.eta_refl ht)⟩
  have hs0I : M.InI s0 := M.i_down hs0t ht
  have hs0η : M.Eta s0 t := (key s0 hs0t).mpr hs0S
  refine ⟨s0, ⟨hs0I, fun s' hs' hη => ?_⟩, hs0η⟩
  have hs's0 : s' ≤ s0 := le_trans (M.nfacts.le_add s' 1) hs'
  have hs't : s' ≤ t := le_trans hs's0 hs0t
  have hη' : M.Eta s' t := M.eta_trans (M.i_down hs's0 hs0I) hs0I ht hη hs0η
  have := hmin s' ⟨hs't, (key s' hs't).mp hη'⟩
  exact M.not_succ_le s' (le_trans hs' this)

/-- Two least terms that are `η`-equal are equal. -/
theorem minTm_unique {s s' : M.Num} (hs : M.MinTm s) (hs' : M.MinTm s') (h : M.Eta s s') : s = s' := by
  rcases M.le_total' s s' with h1 | h1
  · rcases M.eq_or_succ_le h1 with e | e
    · exact e
    · exact absurd h (hs'.2 s e)
  · rcases M.eq_or_succ_le h1 with e | e
    · exact e.symm
    · exact absurd (M.eta_symm hs.1 hs'.1 h) (hs.2 s' e)

theorem bholds_minTm2 (e : ℕ → M.Num) (s : ℕ → V) : M.bholds minTm2 e s ↔ M.MinTm (e 0) := by
  unfold minTm2 MinTm
  simp only [bholds, M.bholds_imp]
  rw [M.bholds_inIF (.var 0) e s (M.fr_var (by norm_num)) (M.fr_var (by norm_num))
    (M.fr_var (by norm_num))]
  refine and_congr Iff.rfl (forall_congr' fun a => ?_)
  rw [M.bholds_etaF (.var 1) (.var 0) _ s (M.fr_var (by norm_num)) (M.fr_var (by norm_num))]
  simp [evalT, Function.update_apply]

/-- A formula of two-sorted arithmetic in one number variable, translated and with the
parameters quantified away, defines the corresponding set of numbers. -/
theorem sat_one (ψ : BFml) (P : M.Num → Prop)
    (hψ : ∀ (e : ℕ → M.Num) (s : ℕ → V), M.bholds ψ e s ↔ P (e 0)) (x : V) :
    Sat M.mem M.isSet (closeP (.and (.mem 100 2) (trB ψ))) (fun _ => x) ↔
      ∃ hx : M.mem x M.nat, P ⟨x, hx⟩ := by
  rw [M.sat_closeP]
  have hnv : ∀ (z N A Mu o Tw Ex : V) (i : ℕ),
      parEnv (fun _ => x) z N A Mu o Tw Ex (nv i) = x := fun z N A Mu o Tw Ex i =>
    parEnv_ge _ _ _ _ _ _ _ _ (by unfold nv; omega)
  have hsv : ∀ (z N A Mu o Tw Ex : V) (X : ℕ),
      parEnv (fun _ => x) z N A Mu o Tw Ex (sv X) = x := fun z N A Mu o Tw Ex X =>
    parEnv_ge _ _ _ _ _ _ _ _ (by unfold sv; omega)
  constructor
  · rintro ⟨z, N, A, Mu, o, Tw, Ex, hP, hsat⟩
    simp only [Sat] at hsat
    obtain ⟨hmem, htr⟩ := hsat
    rw [show (100 : ℕ) = nv 0 from rfl, hnv, hP.2.1] at hmem
    refine ⟨hmem, ?_⟩
    rw [M.sat_trB_par ψ _ hP (fun _ => ⟨x, hmem⟩) (fun _ => x)
      (fun i => hnv _ _ _ _ _ _ _ i) (fun X => hsv _ _ _ _ _ _ _ X)] at htr
    exact (hψ _ _).mp htr
  · rintro ⟨hx, hI⟩
    obtain ⟨z, N, A, Mu, o, Tw, Ex, hP⟩ := M.exists_par (fun _ => x)
    refine ⟨z, N, A, Mu, o, Tw, Ex, hP, ?_⟩
    simp only [Sat]
    refine ⟨?_, ?_⟩
    · rw [show (100 : ℕ) = nv 0 from rfl, hnv, hP.2.1]
      exact hx
    · rw [M.sat_trB_par ψ _ hP (fun _ => ⟨x, hx⟩) (fun _ => x)
        (fun i => hnv _ _ _ _ _ _ _ i) (fun X => hsv _ _ _ _ _ _ _ X)]
      exact (hψ _ _).mpr hI

/-- **The formula `nfDom` defines the least terms.** -/
theorem sat_nfDom (x : V) :
    Sat M.mem M.isSet nfDom (fun _ => x) ↔ ∃ hx : M.mem x M.nat, M.MinTm ⟨x, hx⟩ :=
  M.sat_one minTm2 M.MinTm (fun e s => M.bholds_minTm2 e s) x

/-- The objects that satisfy `nfDom`. -/
def Dom : Type := {x : V // Sat M.mem M.isSet nfDom (fun _ => x)}

/-- The interpreted membership on the objects that satisfy `nfDom`. -/
def dmem (x y : M.Dom) : Prop := Sat M.mem M.isSet nfEps (Function.update (fun _ => x.1) 103 y.1)

/-- **NFU + Infinity interprets NF with equality interpreted by equality.** In every model of
NFU + Infinity, the objects that satisfy `nfDom`, with the relation defined by `nfEps` and true
equality, form a model of NF. -/
theorem dom_isNF : ConNF.NF.IsNF M.Dom M.dmem := by
  have hd : ∀ x : M.Dom, ∃ hx : M.mem x.1 M.nat, M.MinTm ⟨x.1, hx⟩ :=
    fun x => (M.sat_nfDom x.1).mp x.2
  let tm : M.Dom → M.Tm := fun x => ⟨⟨x.1, (hd x).fst⟩, (hd x).snd.1⟩
  have htm : ∀ x : M.Dom, M.MinTm (tm x).1 := fun x => (hd x).snd
  have hval : ∀ x : M.Dom, (tm x).1.1 = x.1 := fun x => rfl
  refine ConNF.NF.IsNF.of_bijective (fun x => M.nmk (tm x)) ⟨fun x y hxy => ?_, fun w => ?_⟩
    (fun x y => ?_) M.termModel_isNF
  · have h1 : M.Eta (tm x).1 (tm y).1 := (M.nmk_eq (a := tm x) (b := tm y)).mp hxy
    have h2 : (tm x).1 = (tm y).1 := M.minTm_unique (htm x) (htm y) h1
    have h3 : (tm x).1.1 = (tm y).1.1 := congrArg Subtype.val h2
    rw [hval x, hval y] at h3
    exact Subtype.ext h3
  · obtain ⟨a, rfl⟩ := M.nmk_surj w
    obtain ⟨s, hs, hsa⟩ := M.exists_minTm a.2
    let x : M.Dom := ⟨s.1, (M.sat_nfDom s.1).mpr ⟨s.2, hs⟩⟩
    refine ⟨x, ?_⟩
    have e1 : (tm x).1 = s := Subtype.ext rfl
    exact (M.nmk_eq (a := tm x) (b := a)).mpr (by rw [e1]; exact hsa)
  · have h1 : M.dmem x y ↔ ∃ (hx : M.mem x.1 M.nat) (hy : M.mem y.1 M.nat),
        M.Eps ⟨x.1, hx⟩ ⟨y.1, hy⟩ := M.sat_nfEps x.1 y.1
    rw [h1]
    exact ⟨fun ⟨_, _, h⟩ => h, fun h => ⟨(hd x).fst, (hd y).fst, h⟩⟩

end Model

end NFUCut
