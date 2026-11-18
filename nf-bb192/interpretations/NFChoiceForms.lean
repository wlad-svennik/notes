import NFSpecker

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

/-!
# Other forms of the axiom of choice

`NFSpecker.lean` refutes, in NF, the axiom of choice in the form "every set of pairwise disjoint
sets with members has a set that meets each of them in exactly one element" (`Model.AC`), and
proves directly that the universe has no well-ordering. Here two more forms are shown to imply
`Model.AC` in every model of NFU, so NF refutes them too:

* `Model.ZornLemma`: a family in which every chain has an upper bound has a maximal element;
* `Model.ChoiceFunctions`: every set of sets with members has a choice function. The function
  sends a set to the singleton of the chosen member, so that the statement is stratified.
-/

namespace NFUCut

namespace Model

variable {V : Type} [Nonempty V] (M : Model V)

/-- **Zorn's lemma** for inclusion: if every chain in the family `P` has an upper bound in `P`,
then `P` has a maximal member. -/
def ZornLemma : Prop :=
  ∀ P : V,
    (∀ C : V, (∀ c, M.mem c C → M.mem c P) →
      (∀ c c', M.mem c C → M.mem c' C →
        (∀ z, M.mem z c → M.mem z c') ∨ (∀ z, M.mem z c' → M.mem z c)) →
      ∃ b, M.mem b P ∧ ∀ c, M.mem c C → ∀ z, M.mem z c → M.mem z b) →
    ∃ m, M.mem m P ∧ ∀ c, M.mem c P → (∀ z, M.mem z m → M.mem z c) → c = m

/-- **Choice functions**: for every set `X` of sets with members there is a set `f` of ordered
pairs that pairs each `a` in `X` with the singleton of exactly one object, a member of `a`. -/
def ChoiceFunctions : Prop :=
  ∀ X : V, (∀ a, M.mem a X → ∃ u, M.mem u a) →
    ∃ f, ∀ a, M.mem a X →
      ∃ u, M.mem u a ∧ M.mem (M.op a (M.sing u)) f ∧ ∀ w, M.mem (M.op a w) f → w = M.sing u

/-- Zorn's lemma implies the axiom of choice for disjoint families. -/
theorem zorn_ac (hz : M.ZornLemma) : M.AC := by
  intro X hne hdis
  -- the family of partial selectors
  obtain ⟨P, -, hP⟩ := M.comp (fun i => if i = 0 then 1 else if i = 1 then 1 else if i = 4 then 2 else 0)
    (.and (.set 0) (.all 1 (Fml.imp (.mem 1 4) (.all 2 (.all 3 (Fml.imp
      (.and (.mem 2 1) (.and (.mem 2 0) (.and (.mem 3 1) (.mem 3 0)))) (.eq 2 3)))))))
    0 (by decide) (Function.update (fun _ => dflt) 4 X)
  have hP' : ∀ c, M.mem c P ↔ M.isSet c ∧ ∀ a, M.mem a X → ∀ u u',
      (M.mem u a ∧ M.mem u c ∧ M.mem u' a ∧ M.mem u' c) → u = u' := by
    intro c
    rw [hP c]
    simp only [Sat, M.sat_imp]
    simp only [Function.update_apply]
    simp only [reduceIte, Nat.reduceEqDiff]
  have hub : ∀ C : V, (∀ c, M.mem c C → M.mem c P) →
      (∀ c c', M.mem c C → M.mem c' C →
        (∀ z, M.mem z c → M.mem z c') ∨ (∀ z, M.mem z c' → M.mem z c)) →
      ∃ b, M.mem b P ∧ ∀ c, M.mem c C → ∀ z, M.mem z c → M.mem z b := by
    intro C hCP hch
    refine ⟨M.sUnion C, (hP' _).mpr ⟨M.sUnion_isSet C, fun a ha u u' ⟨hua, huC, hu'a, hu'C⟩ => ?_⟩,
      fun c hc z hz => M.mem_sUnion.mpr ⟨c, hc, hz⟩⟩
    obtain ⟨c1, hc1, hu1⟩ := M.mem_sUnion.mp huC
    obtain ⟨c2, hc2, hu2⟩ := M.mem_sUnion.mp hu'C
    rcases hch c1 c2 hc1 hc2 with h | h
    · exact ((hP' c2).mp (hCP c2 hc2)).2 a ha u u' ⟨hua, h u hu1, hu'a, hu2⟩
    · exact ((hP' c1).mp (hCP c1 hc1)).2 a ha u u' ⟨hua, hu1, hu'a, h u' hu2⟩
  obtain ⟨m, hmP, hmax⟩ := hz P hub
  obtain ⟨hmset, hmsel⟩ := (hP' m).mp hmP
  refine ⟨m, fun a ha => ?_⟩
  by_cases hmeet : ∃ u, M.mem u a ∧ M.mem u m
  · obtain ⟨u, hua, hum⟩ := hmeet
    exact ⟨u, hua, hum, fun u' hu'a hu'm => hmsel a ha u' u ⟨hu'a, hu'm, hua, hum⟩⟩
  · exfalso
    obtain ⟨u, hua⟩ := hne a ha
    have hum : ¬ M.mem u m := fun h => hmeet ⟨u, hua, h⟩
    have hadj : M.mem (M.adj m u) P := by
      refine (hP' _).mpr ⟨M.adj_isSet m u, fun a' ha' v v' ⟨hva', hv, hv'a', hv'⟩ => ?_⟩
      rcases M.mem_adj.mp hv with hv | hv
      · rcases M.mem_adj.mp hv' with hv' | hv'
        · exact hmsel a' ha' v v' ⟨hva', hv, hv'a', hv'⟩
        · have e : a' = a := hdis a' a u ha' ha (hv' ▸ hv'a') hua
          exact absurd ⟨v, e ▸ hva', hv⟩ hmeet
      · rcases M.mem_adj.mp hv' with hv' | hv'
        · have e : a' = a := hdis a' a u ha' ha (hv ▸ hva') hua
          exact absurd ⟨v', e ▸ hv'a', hv'⟩ hmeet
        · rw [hv, hv']
    have e : M.adj m u = m := hmax _ hadj (fun z hz => M.mem_adj.mpr (Or.inl hz))
    have h1 : M.mem u (M.adj m u) := M.mem_adj.mpr (Or.inr rfl)
    rw [e] at h1
    exact hum h1

/-- Choice functions give the axiom of choice for disjoint families. -/
theorem choiceFunctions_ac (hcf : M.ChoiceFunctions) : M.AC := by
  intro X hne hdis
  obtain ⟨f, hf⟩ := hcf X hne
  -- the set of the chosen members
  obtain ⟨c, -, hc⟩ := M.comp
    (fun i => if i = 1 then 1 else if i = 2 then 1 else if i = 3 then 3 else if i = 4 then 2
      else if i = 5 then 4 else if i = 7 then 2 else if i = 8 then 1 else 0)
    (Fml.ex 1 (.and (.mem 1 4) (Fml.ex 2 (.and (fSing 2 0 6)
      (Fml.ex 3 (.and (.mem 3 5) (fOp 3 1 2 7 8)))))))
    0 (by decide) (Function.update (Function.update (fun _ => dflt) 4 X) 5 f)
  have hc' : ∀ u, M.mem u c ↔ ∃ a, M.mem a X ∧ M.mem (M.op a (M.sing u)) f := by
    intro u
    rw [hc u]
    simp only [M.sat_ex, Sat, M.sat_fSing (u := 2) (a := 0) (c := 6) (by decide) (by decide),
      M.sat_fOp (p := 3) (a := 1) (b := 2) (u := 7) (c := 8) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)]
    simp only [Function.update_apply]
    simp only [reduceIte, Nat.reduceEqDiff]
    constructor
    · rintro ⟨a, ha, w, rfl, p, hp, rfl⟩
      exact ⟨a, ha, hp⟩
    · rintro ⟨a, ha, hp⟩
      exact ⟨a, ha, _, rfl, _, hp, rfl⟩
  refine ⟨c, fun a ha => ?_⟩
  obtain ⟨u, hua, huf, huniq⟩ := hf a ha
  refine ⟨u, hua, (hc' u).mpr ⟨a, ha, huf⟩, fun u' hu'a hu'c => ?_⟩
  obtain ⟨a', ha', hf'⟩ := (hc' u').mp hu'c
  obtain ⟨v, hva', hvf, hvuniq⟩ := hf a' ha'
  have e2 : u' = v := M.sing_inj (hvuniq _ hf')
  have e3 : a = a' := hdis a a' u' ha ha' hu'a (e2 ▸ hva')
  rw [← e3] at hf'
  exact M.sing_inj (huniq _ hf')

variable [hNF : Fact (∀ x : V, M.isSet x)]

/-- **NF refutes Zorn's lemma.** -/
theorem nf_not_zorn : ¬ M.ZornLemma := fun h => M.nf_not_choice (M.zorn_ac h)

/-- **NF refutes the existence of choice functions.** -/
theorem nf_not_choiceFunctions : ¬ M.ChoiceFunctions := fun h =>
  M.nf_not_choice (M.choiceFunctions_ac h)

end Model

/-- **NF refutes Zorn's lemma**, stated with membership only. -/
theorem _root_.ConNF.NF.IsNF.not_zorn {V : Type} {mem : V → V → Prop} (h : ConNF.NF.IsNF V mem) :
    ¬ ∀ P : V,
      (∀ C : V, (∀ c, mem c C → mem c P) →
        (∀ c c', mem c C → mem c' C → (∀ z, mem z c → mem z c') ∨ (∀ z, mem z c' → mem z c)) →
        ∃ b, mem b P ∧ ∀ c, mem c C → ∀ z, mem z c → mem z b) →
      ∃ m, mem m P ∧ ∀ c, mem c P → (∀ z, mem z m → mem z c) → c = m := by
  have := h.nonempty
  have : Fact (∀ x : V, (modelOfNF h).isSet x) := ⟨fun _ => trivial⟩
  exact (modelOfNF h).nf_not_zorn

end NFUCut
