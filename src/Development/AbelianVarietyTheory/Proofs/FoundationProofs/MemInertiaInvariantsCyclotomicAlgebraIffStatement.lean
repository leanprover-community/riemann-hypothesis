import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemCycAlgOfPow
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPolynomialInPrimitiveRootOfInertiaFixedStatement
import Development.AbelianVarietyTheory.Definitions.Foundations.EeProd
import ReciprocityTheory.GaloisValuations.Global
import GroundTheory.GlobalFields.CyclotomicCharacters.ProfinitePadic

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.KZ GlobalTheory.Glue

namespace GlobalTheory

theorem fixed_cycMod_of_fixed_cycZ : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω), A.valuation (l : Ω) < 1 → ∀ (F : Finset Ω) (y : Ω), (∀ s ∈ Ine (F := ℚ) A, (∀ z ∈ F, s z = z) → cycZ ℚ Ω l s = 1 → s y = y) →
  ∃ m : ℕ, ∀ s : G ℚ Ω, s ∈ Ine (F := ℚ) A ∧ (∀ z ∈ F, s z = z) ∧ cycMod ℚ Ω l m s = 1 → s y = y := by
  intro l _ Ω _ _ _ A _ F y hy
  haveI : CompactSpace (G ℚ Ω) := inferInstanceAs (CompactSpace (Ω ≃ₐ[ℚ] Ω))
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic

  set K : IntermediateField ℚ Ω := IntermediateField.adjoin ℚ ({y} : Set Ω) with hK
  have : FiniteDimensional ℚ K :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsAlgebraic.isAlgebraic y).isIntegral
  have hSo : IsOpen (MulAction.stabilizer (G ℚ Ω) y : Set (G ℚ Ω)) := by
    refine Subgroup.isOpen_mono (H₁ := K.fixingSubgroup) ?_ (IntermediateField.fixingSubgroup_isOpen K)
    intro g hg
    exact (IntermediateField.mem_fixingSubgroup_iff K g).mp hg y
      (IntermediateField.subset_adjoin ℚ _ (Set.mem_singleton y))
  set S : Set (G ℚ Ω) := (MulAction.stabilizer (G ℚ Ω) y : Set (G ℚ Ω)) with hS
  have memS : ∀ s : G ℚ Ω, s ∈ S ↔ s y = y := fun s => Iff.rfl
  set H0 : Set (G ℚ Ω) := (Ine (F := ℚ) A : Set (G ℚ Ω)) ∩ ⋂ z ∈ F, {s : G ℚ Ω | s z = z} with hH0
  have hH0c : IsClosed H0 :=
    (isClosed_Ine A).inter (isClosed_biInter fun z _ => isClosed_setOf_apply z (fun t => t = z))

  have hcm : ∀ (m : ℕ) (s : G ℚ Ω), cycMod ℚ Ω l m s = 1 ↔
      PadicInt.toZModPow m ((cycZ ℚ Ω l s : ℤ_[l]ˣ) : ℤ_[l]) = 1 := by
    intro m s; rw [Units.ext_iff]; rfl
  set C : ℕ → Set (G ℚ Ω) := fun m =>
    (H0 ∩ {s | PadicInt.toZModPow m ((cycZ ℚ Ω l s : ℤ_[l]ˣ) : ℤ_[l]) = 1}) ∩ Sᶜ with hC
  have hCc : ∀ m, IsClosed (C m) := by
    intro m
    have hc : Continuous fun s : G ℚ Ω => PadicInt.toZModPow m ((cycZ ℚ Ω l s : ℤ_[l]ˣ) : ℤ_[l]) :=
      (GroundTheory.Global.Cyclotomic.continuous_toZModPow m).comp
        (Units.continuous_val.comp (continuous_cycZ ℚ Ω l))
    exact (hH0c.inter ((isClosed_discrete ({1} : Set (ZMod (l ^ m)))).preimage hc)).inter
      hSo.isClosed_compl
  have hmono : ∀ m k, m ≤ k → C k ⊆ C m := by
    intro m k hmk s ⟨⟨h0, h1⟩, h2⟩
    refine ⟨⟨h0, ?_⟩, h2⟩
    simp only [Set.mem_setOf_eq] at h1 ⊢
    rw [← PadicInt.zmod_cast_comp_toZModPow m k hmk, RingHom.comp_apply, h1, map_one]
  by_contra hne
  push_neg at hne
  have hCn : ∀ m, (C m).Nonempty := by
    intro m
    obtain ⟨s, ⟨hs1, hs2, hs3⟩, hs4⟩ := hne m
    refine ⟨s, ⟨⟨hs1, ?_⟩, (hcm m s).mp hs3⟩, hs4⟩
    simp only [Set.mem_iInter, Set.mem_setOf_eq]
    exact hs2
  have hdir : Directed (· ⊇ ·) C := fun m k =>
    ⟨max m k, hmono m _ (le_max_left m k), hmono k _ (le_max_right m k)⟩
  obtain ⟨s, hs⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed C hdir hCn
    (fun m => (hCc m).isCompact) hCc
  simp only [Set.mem_iInter] at hs
  obtain ⟨⟨h0i, h0f⟩, -⟩ := (hs 0).1
  have hz : cycZ ℚ Ω l s = 1 := by
    refine Units.ext (PadicInt.ext_of_toZModPow.mp fun n => ?_)
    rw [(hs n).1.2, Units.val_one, map_one]
  simp only [Set.mem_iInter, Set.mem_setOf_eq] at h0f
  exact (hs 0).2 ((memS s).mpr (hy s h0i h0f hz))

end GlobalTheory
end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.RecOne GlobalTheory.AlmostEt
open scoped Matrix NNReal

namespace GlobalTheory.RecOne

theorem mem_cycAlg_iff : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω), OverL l A → ∀ x : A, x ∈ cycAlg l A ↔ ∀ s ∈ ineCyc l A, s (x : Ω) = x := by
  intro l _ Ω _ _ _ A hA x
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := algebraRat.charZero Ω
  have hl : l.Prime := Fact.out
  haveI : NeZero l := ⟨hl.ne_zero⟩
  haveI hE : ∀ i, HasEnoughRootsOfUnity Ω (l ^ i) := fun i => inferInstance
  constructor
  · intro hx s hs
    obtain ⟨hsI, hsZ⟩ := mem_ineCyc.1 hs
    induction hx using Algebra.adjoin_induction with
    | mem z hz =>
      obtain ⟨n, hn⟩ := hz
      refine GlobalTheory.Col.fix_of_cycMod (l := l) (le_refl n) ?_ ?_
      · simp [cycMod, hsZ]
      · exact_mod_cast congrArg (fun a : A => (a : Ω)) hn
    | algebraMap r => exact r.2 s hsI
    | add a b _ _ ha hb =>
      show s ((a : Ω) + (b : Ω)) = (a : Ω) + (b : Ω)
      rw [map_add, ha, hb]
    | mul a b _ _ ha hb =>
      show s ((a : Ω) * (b : Ω)) = (a : Ω) * (b : Ω)
      rw [map_mul, ha, hb]
  · intro hx
    have hv : A.valuation (l : Ω) < 1 := by
      obtain ⟨v, hv, hl⟩ := hA
      have h1 := (hv ((l : ℕ) : 𝓞 ℚ)).2 hl
      simpa using h1
    obtain ⟨m, hm⟩ := GlobalTheory.fixed_cycMod_of_fixed_cycZ l Ω A hv ∅ (x : Ω)
      (fun s hs _ hz => hx s (mem_ineCyc.2 ⟨hs, hz⟩))
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ m)
    have hpos : 0 < l ^ m := pow_pos hl.pos m
    haveI : NeZero (l ^ m) := ⟨hpos.ne'⟩
    have hfix : ∀ s ∈ Ine (F := ℚ) A, s ζ = ζ → s (x : Ω) = x := by
      intro s hs hsζ
      refine hm s ⟨hs, by simp, ?_⟩
      have h1 := cyclotomicCharacter.spec (L := Ω) l (MulSemiringAction.toRingAut (G ℚ Ω) Ω s) ζ hζ.pow_eq_one
      have h2 : ζ ^ (PadicInt.toZModPow m ((cycZ ℚ Ω l s : ℤ_[l]ˣ) : ℤ_[l])).val = ζ ^ 1 := by
        rw [pow_one]
        exact h1.symm.trans hsζ
      have h3 := (pow_eq_pow_iff_modEq (G := Ωˣ) (x := (hζ.isUnit hpos.ne').unit)
        (n := (PadicInt.toZModPow m ((cycZ ℚ Ω l s : ℤ_[l]ˣ) : ℤ_[l])).val) (m := 1)).1 (by
          apply Units.ext
          simpa using h2)
      have h4 : orderOf (hζ.isUnit hpos.ne').unit = l ^ m := by
        rw [← orderOf_units, IsUnit.unit_spec]
        exact hζ.eq_orderOf.symm
      rw [h4, ← ZMod.natCast_eq_natCast_iff, ZMod.natCast_zmod_val, Nat.cast_one] at h3
      exact Units.ext h3
    obtain ⟨Q, hQ, hQe⟩ := GlobalTheory.T.exists_polynomial_in_primitiveRoot_of_inertia_fixed l Ω A hA m ζ hζ (x : Ω) x.2 hfix
    have hζA : ζ ∈ A := mem_of_pow_mem A hpos.ne' (by rw [hζ.pow_eq_one]; exact A.one_mem)
    have hζc : (⟨ζ, hζA⟩ : A) ∈ cycAlg l A :=
      mem_cycAlg_of_pow (n := m) (Subtype.ext (by simpa using hζ.pow_eq_one))
    have e : x = ∑ d ∈ Finset.range (Q.natDegree + 1), (⟨Q.coeff d, (hQ d).1⟩ : A) * (⟨ζ, hζA⟩ : A) ^ d := by
      apply Subtype.ext
      rw [← hQe, Polynomial.eval_eq_sum_range]
      refine Eq.trans ?_ (map_sum A.subtype _ _).symm
      refine Finset.sum_congr rfl fun d _ => ?_
      simp
    rw [e]
    refine Subalgebra.sum_mem _ fun d _ => Subalgebra.mul_mem _ ?_ (Subalgebra.pow_mem _ hζc d)
    exact (cycAlg l A).algebraMap_mem (⟨⟨Q.coeff d, (hQ d).1⟩, (hQ d).2⟩ : fixA A)

end GlobalTheory.RecOne
end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.RecOne GlobalTheory.AlmostEt
open scoped Matrix NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_inertiaInvariantsCyclotomicAlgebra_iff : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω), OverL l A → ∀ x : A, x ∈ cycAlg l A ↔ ∀ s ∈ ineCyc l A, s (x : Ω) = x := by
  first | (exact @GlobalTheory.RecOne.mem_cycAlg_iff) | (exact GlobalTheory.RecOne.mem_cycAlg_iff) | (intros; apply GlobalTheory.RecOne.mem_cycAlg_iff  <;> assumption)
end
