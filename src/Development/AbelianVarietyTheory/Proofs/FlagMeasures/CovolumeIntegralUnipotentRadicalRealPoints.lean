import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsVolData
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitQuotientTopology.IsClosedRStab
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HasFlagDepthAtLeastOfFreeEntriesVanish
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarLieNilpotentCoordinates
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StabilizerMeasureNormalisationSymm
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasureUnipotentTuplesFreeEntryBlocks
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralUnipotentRadicalFormsUnitSubgroup
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralUnipotentMemModelUnipotentAtPlace
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameDualTupleIdealsCastAdd
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralUnipotentCornerEntryMemIdealLattice
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralUnipotentMiddleRowMemHomLattice
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralUnipotentAntidiagonalMemSkewLattice
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowEmbeddingMemIntegralOrthogonalGroup
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowIsometryEntriesInModelCoordinatesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIntegralUnipotentLiftEntry
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LiftRowMiddleSpaceIntegralPointStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurePreservingOfBall
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CovolumeInverseDifferentPowMulLattice
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SkewLatticeInverseDifferentPowCovolume
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CovolumeMiddleLatticeHomLatticeIdeal
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnipotentRadicalBlockCovolumesProd

section
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors

namespace GlobalTheory.SnMass.VolN

theorem existsUnique_layered_fundamentalDomain :
    ∀ {G X B : Type} [Group G] [Finite B] {V : B → Type} [∀ β, AddCommGroup (V β)] (ρ : G → X → X) (NN : Set X) (o : X) (deg : B → ℕ) (c : ∀ β, X → V β) (L D : ∀ β, Set (V β)), o ∈ NN → (∀ x, ρ 1 x = x) → (∀ g h x, ρ (g * h) x = ρ g (ρ h x)) → (∀ g, ∀ x ∈ NN, ρ g x ∈ NN) → (∀ β, (0 : V β) ∈ L β) → (∀ β v, ∃! l, l ∈ L β ∧ v + l ∈ D β) → (∀ β, c β o = 0) → (∀ (d : ℕ) (g : G), (∀ β, deg β < d → c β (ρ g o) = 0) → ∀ x ∈ NN, ∀ β, deg β ≤ d → c β (ρ g x) = c β x + c β (ρ g o)) → (∀ (g : G) (β : B), (∀ β', deg β' < deg β → c β' (ρ g o) = 0) → c β (ρ g o) ∈ L β) → (∀ β, ∀ l ∈ L β, ∃ g : G, c β (ρ g o) = l ∧ ∀ β', β' ≠ β → deg β' ≤ deg β → c β' (ρ g o) = 0) → (∀ g : G, (∀ β, c β (ρ g o) = 0) → g = 1) → ∀ x ∈ NN, ∃! g : G, ∀ β, c β (ρ g x) ∈ D β := by
  intro G X B _ _ V _ ρ NN o deg c L D ho h1 hmul hst hL0 hD hco htr hL hon hinj x hx
  classical
  haveI := Fintype.ofFinite B
  have hgx : ∀ (g : G) (y : X), y ∈ NN → ρ g y ∈ NN := fun g y hy => hst g y hy

  have step : ∀ (d : ℕ) (T : Finset B), (∀ β ∈ T, deg β = d) →
      (∃ g : G, ∀ β, deg β < d → c β (ρ g x) ∈ D β) →
      ∃ g : G, ∀ β, (deg β < d ∨ β ∈ T) → c β (ρ g x) ∈ D β := by
    intro d T
    induction T using Finset.induction_on with
    | empty =>
      intro _ ⟨g, hg⟩
      refine ⟨g, fun β hβ => ?_⟩
      rcases hβ with hβ | hβ
      · exact hg β hβ
      · simp at hβ
    | insert b T hb ih =>
      intro hT h0
      obtain ⟨g, hg⟩ := ih (fun β hβ => hT β (Finset.mem_insert_of_mem hβ)) h0
      have hbd : deg b = d := hT b (Finset.mem_insert_self b T)
      obtain ⟨l, ⟨hlL, hlD⟩, -⟩ := hD b (c b (ρ g x))
      obtain ⟨h, hhl, hh0⟩ := hon b l hlL
      have hlow : ∀ β, deg β < d → c β (ρ h o) = 0 := fun β hβ =>
        hh0 β (fun e => by subst e; omega) (by omega)
      have htrans := htr d h hlow (ρ g x) (hgx g x hx)
      refine ⟨h * g, fun β hβ => ?_⟩
      rw [hmul]
      by_cases hβb : β = b
      · subst hβb
        rw [htrans β (by omega), hhl]
        exact hlD
      · have hle : deg β ≤ d := by
          rcases hβ with hβ | hβ
          · omega
          · exact (hT β hβ).le
        have hold : deg β < d ∨ β ∈ T := by
          rcases hβ with hβ | hβ
          · exact Or.inl hβ
          · exact Or.inr ((Finset.mem_insert.mp hβ).resolve_left hβb)
        rw [htrans β hle, hh0 β hβb (by omega), add_zero]
        exact hg β hold
  have exD : ∀ d : ℕ, ∃ g : G, ∀ β, deg β < d → c β (ρ g x) ∈ D β := by
    intro d
    induction d with
    | zero => exact ⟨1, fun β hβ => absurd hβ (Nat.not_lt_zero _)⟩
    | succ d ih =>
      obtain ⟨g, hg⟩ := step d (Finset.univ.filter (fun β => deg β = d))
        (fun β hβ => (Finset.mem_filter.mp hβ).2) ih
      refine ⟨g, fun β hβ => hg β ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hβ with h | h
      · exact Or.inl h
      · exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
  obtain ⟨M, hM⟩ := (Set.finite_range deg).bddAbove
  obtain ⟨g₀, hg₀⟩ := exD (M + 1)
  refine ⟨g₀, fun β => hg₀ β (Nat.lt_succ_of_le (hM ⟨β, rfl⟩)), ?_⟩

  intro g₂ hg₂
  have hg₁ : ∀ β, c β (ρ g₀ x) ∈ D β := fun β => hg₀ β (Nat.lt_succ_of_le (hM ⟨β, rfl⟩))
  have hy : ρ g₀ x ∈ NN := hgx g₀ x hx
  have hδy : ρ (g₂ * g₀⁻¹) (ρ g₀ x) = ρ g₂ x := by
    rw [← hmul, inv_mul_cancel_right]
  have vanish : ∀ d : ℕ, ∀ β, deg β < d → c β (ρ (g₂ * g₀⁻¹) o) = 0 := by
    intro d
    induction d with
    | zero => exact fun β hβ => absurd hβ (Nat.not_lt_zero _)
    | succ d ih =>
      intro β hβ
      rcases Nat.lt_succ_iff_lt_or_eq.mp hβ with h | h
      · exact ih β h
      · have hin : c β (ρ (g₂ * g₀⁻¹) o) ∈ L β := hL _ β (fun β' hβ' => ih β' (by omega))
        have hadd := htr d (g₂ * g₀⁻¹) ih (ρ g₀ x) hy β h.le
        rw [hδy] at hadd
        have hmem : c β (ρ g₀ x) + c β (ρ (g₂ * g₀⁻¹) o) ∈ D β := hadd ▸ hg₂ β
        have hzero : c β (ρ g₀ x) + 0 ∈ D β := by simpa using hg₁ β
        exact (hD β (c β (ρ g₀ x))).unique ⟨hin, hmem⟩ ⟨hL0 β, hzero⟩
  have hone : g₂ * g₀⁻¹ = 1 :=
    hinj _ (fun β => vanish (M + 1) β (Nat.lt_succ_of_le (hM ⟨β, rfl⟩)))
  exact mul_inv_eq_one.mp hone

end GlobalTheory.SnMass.VolN
end

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_layered_strictFundamentalDomain : ∀ {G X B : Type} [Group G] [Finite B] {V : B → Type} [∀ β, AddCommGroup (V β)] (ρ : G → X → X) (NN : Set X) (o : X) (deg : B → ℕ) (c : ∀ β, X → V β) (L D : ∀ β, Set (V β)), o ∈ NN → (∀ x, ρ 1 x = x) → (∀ g h x, ρ (g * h) x = ρ g (ρ h x)) → (∀ g, ∀ x ∈ NN, ρ g x ∈ NN) → (∀ β, (0 : V β) ∈ L β) → (∀ β v, ∃! l, l ∈ L β ∧ v + l ∈ D β) → (∀ β, c β o = 0) → (∀ (d : ℕ) (g : G), (∀ β, deg β < d → c β (ρ g o) = 0) → ∀ x ∈ NN, ∀ β, deg β ≤ d → c β (ρ g x) = c β x + c β (ρ g o)) → (∀ (g : G) (β : B), (∀ β', deg β' < deg β → c β' (ρ g o) = 0) → c β (ρ g o) ∈ L β) → (∀ β, ∀ l ∈ L β, ∃ g : G, c β (ρ g o) = l ∧ ∀ β', β' ≠ β → deg β' ≤ deg β → c β' (ρ g o) = 0) → (∀ g : G, (∀ β, c β (ρ g o) = 0) → g = 1) → ∀ x ∈ NN, ∃! g : G, ∀ β, c β (ρ g x) ∈ D β := by
  atlas_forward_decl GlobalTheory.SnMass.VolN.existsUnique_layered_fundamentalDomain
end

section
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors

namespace GlobalTheory.SnMass.VolN

theorem strictFD_measure_eq_tsum {G X : Type} [Countable G] [MeasurableSpace X]
    (μ : Measure X) (ρ : G → X → X) (NN D D' : Set X) (hNN : MeasurableSet NN)
    (hnull : μ NNᶜ = 0) (hD : MeasurableSet D) (hD' : MeasurableSet D')
    (hmeas : ∀ g, Measurable (ρ g)) (hu' : ∀ x ∈ NN, ∃! g : G, ρ g x ∈ D') :
    μ D = ∑' g, μ (D ∩ NN ∩ (ρ g)⁻¹' D') := by
  have h1 : μ D = μ (D ∩ NN) := by
    rw [← measure_inter_add_diff D hNN]
    have : μ (D \ NN) = 0 := measure_mono_null (fun x hx => hx.2) hnull
    rw [this, add_zero]
  rw [h1]
  have hU : D ∩ NN = ⋃ g, D ∩ NN ∩ (ρ g)⁻¹' D' := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage]
    constructor
    · rintro ⟨hxD, hxN⟩
      obtain ⟨g, hg, -⟩ := hu' x hxN
      exact ⟨g, ⟨hxD, hxN⟩, hg⟩
    · rintro ⟨g, ⟨hxD, hxN⟩, -⟩
      exact ⟨hxD, hxN⟩
  conv_lhs => rw [hU]
  apply measure_iUnion
  · intro g h hgh
    rw [Function.onFun, Set.disjoint_left]
    rintro x ⟨⟨-, hxN⟩, hg⟩ ⟨⟨-, -⟩, hh⟩
    exact hgh ((hu' x hxN).unique hg hh)
  · intro g
    exact (hD.inter hNN).inter (hmeas g hD')

theorem strictFD_measure_eq {G X : Type} [Group G] [Countable G] [MeasurableSpace X]
    (μ : Measure X) (ρ : G → X → X) (NN D D' : Set X) (hNN : MeasurableSet NN)
    (hnull : μ NNᶜ = 0) (hD : MeasurableSet D) (hD' : MeasurableSet D')
    (hone : ∀ x, ρ 1 x = x) (hmul : ∀ g h x, ρ (g * h) x = ρ g (ρ h x))
    (hinv : ∀ g, ∀ x ∈ NN, ρ g x ∈ NN) (hmp : ∀ g, MeasurePreserving (ρ g) μ μ)
    (hu : ∀ x ∈ NN, ∃! g : G, ρ g x ∈ D) (hu' : ∀ x ∈ NN, ∃! g : G, ρ g x ∈ D') :
    μ D = μ D' := by
  have hmeas : ∀ g, Measurable (ρ g) := fun g => (hmp g).measurable
  rw [strictFD_measure_eq_tsum μ ρ NN D D' hNN hnull hD hD' hmeas hu',
    strictFD_measure_eq_tsum μ ρ NN D' D hNN hnull hD' hD hmeas hu]
  conv_rhs => rw [← (Equiv.inv G).tsum_eq]
  refine tsum_congr fun g => ?_
  simp only [Equiv.inv_apply]
  have hS : MeasurableSet (D' ∩ NN ∩ (ρ g⁻¹)⁻¹' D) :=
    (hD'.inter hNN).inter (hmeas g⁻¹ hD)
  rw [← (hmp g).measure_preimage hS.nullMeasurableSet]
  congr 1
  ext x
  simp only [Set.mem_inter_iff, Set.mem_preimage]
  have hx : ρ g⁻¹ (ρ g x) = x := by rw [← hmul, inv_mul_cancel, hone]
  rw [hx]
  constructor
  · rintro ⟨⟨hxD, hxN⟩, hgx⟩
    exact ⟨⟨hgx, hinv g x hxN⟩, hxD⟩
  · rintro ⟨⟨hgx, hgxN⟩, hxD⟩
    refine ⟨⟨hxD, ?_⟩, hgx⟩
    have := hinv g⁻¹ _ hgxN
    rwa [hx] at this

example : ∀ {G X : Type} [Group G] [Countable G] [MeasurableSpace X] (μ : Measure X) (ρ : G → X → X) (NN D D' : Set X), MeasurableSet NN → μ NNᶜ = 0 → MeasurableSet D → MeasurableSet D' → (∀ x, ρ 1 x = x) → (∀ g h x, ρ (g * h) x = ρ g (ρ h x)) → (∀ g, ∀ x ∈ NN, ρ g x ∈ NN) → (∀ g, MeasurePreserving (ρ g) μ μ) → (∀ x ∈ NN, ∃! g : G, ρ g x ∈ D) → (∀ x ∈ NN, ∃! g : G, ρ g x ∈ D') → μ D = μ D' :=
  @strictFD_measure_eq

end GlobalTheory.SnMass.VolN
end

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.strictFundamentalDomain_measure_eq : ∀ {G X : Type} [Group G] [Countable G] [MeasurableSpace X] (μ : Measure X) (ρ : G → X → X) (NN D D' : Set X), MeasurableSet NN → μ NNᶜ = 0 → MeasurableSet D → MeasurableSet D' → (∀ x, ρ 1 x = x) → (∀ g h x, ρ (g * h) x = ρ g (ρ h x)) → (∀ g, ∀ x ∈ NN, ρ g x ∈ NN) → (∀ g, MeasurePreserving (ρ g) μ μ) → (∀ x ∈ NN, ∃! g : G, ρ g x ∈ D) → (∀ x ∈ NN, ∃! g : G, ρ g x ∈ D') → μ D = μ D' := by
  atlas_forward_decl GlobalTheory.SnMass.VolN.strictFD_measure_eq
end

section
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors

noncomputable section

namespace GlobalTheory.SnMass.VolN.DepOne

theorem Hpk_mulVec_e {k r : ℕ} (v : Fin (2 * r + k + 1) → ℂ) (a : Fin r) :
    (Hpk k r *ᵥ v) (eI k r a) = v (esI k r a) := by
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single (esI k r a)]
  · have := a.isLt
    have h1 : (eI k r a).val = a.val := rfl
    have h2 : (esI k r a).val = 2 * r + k - a.val := rfl
    unfold Hpk
    rw [if_pos (by omega), one_mul]
  · intro l _ hl
    have hl' : l.val ≠ 2 * r + k - a.val := fun h => hl (Fin.ext h)
    have := a.isLt
    simp only [Hpk, eI, Fin.ext_iff]
    split_ifs <;> first | omega | simp
  · simp

theorem Hpk_e_es {k r : ℕ} (a b : Fin r) :
    Hpk k r (eI k r a) (esI k r b) = if a = b then 1 else 0 := by
  have ha := a.isLt
  have hb := b.isLt
  have h1 : (eI k r a).val = a.val := rfl
  have h2 : (esI k r b).val = 2 * r + k - b.val := rfl
  unfold Hpk
  by_cases hab : a = b
  · subst hab
    rw [if_pos (by omega), if_pos rfl]
  · have hab' : a.val ≠ b.val := fun h => hab (Fin.ext h)
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg hab]

theorem es_es {k r : ℕ} {x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hx : x ∈ Nset k r)
    (b : Fin r) : ∀ (n : ℕ) (a : Fin r), a.val = n → a ≤ b →
      x (esI k r a) (esI k r b) = if a = b then 1 else 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro a han hab
  have hU : xᴴ * Hpk k r * x = Hpk k r := hx.1
  have h := congrFun (congrFun hU (eI k r a)) (esI k r b)
  rw [Matrix.mul_assoc, Hpk_e_es] at h
  have hs : (xᴴ * (Hpk k r * x)) (eI k r a) (esI k r b) =
      ∑ i, star (x i (eI k r a)) * (Hpk k r *ᵥ fun l => x l (esI k r b)) i := by
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, Finset.mul_sum]
  rw [hs, Finset.sum_eq_single (eI k r a)] at h
  · rw [Hpk_mulVec_e, hx.2.1 a (eI k r a) le_rfl, if_pos rfl, star_one, one_mul] at h
    exact h
  · intro i _ hi
    by_cases hia : a.val ≤ i.val
    · rw [hx.2.1 a i hia, if_neg hi, star_zero, zero_mul]
    · have ha := a.isLt
      obtain ⟨c, rfl⟩ : ∃ c : Fin r, i = eI k r c := ⟨⟨i.val, by omega⟩, Fin.ext rfl⟩
      have hca : c.val < a.val := by simpa [eI] using not_le.1 hia
      rw [Hpk_mulVec_e]
      have hcb : c ≤ b := le_trans (le_of_lt (show c < a from hca)) hab
      rw [ih c.val (han ▸ hca) c rfl hcb, if_neg (fun h => by
        subst h; exact absurd hab (not_le.2 hca)), mul_zero]
  · simp

theorem dep_one : ∀ (k r : ℕ) (x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ),
    x ∈ Nset k r → Dep k r 1 (x - 1) := by
  intro k r x hx i j hij
  rw [Matrix.sub_apply, Matrix.one_apply, sub_eq_zero]
  have hi := i.isLt
  have hj := j.isLt
  simp only [pos] at hij
  by_cases hjr : j.val < r
  · have hji : j.val ≤ i.val := by split_ifs at hij <;> omega
    have e : j = eI k r ⟨j.val, hjr⟩ := Fin.ext rfl
    have := hx.2.1 ⟨j.val, hjr⟩ i hji
    rw [← e] at this
    exact this
  by_cases hjm : j.val ≤ r + k
  · have hri : r ≤ i.val := by split_ifs at hij <;> omega
    exact hx.2.2 i j (by omega) hjm hri
  · have hji : j.val ≤ i.val := by split_ifs at hij <;> omega
    have hb : 2 * r + k - j.val < r := by omega
    have hc : 2 * r + k - i.val < r := by omega
    have ej : j = esI k r ⟨2 * r + k - j.val, hb⟩ := Fin.ext (by simp [esI]; omega)
    have ei : i = esI k r ⟨2 * r + k - i.val, hc⟩ := Fin.ext (by simp [esI]; omega)
    have key := es_es hx ⟨2 * r + k - j.val, hb⟩ _ ⟨2 * r + k - i.val, hc⟩ rfl
      (by rw [Fin.mk_le_mk]; omega)
    rw [← ei, ← ej] at key
    rw [key]
    by_cases hij' : i = j
    · subst hij'; simp
    · rw [if_neg hij', if_neg]
      intro h
      apply hij'
      rw [ei, ej, h]

end GlobalTheory.SnMass.VolN.DepOne
end
end

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagUnipotent_block_upper_unitriangular : ∀ (k r : ℕ) (x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ), x ∈ Nset k r → Dep k r 1 (x - 1) := by
  atlas_forward_decl GlobalTheory.SnMass.VolN.DepOne.dep_one
end

section
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors

namespace GlobalTheory.SnMass.VolN.LeftMul

theorem pos_eI (k r : ℕ) (a : Fin r) : pos k r (eI k r a) = a.val := by
  have := a.isLt
  unfold pos eI
  dsimp only
  split_ifs <;> omega

theorem pos_wI (k r : ℕ) (j : Fin (k + 1)) : pos k r (wI k r j) = r := by
  have := j.isLt
  unfold pos wI
  dsimp only
  split_ifs <;> omega

theorem pos_esI (k r : ℕ) (a : Fin r) : pos k r (esI k r a) = 2 * r - a.val := by
  have := a.isLt
  unfold pos esI
  dsimp only
  split_ifs <;> omega

theorem mul_apply_of_dep (k r d : ℕ) (g x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (hg : Dep k r d (g - 1)) (hx : Dep k r 1 (x - 1)) (i j : Fin (2 * r + k + 1)) (hij : i ≠ j)
    (hp : pos k r j ≤ pos k r i + d) : (g * x) i j = g i j + x i j := by
  have h1 : g * x = (g - 1) * (x - 1) + (g - 1) + (x - 1) + 1 := by noncomm_ring
  have h2 : ((g - 1) * (x - 1)) i j = 0 := by
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro l _
    by_cases hl : pos k r l < pos k r i + d
    · rw [hg i l hl, zero_mul]
    · rw [hx l j (by omega), mul_zero]
  rw [h1, Matrix.add_apply, Matrix.add_apply, Matrix.add_apply, h2, Matrix.sub_apply, Matrix.sub_apply,
    Matrix.one_apply_ne hij]
  ring

end GlobalTheory.SnMass.VolN.LeftMul

namespace GlobalTheory.SnMass.VolN

open GlobalTheory.SnMass.VolN.LeftMul in

theorem cM_mul_of_dep : ∀ (k r : ℕ) (g x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (d : ℕ),
    Dep k r d (g - 1) → Dep k r 1 (x - 1) → ∀ β : Bk r, degB r β ≤ d →
      cM k r β (Matrix.of.symm (g * x)) = cM k r β (Matrix.of.symm x) + cM k r β (Matrix.of.symm g) := by
  intro k r g x d hg hx β hβ
  rcases β with p | a | p | a
  · have hlt : p.1.1.val < p.1.2.val := p.2
    simp only [degB] at hβ
    show (g * x) (eI k r p.1.1) (eI k r p.1.2) = x (eI k r p.1.1) (eI k r p.1.2) + g (eI k r p.1.1) (eI k r p.1.2)
    rw [mul_apply_of_dep k r d g x hg hx _ _ ?_ ?_, add_comm]
    · intro h; have := congrArg Fin.val h; simp only [eI] at this; omega
    · rw [pos_eI, pos_eI]; omega
  · simp only [degB] at hβ
    have ha := a.isLt
    show (fun j => (g * x) (eI k r a) (wI k r j)) = (fun j => x (eI k r a) (wI k r j)) + (fun j => g (eI k r a) (wI k r j))
    funext l
    rw [Pi.add_apply, mul_apply_of_dep k r d g x hg hx _ _ ?_ ?_, add_comm]
    · intro h; have := congrArg Fin.val h; simp only [eI, wI] at this; omega
    · rw [pos_eI, pos_wI]; omega
  · have hlt : p.1.1.val < p.1.2.val := p.2
    have hb := p.1.2.isLt
    simp only [degB] at hβ
    show (g * x) (eI k r p.1.1) (esI k r p.1.2) = x (eI k r p.1.1) (esI k r p.1.2) + g (eI k r p.1.1) (esI k r p.1.2)
    rw [mul_apply_of_dep k r d g x hg hx _ _ ?_ ?_, add_comm]
    · intro h; have := congrArg Fin.val h; simp only [eI, esI] at this; omega
    · rw [pos_eI, pos_esI]; omega
  · simp only [degB] at hβ
    have ha := a.isLt
    show ((g * x) (eI k r a) (esI k r a)).im = (x (eI k r a) (esI k r a)).im + (g (eI k r a) (esI k r a)).im
    rw [mul_apply_of_dep k r d g x hg hx _ _ ?_ ?_, Complex.add_im, add_comm]
    · intro h; have := congrArg Fin.val h; simp only [eI, esI] at this; omega
    · rw [pos_eI, pos_esI]; omega

end GlobalTheory.SnMass.VolN
end

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unipotentBlockEntries_mul_of_hasFlagDepthAtLeast : ∀ (k r : ℕ) (g x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (d : ℕ), Dep k r d (g - 1) → Dep k r 1 (x - 1) → ∀ β : Bk r, degB r β ≤ d → cM k r β (Matrix.of.symm (g * x)) = cM k r β (Matrix.of.symm x) + cM k r β (Matrix.of.symm g) := by
  atlas_forward_decl GlobalTheory.SnMass.VolN.cM_mul_of_dep
end

section
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors

namespace GlobalTheory.SnMass.VolN

theorem re_corner_eq_zero (k r : ℕ) (x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (a : Fin r)
    (hx : x ∈ Nset k r) (hd : Dep k r (2 * r - 2 * a.val) (x - 1)) :
    (x (eI k r a) (esI k r a)).re = 0 := by
  have hsv : (esI k r a).val = 2 * r + k - a.val := rfl
  have hev : (eI k r a).val = a.val := rfl
  generalize esI k r a = s at *
  generalize eI k r a = e at *
  have ha := a.isLt

  have hcol : ∀ i : Fin (2 * r + k + 1), a.val < i.val → i ≠ s → x i s = 0 := by
    intro i hi hne
    have h0 := hd i s (by
      simp only [pos]
      split_ifs <;> first | rfl | omega | (exfalso; omega))
    rw [Matrix.sub_apply, Matrix.one_apply_ne hne, sub_zero] at h0; exact h0
  have hss : x s s = 1 := by
    have h0 := hd s s (by simp only [pos]; split_ifs <;> first | rfl | omega | (exfalso; omega))
    rw [Matrix.sub_apply, Matrix.one_apply_eq, sub_eq_zero] at h0; exact h0
  have hU := congrFun (congrFun hx.1 s) s
  have hH : Hpk k r s s = 0 := by
    simp only [Hpk, Fin.ext_iff, and_true]
    split_ifs <;> first | rfl | omega | (exfalso; omega)
  rw [hH] at hU
  have key : ∀ i j : Fin (2 * r + k + 1), star (x i s) * Hpk k r i j * x j s =
      (if i = s ∧ j = e then x j s else 0) + (if i = e ∧ j = s then star (x i s) else 0) := by
    intro i j
    by_cases h1 : i = s ∧ j = e
    · rw [h1.1, h1.2]
      have hes : e ≠ s := fun h => by have := congrArg Fin.val h; omega
      have : Hpk k r s e = 1 := by simp only [Hpk, Fin.ext_iff, and_true]; split_ifs <;> first | rfl | omega | (exfalso; omega)
      simp [hes, hes.symm, this, hss]
    by_cases h2 : i = e ∧ j = s
    · rw [h2.1, h2.2]
      have hes : e ≠ s := fun h => by have := congrArg Fin.val h; omega
      have : Hpk k r e s = 1 := by simp only [Hpk, Fin.ext_iff, and_true]; split_ifs <;> first | rfl | omega | (exfalso; omega)
      simp [hes, hes.symm, this, hss]
    rw [if_neg h1, if_neg h2, add_zero]
    have hi : i = s ∨ i.val ≤ a.val ∨ x i s = 0 := by
      by_cases h : i = s
      · exact Or.inl h
      by_cases h' : i.val ≤ a.val
      · exact Or.inr (Or.inl h')
      exact Or.inr (Or.inr (hcol i (by omega) h))
    have hj : j = s ∨ j.val ≤ a.val ∨ x j s = 0 := by
      by_cases h : j = s
      · exact Or.inl h
      by_cases h' : j.val ≤ a.val
      · exact Or.inr (Or.inl h')
      exact Or.inr (Or.inr (hcol j (by omega) h))
    have hI : ∀ i : Fin (2 * r + k + 1), i = s ↔ i.val = 2 * r + k - a.val := fun i =>
      ⟨fun h => h ▸ hsv, fun h => Fin.ext (h.trans hsv.symm)⟩
    have hE : ∀ i : Fin (2 * r + k + 1), i = e ↔ i.val = a.val := fun i =>
      ⟨fun h => h ▸ hev, fun h => Fin.ext (h.trans hev.symm)⟩
    rw [hI, hE] at h1 h2
    rcases hi with hi | hi | hi
    · rcases hj with hj | hj | hj
      · subst hi; subst hj; simp [hH]
      · have : Hpk k r i j = 0 := by
          rw [hI] at hi
          simp only [Hpk, Fin.ext_iff, and_true]; split_ifs <;> first | rfl | omega | (exfalso; omega)
        simp [this]
      · simp [hj]
    · rcases hj with hj | hj | hj
      · have : Hpk k r i j = 0 := by
          rw [hI] at hj
          simp only [Hpk, Fin.ext_iff, and_true]; split_ifs <;> first | rfl | omega | (exfalso; omega)
        simp [this]
      · have : Hpk k r i j = 0 := by
          simp only [Hpk, Fin.ext_iff, and_true]; split_ifs <;> first | rfl | omega | (exfalso; omega)
        simp [this]
      · simp [hj]
    · simp [hi]
  have hsum : (xᴴ * Hpk k r * x) s s = x e s + star (x e s) := by
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    simp_rw [key, Finset.sum_add_distrib]
    simp [ite_and, hss]
  rw [hsum] at hU
  have := congrArg Complex.re hU
  simp at this
  linarith

end GlobalTheory.SnMass.VolN
end

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.re_antidiagonal_entry_eq_zero_of_flagDepth : ∀ (k r : ℕ) (x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (a : Fin r), x ∈ Nset k r → Dep k r (2 * r - 2 * a.val) (x - 1) → (x (eI k r a) (esI k r a)).re = 0 := by
  atlas_forward_decl GlobalTheory.SnMass.VolN.re_corner_eq_zero
end

section
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors

namespace GlobalTheory.SnMass.VolN

theorem actM_measurePreserving (E : Type) [Field E] [NumberField E] (k r : ℕ)
    (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E) (hN : ∀ w, gM A γ w ∈ Nset k r) :
    MeasurePreserving (actM A γ) (Measure.pi fun _ : InfinitePlace E => haarLie (Nset k r) 1)
      (Measure.pi fun _ : InfinitePlace E => haarLie (Nset k r) 1) := by
  have hH := (GlobalTheory.T.haar_lie_nilpotent_coordinates k r).1
  haveI : SigmaFinite (haarLie (Nset k r) 1) := hH.1
  have hf : ∀ w, MeasurePreserving (lmulM (gM A γ w)) (haarLie (Nset k r) 1) (haarLie (Nset k r) 1) :=
    fun w => ⟨GlobalTheory.Amp.StabMeas.meas_lmul _, hH.2.2.2 _ (hN w)⟩
  exact measurePreserving_pi (fun _ : InfinitePlace E => haarLie (Nset k r) 1) (fun _ => haarLie (Nset k r) 1) hf

end GlobalTheory.SnMass.VolN
end

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unipotentModelProductAction_measurePreserving : ∀ (E : Type) [Field E] [NumberField E] (k r : ℕ) (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E), (∀ w, gM A γ w ∈ Nset k r) → MeasurePreserving (actM A γ) (Measure.pi fun _ : InfinitePlace E => haarLie (Nset k r) 1) (Measure.pi fun _ : InfinitePlace E => haarLie (Nset k r) 1) := by
  atlas_forward_decl GlobalTheory.SnMass.VolN.actM_measurePreserving
end

section
section
noncomputable section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors

namespace GlobalTheory.SnMass.VolN

theorem det_embed_ne_zero {E : Type} [Field E] [NumberField E] {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (hJ : J.det ≠ 0)
    (w : InfinitePlace E) : (J.map w.embedding).det ≠ 0 := by
  rw [show J.map w.embedding = w.embedding.mapMatrix J from rfl, ← RingHom.map_det]
  exact (map_ne_zero _).mpr hJ

theorem A_isUnit_det {E : Type} [Field E] [NumberField E] {k r : ℕ}
    (J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E)
    (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (hJ : J.det ≠ 0) (hA : IsModelAt J A) (w : InfinitePlace E) : IsUnit (A w).det := by
  rw [isUnit_iff_ne_zero]
  intro h0
  have h : ((A w)ᴴ * Hpk k r * A w).det = (J.map w.embedding).det := congrArg Matrix.det (hA w)
  rw [det_mul, det_mul, h0, mul_zero] at h
  exact det_embed_ne_zero J hJ w h.symm

theorem actLaws (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (k r : ℕ) (J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E) (Λ : Submodule (𝓞 E) (Fin (2 * r + k + 1) → E)) (P : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) E) (f : Matrix (Fin (2 * r + k + 1)) (Fin r) E) (T : F) (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (s : Fin r → ℝ) :
    IsVolData σ J Λ P f T A s → (∀ x, actM A 1 x = x) ∧ (∀ γ γ' x, actM A (γ * γ') x = actM A γ (actM A γ' x)) ∧ ∀ γ, (∀ w, gM A γ w = 1) → γ = 1 := by
  intro h
  have hJ : J.det ≠ 0 := h.2.2.1.2
  have hA : IsModelAt J A := h.2.2.2.2.2.2.2.1
  have hu : ∀ w, IsUnit (A w).det := fun w => A_isUnit_det J A hJ hA w
  refine ⟨?_, ?_, ?_⟩
  · intro x
    funext w
    have e : (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E).map w.embedding = 1 :=
      map_one w.embedding.mapMatrix
    simp only [actM, e, Matrix.mul_one, Matrix.mul_nonsing_inv _ (hu w), Matrix.one_mul]
    rfl
  · intro γ γ' x
    funext w
    have e : (γ * γ').map w.embedding = γ.map w.embedding * γ'.map w.embedding :=
      map_mul w.embedding.mapMatrix γ γ'
    have m : A w * (γ.map w.embedding * γ'.map w.embedding) * (A w)⁻¹ * Matrix.of (x w) =
        A w * γ.map w.embedding * (A w)⁻¹ * (A w * γ'.map w.embedding * (A w)⁻¹ * Matrix.of (x w)) := by
      simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ (hu w)]
    show Matrix.of.symm (A w * (γ * γ').map w.embedding * (A w)⁻¹ * Matrix.of (x w)) =
      Matrix.of.symm (A w * γ.map w.embedding * (A w)⁻¹ *
        Matrix.of (Matrix.of.symm (A w * γ'.map w.embedding * (A w)⁻¹ * Matrix.of (x w))))
    rw [Equiv.apply_symm_apply, e, m]
  · intro γ hγ
    obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
    have hi : (A w)⁻¹ * A w = 1 := Matrix.nonsing_inv_mul _ (hu w)
    have h1 : γ.map w.embedding = 1 := by
      have e : A w * γ.map w.embedding * (A w)⁻¹ = 1 := hγ w
      calc γ.map w.embedding = (A w)⁻¹ * (A w * γ.map w.embedding * (A w)⁻¹) * A w := by
            simp only [Matrix.mul_assoc, hi, Matrix.mul_one, Matrix.nonsing_inv_mul_cancel_left _ _ (hu w)]
        _ = 1 := by rw [e, Matrix.mul_one, hi]
    ext i j
    apply w.embedding.injective
    have := congrArg (fun M => M i j) h1
    simpa [Matrix.one_apply, apply_ite] using this

end GlobalTheory.SnMass.VolN
end
end

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unipotentModelAction_isAction_and_faithful : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (k r : ℕ) (J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E) (Λ : Submodule (𝓞 E) (Fin (2 * r + k + 1) → E)) (P : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) E) (f : Matrix (Fin (2 * r + k + 1)) (Fin r) E) (T : F) (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (s : Fin r → ℝ), IsVolData σ J Λ P f T A s → (∀ x, actM A 1 x = x) ∧ (∀ γ γ' x, actM A (γ * γ') x = actM A γ (actM A γ' x)) ∧ ∀ γ, (∀ w, gM A γ w = 1) → γ = 1 := by
  atlas_forward_decl GlobalTheory.SnMass.VolN.actLaws
end

section
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors

noncomputable section

namespace GlobalTheory.SnMass.VolN.IntU

theorem hpk_row (k r : ℕ) (a : Fin r) (j : Fin (2 * r + k + 1)) :
    Hpk k r (esI k r a) j = if j = eI k r a then 1 else 0 := by
  simp only [Hpk, esI, eI, Fin.ext_iff]
  split_ifs <;> first | rfl | omega

theorem hpk_mulVec_esI (k r : ℕ) (a : Fin r) (z : Fin (2 * r + k + 1) → ℂ) :
    (Hpk k r *ᵥ z) (esI k r a) = z (eI k r a) := by
  simp [Matrix.mulVec, dotProduct, hpk_row]

theorem coord_eI {E : Type} [Field E] {k r : ℕ} (σ : E →+* E) (τ : E →+* ℂ)
    (hτ : ∀ x, τ (σ x) = star (τ x)) (J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E)
    (B : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (hB : Bᴴ * Hpk k r * B = J.map τ)
    (x y : Fin (2 * r + k + 1) → E) (a : Fin r) (s : ℝ) (hs : s ≠ 0)
    (hy : B *ᵥ (fun i => τ (y i)) = (s : ℂ)⁻¹ • bvec (esI k r a)) :
    (B *ᵥ fun i => τ (x i)) (eI k r a) = (s : ℂ) * τ (form σ J x y) := by
  have key : star (B *ᵥ (fun i => τ (y i))) ⬝ᵥ (Hpk k r *ᵥ (B *ᵥ fun i => τ (x i))) =
      star (fun i => τ (y i)) ⬝ᵥ (J.map τ *ᵥ fun i => τ (x i)) := by
    rw [← hB]
    simp only [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, Matrix.mulVec_mulVec,
      Matrix.mul_assoc]
  have lhs : star (B *ᵥ (fun i => τ (y i))) ⬝ᵥ (Hpk k r *ᵥ (B *ᵥ fun i => τ (x i))) =
      (s : ℂ)⁻¹ * (B *ᵥ fun i => τ (x i)) (eI k r a) := by
    rw [hy, star_smul, bvec, ← hpk_mulVec_esI k r a (B *ᵥ fun i => τ (x i))]
    simp [Pi.star_def, dotProduct, Pi.single_apply, -Matrix.mulVec_mulVec]
  have rhs : star (fun i => τ (y i)) ⬝ᵥ (J.map τ *ᵥ fun i => τ (x i)) = τ (form σ J x y) := by
    simp only [form, dotProduct, map_sum, map_mul, hτ, RingHom.map_mulVec]
    rfl
  rw [lhs, rhs] at key
  rw [← key, ← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast hs), one_mul]

end GlobalTheory.SnMass.VolN.IntU

namespace GlobalTheory.SnMass.VolN.IntU

theorem form_smul_smul {E : Type} [Field E] {n : ℕ} (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E)
    (c c' : E) (x y : Fin n → E) : form σ J (c • x) (c' • y) = c * σ c' * form σ J x y := by
  simp only [form, dotProduct, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem mem_of_pair {E : Type} [Field E] [NumberField E] (σ : E →+* E) (hσ : ∀ x, σ (σ x) = x)
    (𝔞 𝔟 : FractionalIdeal (𝓞 E)⁰ E) (h𝔞 : 𝔞 ≠ 0) (h𝔟 : 𝔟 ≠ 0) (hst : FrameDual.Stab σ 𝔞⁻¹) (u : E)
    (hu : ∀ c ∈ 𝔟, ∀ c' ∈ 𝔞⁻¹, c * σ c' * u ∈ (algebraMap (𝓞 E) E).range) : u ∈ 𝔞 * 𝔟⁻¹ := by
  have hI : 𝔟 * 𝔞⁻¹ ≠ 0 := mul_ne_zero h𝔟 (inv_ne_zero h𝔞)
  have e : 𝔞 * 𝔟⁻¹ = (𝔟 * 𝔞⁻¹)⁻¹ := by rw [mul_inv, inv_inv, mul_comm]
  rw [e, FractionalIdeal.mem_inv_iff hI]
  intro y hy
  refine FractionalIdeal.mul_induction_on hy (fun c hc d hd => ?_) (fun y₁ y₂ h₁ h₂ => ?_)
  · have := hu c hc (σ d) (hst d hd)
    rw [hσ] at this
    obtain ⟨t, ht⟩ := this
    exact (FractionalIdeal.mem_one_iff _).2 ⟨t, by rw [ht]; ring⟩
  · rw [mul_add]; exact Submodule.add_mem (1 : FractionalIdeal (𝓞 E)⁰ E).coeToSubmodule h₁ h₂

end GlobalTheory.SnMass.VolN.IntU

open GlobalTheory.SnMass.VolN.IntU in

theorem GlobalTheory.SnMass.VolN.gM_entry_mem_ideLat : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (k r : ℕ) (J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E) (Λ : Submodule (𝓞 E) (Fin (2 * r + k + 1) → E)) (P : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) E) (f : Matrix (Fin (2 * r + k + 1)) (Fin r) E) (T : F) (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (s : Fin r → ℝ), IsVolData σ J Λ P f T A s → ∀ γ ∈ GN (σ : E →+* E) J Λ P, ∀ p : UTr r, (fun w => gM A γ w (eI k r p.1.1) (eI k r p.1.2)) ∈ ideLat (dInv E (r - p.1.1.val) * (dInv E (r - p.1.2.val))⁻¹) (s p.1.1 / s p.1.2) := by
  intro F E _ _ _ _ _ σ k r J Λ P f T A s hV γ hγ p
  obtain ⟨hCM, -, hND, hSD, -, -, hTup, hMod, hs, hAd⟩ := hV
  obtain ⟨⟨a, b⟩, hab⟩ := p
  dsimp only
  have hconj : ∀ (τ : E →+* ℂ) (x : E), τ (σ x) = star (τ x) := hCM.2.2.2
  have hσ : ∀ x, (σ : E →+* E) ((σ : E →+* E) x) = x := by
    intro x
    show σ (σ x) = x
    exact (Classical.arbitrary (InfinitePlace E)).embedding.injective (by rw [hconj, hconj, star_star])
  set eb : Fin (2 * r + k + 1) → E := fun i => P i b.castSucc with heb
  set fa : Fin (2 * r + k + 1) → E := fun i => f i a with hfa
  refine ⟨form (σ : E →+* E) J (γ *ᵥ eb) fa, ?_, fun w => ?_⟩
  · refine mem_of_pair (σ : E →+* E) hσ _ _ (FrameDual.dInv_ne_zero _) (FrameDual.dInv_ne_zero _)
      ((FrameDual.stab_dInv hσ _).inv hσ (FrameDual.dInv_ne_zero _)) _ ?_
    intro c hc c' hc'
    have h1 : c • eb ∈ Λ := hTup (Submodule.subset_span
      ⟨Fin.castAdd r b.castSucc, c, by rw [FrameDual.frameDualTupleIdeals_castAdd]; exact hc, by
        funext i; simp [heb, sideM]⟩)
    have h2 : c' • fa ∈ Λ := hTup (Submodule.subset_span
      ⟨Fin.natAdd (r + 1) a, c', by rw [FrameDual.frameDualTupleIdeals_natAdd]; exact hc', by
        funext i; simp [hfa, sideM]⟩)
    have h3 : γ *ᵥ (c • eb) ∈ Λ := by
      rw [← hγ.2]; exact ⟨_, h1, rfl⟩
    have h4 := (hSD.2 _).1 h3 _ h2
    rwa [Matrix.mulVec_smul, form_smul_smul] at h4
  · set τ := w.embedding with hτ
    have hB := hMod w
    have hdet : IsUnit (A w).det := by
      refine Ne.isUnit fun h0 => hND.2 ?_
      have := congrArg Matrix.det hB
      rw [Matrix.det_mul, Matrix.det_mul, h0, mul_zero, ← RingHom.mapMatrix_apply, ← RingHom.map_det] at this
      exact (map_eq_zero τ).1 this.symm
    have hsb : (s b : ℂ) ≠ 0 := by exact_mod_cast (hs b).ne'
    have hbv : bvec (eI k r b) = (s b : ℂ)⁻¹ • (A w *ᵥ fun i => τ (eb i)) := by
      rw [(hAd w b).1, smul_smul, inv_mul_cancel₀ hsb, one_smul]
    have hmap : (γ.map τ *ᵥ fun i => τ (eb i)) = fun i => τ ((γ *ᵥ eb) i) := by
      funext i; exact (RingHom.map_mulVec τ γ eb i).symm
    have hent : gM A γ w (eI k r a) (eI k r b) =
        (s b : ℂ)⁻¹ * (A w *ᵥ fun i => τ ((γ *ᵥ eb) i)) (eI k r a) := by
      have e1 : gM A γ w (eI k r a) (eI k r b) = (gM A γ w *ᵥ bvec (eI k r b)) (eI k r a) := by
        simp [bvec]
      rw [e1, hbv, Matrix.mulVec_smul, gM, Matrix.mulVec_mulVec, Matrix.mul_assoc (A w * γ.map τ),
        Matrix.nonsing_inv_mul _ hdet, Matrix.mul_one, ← Matrix.mulVec_mulVec, hmap]
      rfl
    show gM A γ w (eI k r a) (eI k r b) = _
    rw [hent, coord_eI (σ : E →+* E) τ (hconj τ) J (A w) hB (γ *ᵥ eb) fa a (s a) (hs a).ne' (hAd w a).2]
    push_cast
    ring
end
end

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralUnipotent_entry_mem_inverseDifferentLattice : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (k r : ℕ) (J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E) (Λ : Submodule (𝓞 E) (Fin (2 * r + k + 1) → E)) (P : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) E) (f : Matrix (Fin (2 * r + k + 1)) (Fin r) E) (T : F) (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (s : Fin r → ℝ), IsVolData σ J Λ P f T A s → ∀ γ ∈ GN (σ : E →+* E) J Λ P, ∀ p : UTr r, (fun w => gM A γ w (eI k r p.1.1) (eI k r p.1.2)) ∈ ideLat (dInv E (r - p.1.1.val) * (dInv E (r - p.1.2.val))⁻¹) (s p.1.1 / s p.1.2) := by
  atlas_forward_decl GlobalTheory.SnMass.VolN.gM_entry_mem_ideLat
end

section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralUnipotent_middleRow_mem_homLattice : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (k r : ℕ) (J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E) (Λ : Submodule (𝓞 E) (Fin (2 * r + k + 1) → E)) (P : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) E) (f : Matrix (Fin (2 * r + k + 1)) (Fin r) E) (T : F) (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (s : Fin r → ℝ), IsVolData σ J Λ P f T A s → ∀ γ ∈ GN (σ : E →+* E) J Λ P, ∀ a : Fin r, (fun w (l : Fin (k + 1)) => gM A γ w (eI k r a) (wI k r l)) ∈ homLat (σ : E →+* E) J Λ P f A (dInv E (r - a.val)) (s a) := by
  first | exact @GlobalTheory.SnMass.VolN.row_mem_homLat | exact GlobalTheory.SnMass.VolN.row_mem_homLat | (intros; apply GlobalTheory.SnMass.VolN.row_mem_homLat <;> assumption)
end

section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralUnipotent_antidiagonal_mem_skewLattice : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (k r : ℕ) (J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E) (Λ : Submodule (𝓞 E) (Fin (2 * r + k + 1) → E)) (P : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) E) (f : Matrix (Fin (2 * r + k + 1)) (Fin r) E) (T : F) (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (s : Fin r → ℝ), IsVolData σ J Λ P f T A s → ∀ γ ∈ GN (σ : E →+* E) J Λ P, ∀ a : Fin r, (∀ w, (gM A γ w (eI k r a) (esI k r a)).re = 0) → (fun w => (gM A γ w (eI k r a) (esI k r a)).im) ∈ skewLat (σ : E →+* E) (dInv E (2 * (r - a.val))) (s a ^ 2) := by
  first | exact @GlobalTheory.SnMass.VolN.IntG.antidiag_mem_skewLat | exact GlobalTheory.SnMass.VolN.IntG.antidiag_mem_skewLat | (intros; apply GlobalTheory.SnMass.VolN.IntG.antidiag_mem_skewLat <;> assumption)
end

section
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors

namespace GlobalTheory.SnMass.VolN

theorem nset_closed (k r : ℕ) : IsClosed {y : Mt k r | Matrix.of y ∈ Nset k r} := by
  simp only [Nset, UH, Set.mem_setOf_eq, Set.setOf_and, Set.setOf_forall]
  refine IsClosed.inter ?_ (IsClosed.inter ?_ ?_)
  · have hc : Continuous fun y : Mt k r => (Matrix.of y)ᴴ * Hpk k r * Matrix.of y := by
      have h0 : Continuous fun y : Mt k r => (Matrix.of y : Matrix _ _ ℂ) := continuous_id
      exact (h0.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul h0
    exact isClosed_eq hc continuous_const
  · refine isClosed_iInter fun a => isClosed_iInter fun i => isClosed_iInter fun _ => ?_
    exact isClosed_eq ((continuous_apply _).comp (continuous_apply _)) continuous_const
  · refine isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
      isClosed_iInter fun _ => isClosed_iInter fun _ => ?_
    exact isClosed_eq ((continuous_apply _).comp (continuous_apply _)) continuous_const

theorem pi_nset_full : ∀ (ι : Type) [Fintype ι] (k r : ℕ), MeasurableSet {x : ι → Mt k r | ∀ w, Matrix.of (x w) ∈ Nset k r} ∧ (Measure.pi fun _ : ι => haarLie (Nset k r) 1) {x : ι → Mt k r | ∀ w, Matrix.of (x w) ∈ Nset k r}ᶜ = 0 := by
  intro ι _ k r
  have hS : MeasurableSet {y : Mt k r | Matrix.of y ∈ Nset k r} := (nset_closed k r).measurableSet
  have hH := (GlobalTheory.T.haar_lie_nilpotent_coordinates k r).1
  haveI : SigmaFinite (haarLie (Nset k r) 1) := hH.1
  have hset : {x : ι → Mt k r | ∀ w, Matrix.of (x w) ∈ Nset k r} =
      ⋂ w, Function.eval w ⁻¹' {y : Mt k r | Matrix.of y ∈ Nset k r} := by
    ext x; simp
  refine ⟨?_, ?_⟩
  · rw [hset]
    exact MeasurableSet.iInter fun w => measurable_pi_apply w hS
  · rw [hset, Set.compl_iInter]
    refine measure_iUnion_null fun w => ?_
    rw [← Set.preimage_compl]
    exact Measure.pi_eval_preimage_null _ (by simpa [Set.compl_setOf] using hH.2.2.1)

end GlobalTheory.SnMass.VolN
end

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pi_unipotentModel_measurable_full_measure : ∀ (ι : Type) [Fintype ι] (k r : ℕ), MeasurableSet {x : ι → Mt k r | ∀ w, Matrix.of (x w) ∈ Nset k r} ∧ (Measure.pi fun _ : ι => haarLie (Nset k r) 1) {x : ι → Mt k r | ∀ w, Matrix.of (x w) ∈ Nset k r}ᶜ = 0 := by
  atlas_forward_decl GlobalTheory.SnMass.VolN.pi_nset_full
end

section
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors

namespace GlobalTheory.SnMass.VolN.LiftCorner

lemma hpk_eI (k r : ℕ) (a : Fin r) (j : Fin (2 * r + k + 1)) :
    Hpk k r (eI k r a) j = if j = esI k r a then 1 else 0 := by
  have ha := a.isLt
  have hj := j.isLt
  simp only [Hpk, eI, esI, Fin.ext_iff]
  split_ifs <;> first | rfl | omega

lemma herm_bvec (k r : ℕ) (a : Fin r) (j : Fin (2 * r + k + 1)) (x : ℂ) :
    herm (Hpk k r) (bvec j) (x • bvec (eI k r a)) = star x * (if j = esI k r a then 1 else 0) := by
  rw [← hpk_eI]
  simp [herm, bvec, dotProduct, Matrix.mulVec, Pi.single_apply, apply_ite (starRingEnd ℂ), ite_mul]

lemma form_smul_left {E : Type} [Field E] (σ : E →+* E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (u v : Fin n → E) (x : E) : form σ J (x • u) v = x * form σ J u v := by
  simp [form, Matrix.mulVec_smul, dotProduct_smul]

lemma form_smul_right {E : Type} [Field E] (σ : E →+* E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (u v : Fin n → E) (x : E) : form σ J u (x • v) = σ x * form σ J u v := by
  simp [form, dotProduct, Finset.mul_sum, mul_assoc]

lemma form_cols {E : Type} [Field E] (σ : E →+* E) {n m : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (P : Matrix (Fin n) (Fin m) E) (x z : Fin m) :
    form σ J (fun i => P i z) (fun i => P i x) = pairM σ J P P x z := by
  simp only [form, pairM, cT, Matrix.mul_apply, dotProduct, Matrix.mulVec, Matrix.transpose_apply,
    Matrix.map_apply, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  exact Finset.sum_comm

theorem lift_corner : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (k r : ℕ) (J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E) (Λ : Submodule (𝓞 E) (Fin (2 * r + k + 1) → E)) (P : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) E) (f : Matrix (Fin (2 * r + k + 1)) (Fin r) E) (T : F) (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (s : Fin r → ℝ), IsVolData σ J Λ P f T A s → ∀ (p : UTr r) (l : InfinitePlace E → ℂ), l ∈ ideLat (dInv E (r - p.1.1.val) * dInv E (r - p.1.2.val)) (s p.1.1 * s p.1.2) → ∃ γ ∈ GN (σ : E →+* E) J Λ P, (∀ w, cM k r (.inr (.inr (.inl p))) (Matrix.of.symm (gM A γ w)) = l w) ∧ ∀ β : Bk r, β ≠ (.inr (.inr (.inl p))) → degB r β ≤ degB r (.inr (.inr (.inl p))) → ∀ w, cM k r β (Matrix.of.symm (gM A γ w)) = 0 := by
  intro F E _ _ _ _ _ σ k r J Λ P f T A s hV p l hl
  obtain ⟨⟨a, b⟩, hab⟩ := p
  have hab' : a.val < b.val := hab
  have ha := a.isLt
  have hb := b.isLt
  obtain ⟨-, -, -, -, hFr, -, hLat, -, -, hAd⟩ := id hV
  obtain ⟨c, hc, hlc⟩ := hl
  dsimp only at hc hlc
  let e : Fin (2 * r + k + 1) → E := fun i => P i a.castSucc
  let y : Fin (2 * r + k + 1) → E := c • e
  have hiso : ∀ x z : Fin r,
      form (σ : E →+* E) J (fun i => P i z.castSucc) (fun i => P i x.castSucc) = 0 := by
    intro x z
    rw [form_cols, hFr.2]
    simp [TF, Matrix.diagonal_apply, Fin.castSucc_ne_last]
  have hd : ∀ j, dInv E j ≠ 0 := fun j =>
    pow_ne_zero _ (inv_ne_zero (FractionalIdeal.coeIdeal_ne_zero.2 differentIdeal_ne_bot))
  have hG : rowE (σ : E →+* E) J (fun i => P i b.castSucc) y 0 ∈ GN (σ : E →+* E) J Λ P := by
    refine GlobalTheory.T.rowE_mem_GN_of_form_add_trace_eq_zero F E σ k r J Λ P f T A s hV b y 0 ?_ ?_ ?_ ?_
    · intro c' _
      show form _ J (c • e) _ = 0
      rw [form_smul_left, hiso, mul_zero]
    · show form _ J (c • e) (c • e) + 0 + (σ : E →+* E) 0 = 0
      rw [form_smul_left, form_smul_right, hiso]
      simp
    · intro c' hc'
      have hmem : c' * c ∈ dInv E (r - a.val) := by
        have := FractionalIdeal.mul_mem_mul hc' hc
        rwa [mul_comm (dInv E (r - a.val)), ← mul_assoc, inv_mul_cancel₀ (hd _), one_mul] at this
      have hy : c' • y = (c' * c) • e := by
        simp only [y, smul_smul]
      rw [hy]
      apply hLat
      apply Submodule.subset_span
      refine ⟨Fin.castAdd r a.castSucc, c' * c, ?_, ?_⟩
      · simpa [id1, Fin.append_left] using hmem
      · ext i
        simp [sideM, Fin.append_left, e]
    · exact (dInv E _ : Submodule (𝓞 E) E).zero_mem
  have hAy : ∀ w : InfinitePlace E, (A w).mulVec (fun l => w.embedding (y l)) =
      (w.embedding c * (s a : ℂ)) • bvec (eI k r a) := by
    intro w
    have h1 : (fun l => w.embedding (y l)) = w.embedding c • fun l => w.embedding (P l a.castSucc) := by
      ext l
      simp [y, e]
    rw [h1, Matrix.mulVec_smul, (hAd w a).1, smul_smul]
  have hent : ∀ w i j, gM A (rowE (σ : E →+* E) J (fun i => P i b.castSucc) y 0) w i j =
      (if i = j then 1 else 0) +
        (if i = eI k r a ∧ j = esI k r b then (s a : ℂ) * s b * w.embedding c else 0) -
        (if i = eI k r b ∧ j = esI k r a then (s b : ℂ) * star (w.embedding c * (s a : ℂ)) else 0) := by
    intro w i j
    rw [GlobalTheory.T.rowIsometry_entries_in_modelCoordinates F E σ k r J Λ P f T A s hV b y 0 w i j, hAy w, herm_bvec]
    simp only [bvec, Pi.smul_apply, Pi.single_apply, smul_eq_mul, map_zero, mul_zero, add_zero, ite_and]
    split_ifs <;> ring
  refine ⟨_, hG, fun w => ?_, fun β hβ _ w => ?_⟩
  · show gM A _ w (eI k r a) (esI k r b) = l w
    rw [hent, hlc w]
    have h1 : eI k r a ≠ esI k r b := by simp [Fin.ext_iff, eI, esI]; omega
    have h2 : eI k r a ≠ eI k r b := by simp [Fin.ext_iff, eI]; omega
    simp [h1, h2]
    first | done | (push_cast; ring)
  · rcases β with p' | a' | p' | a'
    · obtain ⟨⟨a', b'⟩, h'⟩ := p'
      have h'' : a'.val < b'.val := h'
      show gM A _ w (eI k r a') (eI k r b') = 0
      rw [hent]
      simp only [eI, esI, Fin.ext_iff]
      split_ifs <;> first | omega | simp
    · show (fun j' => gM A _ w (eI k r a') (wI k r j')) = (0 : Fin (k + 1) → ℂ)
      funext j'
      have := j'.isLt
      rw [hent]
      simp only [eI, esI, wI, Fin.ext_iff]
      split_ifs <;> first | omega | simp
    · obtain ⟨⟨a', b'⟩, h'⟩ := p'
      have h'' : a'.val < b'.val := h'
      have hne : ¬ (a'.val = a.val ∧ b'.val = b.val) := by
        rintro ⟨e1, e2⟩
        obtain rfl := Fin.ext e1
        obtain rfl := Fin.ext e2
        exact hβ rfl
      show gM A _ w (eI k r a') (esI k r b') = 0
      rw [hent]
      simp only [eI, esI, Fin.ext_iff]
      split_ifs <;> first | omega | simp
    · show (gM A _ w (eI k r a') (esI k r a')).im = 0
      rw [hent]
      simp only [eI, esI, Fin.ext_iff]
      split_ifs <;> first | omega | simp

end GlobalTheory.SnMass.VolN.LiftCorner
end

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_unipotent_lift_corner : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (k r : ℕ) (J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E) (Λ : Submodule (𝓞 E) (Fin (2 * r + k + 1) → E)) (P : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) E) (f : Matrix (Fin (2 * r + k + 1)) (Fin r) E) (T : F) (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (s : Fin r → ℝ), IsVolData σ J Λ P f T A s → ∀ (p : UTr r) (l : InfinitePlace E → ℂ), l ∈ ideLat (dInv E (r - p.1.1.val) * dInv E (r - p.1.2.val)) (s p.1.1 * s p.1.2) → ∃ γ ∈ GN (σ : E →+* E) J Λ P, (∀ w, cM k r (.inr (.inr (.inl p))) (Matrix.of.symm (gM A γ w)) = l w) ∧ ∀ β : Bk r, β ≠ (.inr (.inr (.inl p))) → degB r β ≤ degB r (.inr (.inr (.inl p))) → ∀ w, cM k r β (Matrix.of.symm (gM A γ w)) = 0 := by
  atlas_forward_decl GlobalTheory.SnMass.VolN.LiftCorner.lift_corner
end

section
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors

namespace GlobalTheory.SnMass.VolN

theorem exists_lift_antidiag : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (k r : ℕ) (J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E) (Λ : Submodule (𝓞 E) (Fin (2 * r + k + 1) → E)) (P : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) E) (f : Matrix (Fin (2 * r + k + 1)) (Fin r) E) (T : F) (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (s : Fin r → ℝ), IsVolData σ J Λ P f T A s → ∀ (a : Fin r) (l : InfinitePlace E → ℝ), l ∈ skewLat (σ : E →+* E) (dInv E (2 * (r - a.val))) (s a ^ 2) → ∃ γ ∈ GN (σ : E →+* E) J Λ P, (∀ w, cM k r (.inr (.inr (.inr a))) (Matrix.of.symm (gM A γ w)) = l w) ∧ ∀ β : Bk r, β ≠ (.inr (.inr (.inr a))) → degB r β ≤ degB r (.inr (.inr (.inr a))) → ∀ w, cM k r β (Matrix.of.symm (gM A γ w)) = 0 := by
  intro F E _ _ _ _ _ σ k r J Λ P f T A s hV a l hl
  obtain ⟨c, hc, hσ, hlw⟩ := hl
  have hσ' : σ c = -c := hσ
  refine ⟨rowE (σ : E →+* E) J (fun i => P i a.castSucc) 0 c, ?_, ?_⟩
  · refine GlobalTheory.T.rowE_mem_GN_of_form_add_trace_eq_zero F E σ k r J Λ P f T A s hV a 0 c ?_ ?_ ?_ hc
    · intro b _
      simp [form]
    · simp [form, hσ']
    · intro b _
      simp
  have hE : ∀ w i j, gM A (rowE (σ : E →+* E) J (fun i => P i a.castSucc) 0 c) w i j =
      (if i = j then 1 else 0) +
        (if j = esI k r a then (if i = eI k r a then (s a : ℂ) * ((s a : ℂ) * w.embedding c) else 0) else 0) := by
    intro w i j
    have h0 : (A w *ᵥ fun l => w.embedding ((0 : Fin (2 * r + k + 1) → E) l)) = 0 := by
      have h1 : (fun l => w.embedding ((0 : Fin (2 * r + k + 1) → E) l)) = 0 := by
        funext l
        simp
      rw [h1, mulVec_zero]
    rw [GlobalTheory.T.rowIsometry_entries_in_modelCoordinates F E σ k r J Λ P f T A s hV a 0 c w i j, h0]
    simp [herm]
  have hne : ∀ b b' : Fin r, eI k r b ≠ esI k r b' := by
    intro b b' h
    have := congrArg Fin.val h
    simp only [eI, esI] at this
    omega
  have hnw : ∀ (j : Fin (k + 1)) (b : Fin r), wI k r j ≠ esI k r b := by
    intro j b h
    have := congrArg Fin.val h
    simp only [wI, esI] at this
    omega
  have hnw' : ∀ (j : Fin (k + 1)) (b : Fin r), eI k r b ≠ wI k r j := by
    intro j b h
    have := congrArg Fin.val h
    simp only [wI, eI] at this
    omega
  have hee : ∀ b b' : Fin r, b ≠ b' → eI k r b ≠ eI k r b' := by
    intro b b' hb h
    apply hb
    have := congrArg Fin.val h
    simp only [eI] at this
    exact Fin.ext this
  have hss : ∀ b b' : Fin r, esI k r b = esI k r b' → b = b' := by
    intro b b' h
    have := congrArg Fin.val h
    simp only [esI] at this
    exact Fin.ext (by omega)
  constructor
  · intro w
    show ((gM A _ w) (eI k r a) (esI k r a)).im = l w
    rw [hE, hlw w]
    simp [hne a a, pow_two, mul_assoc, Complex.mul_im]
  · rintro (p | b | p | b) hβ _ w
    · show (gM A _ w) (eI k r p.1.1) (eI k r p.1.2) = 0
      rw [hE]
      have h1 : eI k r p.1.1 ≠ eI k r p.1.2 := hee _ _ (ne_of_lt p.2)
      simp [h1, (hne p.1.2 a)]
    · funext j
      show (gM A _ w) (eI k r b) (wI k r j) = 0
      rw [hE]
      simp [hnw' j b, hnw j a]
    · show (gM A _ w) (eI k r p.1.1) (esI k r p.1.2) = 0
      rw [hE]
      have h1 : p.1.1 ≠ p.1.2 := ne_of_lt p.2
      by_cases h2 : p.1.2 = a
      · have h3 : eI k r p.1.1 ≠ eI k r a := hee _ _ (h2 ▸ h1)
        simp [hne p.1.1 p.1.2, h3]
      · have h3 : esI k r p.1.2 ≠ esI k r a := fun h => h2 (hss _ _ h)
        simp [hne p.1.1 p.1.2, h3]
    · show ((gM A _ w) (eI k r b) (esI k r b)).im = 0
      rw [hE]
      have hb : b ≠ a := fun h => hβ (by rw [h])
      have h3 : esI k r b ≠ esI k r a := fun h => hb (hss _ _ h)
      simp [hne b b, h3]

end GlobalTheory.SnMass.VolN
end
end

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_unipotent_lift_antidiagonal : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (k r : ℕ) (J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E) (Λ : Submodule (𝓞 E) (Fin (2 * r + k + 1) → E)) (P : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) E) (f : Matrix (Fin (2 * r + k + 1)) (Fin r) E) (T : F) (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (s : Fin r → ℝ), IsVolData σ J Λ P f T A s → ∀ (a : Fin r) (l : InfinitePlace E → ℝ), l ∈ skewLat (σ : E →+* E) (dInv E (2 * (r - a.val))) (s a ^ 2) → ∃ γ ∈ GN (σ : E →+* E) J Λ P, (∀ w, cM k r (.inr (.inr (.inr a))) (Matrix.of.symm (gM A γ w)) = l w) ∧ ∀ β : Bk r, β ≠ (.inr (.inr (.inr a))) → degB r β ≤ degB r (.inr (.inr (.inr a))) → ∀ w, cM k r β (Matrix.of.symm (gM A γ w)) = 0 := by
  atlas_forward_decl GlobalTheory.SnMass.VolN.exists_lift_antidiag
end

section
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors

noncomputable section

namespace GlobalTheory.SnMass.VolN

theorem hasDom_ideLat_dInv_div : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → Algebra.FormallyUnramified (𝓞 F) (𝓞 E) → ∀ (t t' : ℕ) (c : ℝ), 0 < c → HasDom volume (ideLat (dInv E t * (dInv E t')⁻¹) c : Set (InfinitePlace E → ℂ)) (ENNReal.ofReal ((2⁻¹ : ℝ) ^ Fintype.card (InfinitePlace E) * |(NumberField.discr F : ℝ)| ^ (1 - 2 * (t : ℝ) + 2 * (t' : ℝ)) * c ^ (2 * Fintype.card (InfinitePlace E)))) := by
  intro F E _ _ _ _ _ σ hσ hu t t' c hc
  have hE : IsTotallyComplex E := hσ.2.1
  have hdE : (discr E : ℝ) ≠ 0 := by exact_mod_cast discr_ne_zero E
  have hdF : (discr F : ℝ) ≠ 0 := by exact_mod_cast discr_ne_zero F
  have hd : |(discr E : ℝ)| = |(discr F : ℝ)| ^ 2 := by
    have h1 := congrArg (Nat.cast : ℕ → ℤ) (FrameDual.natAbs_discr_sq (F := F) (E := E) hσ.2.2.1)
    rw [Nat.cast_pow, Int.natCast_natAbs, Int.natCast_natAbs] at h1
    rw [sq_abs]
    have h2 : ((|discr E| : ℤ) : ℝ) = ((|discr F| ^ 2 : ℤ) : ℝ) := by rw [h1]
    push_cast at h2
    rw [h2, sq_abs]
  set I := dInv E t * (dInv E t')⁻¹ with hIdef
  have hNI : ((FractionalIdeal.absNorm I : ℚ) : ℝ) = (|(discr E : ℝ)|⁻¹ ^ t) * (|(discr E : ℝ)|⁻¹ ^ t')⁻¹ := by
    rw [hIdef, map_mul, map_inv₀, Rat.cast_mul, Rat.cast_inv, FrameDual.absNorm_dInv, FrameDual.absNorm_dInv]
  have hI : I ≠ 0 := by
    intro h0
    have h1 : ((FractionalIdeal.absNorm I : ℚ) : ℝ) = 0 := by rw [h0, map_zero, Rat.cast_zero]
    rw [hNI] at h1
    have : |(discr E : ℝ)| ≠ 0 := abs_ne_zero.2 hdE
    simp_all
  obtain ⟨L₀, hL₀, hcov⟩ := HomCovolume.exists_idealLat E hE I hI
  have hc0 : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  let f : (InfinitePlace E → ℂ) →ₗ[ℝ] (InfinitePlace E → ℂ) :=
    LinearMap.pi fun w => (Algebra.lmul ℝ ℂ ((c : ℂ))⁻¹).comp (LinearMap.proj w)
  have hf : ∀ z w, f z w = ((c : ℂ))⁻¹ * z w := fun _ _ => rfl
  have hdet : LinearMap.det f = (∏ _w : InfinitePlace E, ‖(c : ℂ)‖ ^ 2)⁻¹ := by
    rw [LinearMap.det_pi, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [← Algebra.norm_apply, Algebra.norm_complex_apply, Complex.normSq_eq_norm_sq, norm_inv, inv_pow]
  have hpos : 0 < ∏ _w : InfinitePlace E, ‖(c : ℂ)‖ ^ 2 :=
    Finset.prod_pos fun v _ => pow_pos (norm_pos_iff.2 hc0) _
  let L : Submodule ℤ (InfinitePlace E → ℂ) := L₀.comap (f.restrictScalars ℤ)
  obtain ⟨_, _, h⟩ := HomCovolume.HasCov.of_det f (L := L) (by rw [hdet]; exact (inv_pos.2 hpos).ne')
    (fun _ => Iff.rfl) hcov
  have hL : ∀ z, z ∈ L ↔ z ∈ (ideLat I c : Set (InfinitePlace E → ℂ)) := by
    intro z
    change f z ∈ L₀ ↔ ∃ y ∈ I, ∀ w, z w = (c : ℂ) * w.embedding y
    rw [hL₀]
    refine exists_congr fun y => and_congr Iff.rfl ⟨fun h w => ?_, fun h w => ?_⟩
    · rw [← h w, hf, mul_inv_cancel_left₀ hc0]
    · rw [hf, h w, inv_mul_cancel_left₀ hc0]
  refine ⟨latticeDomain L, measurableSet_latticeDomain L, fun a => ?_, ?_⟩
  · obtain ⟨z, hz, hu'⟩ := existsUnique_add_mem_latticeDomain L a
    refine ⟨z, ⟨(hL z).1 z.2, hz⟩, ?_⟩
    rintro l ⟨hl, hl'⟩
    exact congrArg Subtype.val (hu' ⟨l, (hL l).2 hl⟩ hl')
  · rw [ZLattice.covolume_eq_measure_fundamentalDomain _ _
      (isAddFundamentalDomain_latticeDomain _ _), measureReal_def, hdet, abs_of_pos (inv_pos.2 hpos),
      div_inv_eq_mul] at h
    have hfin : volume (latticeDomain L) ≠ ⊤ := (ZSpan.fundamentalDomain_isBounded _).measure_lt_top.ne
    rw [← ENNReal.ofReal_toReal hfin, h]
    congr 1
    have hn : InfinitePlace.nrComplexPlaces E = Fintype.card (InfinitePlace E) := by
      rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, IsTotallyComplex.nrRealPlaces_eq_zero, zero_add]
    have hDpos : 0 < |(discr F : ℝ)| := abs_pos.2 hdF
    have hr : |(discr F : ℝ)| ^ (1 - 2 * (t : ℝ) + 2 * (t' : ℝ)) =
        |(discr F : ℝ)| ^ (1 + 2 * t') / |(discr F : ℝ)| ^ (2 * t) := by
      rw [show (1 - 2 * (t : ℝ) + 2 * (t' : ℝ)) = ((1 + 2 * t' : ℕ) : ℝ) - ((2 * t : ℕ) : ℝ) by push_cast; ring,
        Real.rpow_sub hDpos, Real.rpow_natCast, Real.rpow_natCast]
    rw [hNI, HomCovolume.vInv_pow E hE, hn, hd, Real.sqrt_sq hDpos.le, hr, Finset.prod_const, Finset.card_univ,
      Complex.norm_real, Real.norm_of_nonneg hc.le]
    generalize |(discr F : ℝ)| = D at hDpos
    generalize Fintype.card (InfinitePlace E) = n
    rw [inv_pow, inv_pow, inv_inv, ← pow_mul, ← pow_mul, ← pow_mul, pow_add, pow_one, div_eq_mul_inv]
    ring

end GlobalTheory.SnMass.VolN
end
end

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.covolume_inverseDifferentPow_div_lattice : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → Algebra.FormallyUnramified (𝓞 F) (𝓞 E) → ∀ (t t' : ℕ) (c : ℝ), 0 < c → HasDom volume (ideLat (dInv E t * (dInv E t')⁻¹) c : Set (InfinitePlace E → ℂ)) (ENNReal.ofReal ((2⁻¹ : ℝ) ^ Fintype.card (InfinitePlace E) * |(NumberField.discr F : ℝ)| ^ (1 - 2 * (t : ℝ) + 2 * (t' : ℝ)) * c ^ (2 * Fintype.card (InfinitePlace E)))) := by
  atlas_forward_decl GlobalTheory.SnMass.VolN.hasDom_ideLat_dInv_div
end

section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.covolume_inverseDifferentPow_mul_lattice : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → Algebra.FormallyUnramified (𝓞 F) (𝓞 E) → ∀ (t t' : ℕ) (c : ℝ), 0 < c → HasDom volume (ideLat (dInv E t * dInv E t') c : Set (InfinitePlace E → ℂ)) (ENNReal.ofReal ((2⁻¹ : ℝ) ^ Fintype.card (InfinitePlace E) * |(NumberField.discr F : ℝ)| ^ (1 - 2 * (t : ℝ) - 2 * (t' : ℝ)) * c ^ (2 * Fintype.card (InfinitePlace E)))) := by
  first | exact @GlobalTheory.SnMass.VolN.CovMul.hasDom_ideLat_dInv_mul | exact GlobalTheory.SnMass.VolN.CovMul.hasDom_ideLat_dInv_mul | (intros; apply GlobalTheory.SnMass.VolN.CovMul.hasDom_ideLat_dInv_mul <;> assumption)
end

section
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass
open scoped TensorProduct ENNReal nonZeroDivisors

namespace GlobalTheory.SnMass.VolN

theorem cM_one (k r : ℕ) (β : Bk r) : cM k r β (Matrix.of.symm 1) = 0 := by
  rcases β with p | a | p | a
  · show (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (eI k r p.1.1) (eI k r p.1.2) = 0
    exact Matrix.one_apply_ne (fun h => p.2.ne (by simpa [eI, Fin.ext_iff] using h))
  · funext j
    show (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (eI k r a) (wI k r j) = 0
    refine Matrix.one_apply_ne (fun h => ?_)
    have h' := congrArg Fin.val h
    simp only [eI, wI] at h'
    have := a.isLt
    omega
  · show (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (eI k r p.1.1) (esI k r p.1.2) = 0
    refine Matrix.one_apply_ne (fun h => ?_)
    have h' := congrArg Fin.val h
    simp only [eI, esI] at h'
    have := p.1.1.isLt
    have := p.1.2.isLt
    omega
  · show ((1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (eI k r a) (esI k r a)).im = 0
    rw [Matrix.one_apply]
    split_ifs <;> simp

theorem pos_le (k r : ℕ) (i : Fin (2 * r + k + 1)) : pos k r i ≤ 2 * r := by
  have := i.isLt
  unfold pos
  split_ifs <;> omega

theorem eq_one_of_dep {k r : ℕ} {x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (h : Dep k r (2 * r + 1) (x - 1)) : x = 1 := by
  refine sub_eq_zero.1 (Matrix.ext fun i j => ?_)
  exact h i j (by have := pos_le k r j; omega)

theorem countable_units (E : Type) [Field E] [NumberField E] (n : ℕ) :
    Countable (Matrix (Fin n) (Fin n) E)ˣ := by
  haveI : Countable E :=
    Function.Injective.countable (Module.finBasis ℚ E).equivFun.injective
  haveI : Countable (Matrix (Fin n) (Fin n) E) := inferInstanceAs (Countable (Fin n → Fin n → E))
  exact Function.Injective.countable (f := fun u : (Matrix (Fin n) (Fin n) E)ˣ => (u : Matrix (Fin n) (Fin n) E))
    Units.val_injective

theorem ofReal_five (t u h c g : ℝ) (ht : 0 ≤ t) (hu : 0 ≤ u) (hh : 0 ≤ h) (hc : 0 ≤ c) (hg : 0 ≤ g) :
    ENNReal.ofReal (t * (u * h * c * g)) =
      ENNReal.ofReal t * (ENNReal.ofReal u * ENNReal.ofReal h * ENNReal.ofReal c * ENNReal.ofReal g) := by
  rw [ENNReal.ofReal_mul ht, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_mul hu]

abbrev MM (k r : ℕ) (E : Type) := Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E

theorem covolume_N : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (k r : ℕ) (J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E) (Λ : Submodule (𝓞 E) (Fin (2 * r + k + 1) → E)) (P : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) E) (f : Matrix (Fin (2 * r + k + 1)) (Fin r) E) (T : F) (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (s : Fin r → ℝ), IsCMExt F E σ → Algebra.FormallyUnramified (𝓞 F) (𝓞 E) → IsHermND σ J → GlobalTheory.SgGlob.SelfDual (σ : E →+* E) J Λ → IsFrame (σ : E →+* E) J (algebraMap F E T) P → IsDual (σ : E →+* E) J P f → tupLat (id1 E r) (sideM P f) ≤ Λ → IsModelAt J A → (∀ a, 0 < s a) → Adapted A P f s → AllSome (IsDomN (σ : E →+* E) J Λ P A) fun 𝓓 => Measure.pi (fun _ : InfinitePlace E => haarLie (Nset k r) 1) 𝓓 = ENNReal.ofReal (|(NumberField.discr F : ℝ)| ^ (-(((k : ℝ) + 1) * (r : ℝ) ^ 2) - 4 * ((r : ℝ) ^ 3 - r) / 3 - 3 * (r : ℝ) / 2) * (∏ a : Fin r, s a ^ (4 * (r - (a : ℕ)) + 2 * k)) ^ Fintype.card (InfinitePlace E)) := by
  intro F E _ _ _ _ _ σ k r J Λ P f T A s h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  have hV : IsVolData σ J Λ P f T A s := ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  obtain ⟨⟨G, hG⟩, hGu⟩ := GlobalTheory.T.integralUnipotentRadical_forms_unit_subgroup F E σ k r J Λ P f T A s hV
  obtain ⟨ha1, ha2, ha3⟩ := GlobalTheory.T.unipotentModelAction_isAction_and_faithful F E σ k r J Λ P f T A s hV
  have hmem := GlobalTheory.T.integralUnipotent_mem_modelUnipotentAtPlace F E σ k r J Λ P f T A s hV
  choose DU hDUm hDUf hDUv using fun p : UTr r =>
    GlobalTheory.T.covolume_inverseDifferentPow_div_lattice F E σ h1 h2 (r - p.1.1.val) (r - p.1.2.val) (s p.1.1 / s p.1.2) (div_pos (h9 _) (h9 _))
  choose DC hDCm hDCf hDCv using fun p : UTr r =>
    GlobalTheory.T.covolume_inverseDifferentPow_mul_lattice F E σ h1 h2 (r - p.1.1.val) (r - p.1.2.val) (s p.1.1 * s p.1.2) (mul_pos (h9 _) (h9 _))
  choose DH hDHm hDHf hDHv using GlobalTheory.T.covolume_middleLattice_homLattice_ideal F E σ k r J Λ P f T A s hV
  choose DG hDGm hDGf hDGv using fun a : Fin r =>
    GlobalTheory.T.skewLattice_inverseDifferentPow_covolume F E σ h1 h2 (r - a.val) (s a ^ 2) (pow_pos (h9 _) 2)
  let LB := blkSet (InfinitePlace E) k r
    (fun p => (ideLat (dInv E (r - p.1.1.val) * (dInv E (r - p.1.2.val))⁻¹) (s p.1.1 / s p.1.2) : Set _))
    (fun a => homLat (σ : E →+* E) J Λ P f A (dInv E (r - a.val)) (s a))
    (fun p => (ideLat (dInv E (r - p.1.1.val) * dInv E (r - p.1.2.val)) (s p.1.1 * s p.1.2) : Set _))
    (fun a => (skewLat (σ : E →+* E) (dInv E (2 * (r - a.val))) (s a ^ 2) : Set _))
  let DB := blkSet (InfinitePlace E) k r DU DH DC DG
  let NN : Set (InfinitePlace E → Mt k r) := {x | ∀ w, Matrix.of (x w) ∈ Nset k r}
  let ρ : G → (InfinitePlace E → Mt k r) → (InfinitePlace E → Mt k r) :=
    fun g => actM A ((g : (MM k r E)ˣ) : MM k r E)
  let o : InfinitePlace E → Mt k r := fun _ => Matrix.of.symm 1
  let gm : G → InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ :=
    fun g => gM A ((g : (MM k r E)ˣ) : MM k r E)
  have hρo : ∀ g w, ρ g o w = Matrix.of.symm (gm g w) := fun g w => by
    show Matrix.of.symm (gm g w * 1) = Matrix.of.symm (gm g w)
    rw [mul_one]
  have hgm : ∀ g w, gm g w ∈ Nset k r := fun g => hmem _ ((hG _).1 g.2)
  have hρ1 : ∀ x, ρ 1 x = x := fun x => by
    have e : (((1 : G) : (MM k r E)ˣ) : MM k r E) = 1 := rfl
    show actM A (((1 : G) : (MM k r E)ˣ) : MM k r E) x = x
    rw [e]; exact ha1 x
  have hρm : ∀ g h x, ρ (g * h) x = ρ g (ρ h x) := fun g h x => by
    have e : (((g * h : G) : (MM k r E)ˣ) : MM k r E) = ((g : (MM k r E)ˣ) : MM k r E) * ((h : (MM k r E)ˣ) : MM k r E) := rfl
    show actM A (((g * h : G) : (MM k r E)ˣ) : MM k r E) x = _
    rw [e]; exact ha2 _ _ x
  have hρN : ∀ g, ∀ x ∈ NN, ρ g x ∈ NN := fun g x hx w =>
    PI.AmpOrbQuot.nset_mul (hgm g w) (hx w)
  have hdep : ∀ (g : G) (d : ℕ), (∀ β : Bk r, degB r β < d →
      (fun w => cM k r β (ρ g o w)) = 0) → ∀ w, Dep k r d (gm g w - 1) := fun g d hg w =>
    GlobalTheory.T.hasFlagDepthAtLeast_of_free_entries_vanish k r _ d (hgm g w) fun β hβ => by
      have := congrFun (hg β hβ) w
      rwa [hρo] at this
  have tw := GlobalTheory.T.existsUnique_layered_strictFundamentalDomain (V := fun β : Bk r => InfinitePlace E → VM k r β) ρ NN o (degB r)
    (fun β x w => cM k r β (x w)) LB DB (fun w => by simpa [o] using PI.AmpOrbQuot.nset_one) hρ1 hρm hρN
    (by
      rintro (p | a | p | a)
      · exact (ideLat _ _).zero_mem
      · exact ⟨0, ⟨fun a => by simp [form], fun c _ => by simp⟩, fun w l => by
          have e : (fun i => w.embedding ((0 : Fin (2 * r + k + 1) → E) i)) = 0 := by ext; simp
          rw [e, Matrix.mulVec_zero]
          simp [herm]
          rfl⟩
      · exact (ideLat _ _).zero_mem
      · exact (skewLat _ _ _).zero_mem)
    (by
      rintro (p | a | p | a) v
      · exact hDUf p v
      · exact hDHf a v
      · exact hDCf p v
      · exact hDGf a v)
    (fun β => funext fun w => cM_one k r β)
    (fun d g hg x hx β hβ => funext fun w => by
      have := GlobalTheory.T.unipotentBlockEntries_mul_of_hasFlagDepthAtLeast k r (gm g w) (Matrix.of (x w)) d (hdep g d hg w) (GlobalTheory.T.flagUnipotent_block_upper_unitriangular k r _ (hx w)) β hβ
      show cM k r β (ρ g x w) = cM k r β (x w) + cM k r β (ρ g o w)
      rw [hρo]
      exact this)
    (by
      intro g β hβ
      have hgN := (hG _).1 g.2
      have e : (fun w => cM k r β (ρ g o w)) = fun w => cM k r β (Matrix.of.symm (gm g w)) :=
        funext fun w => by rw [hρo]
      show (fun w => cM k r β (ρ g o w)) ∈ LB β
      rw [e]
      rcases β with p | a | p | a
      · exact GlobalTheory.T.integralUnipotent_entry_mem_inverseDifferentLattice F E σ k r J Λ P f T A s hV _ hgN p
      · exact GlobalTheory.T.integralUnipotent_middleRow_mem_homLattice F E σ k r J Λ P f T A s hV _ hgN a
      · exact GlobalTheory.T.integralUnipotent_corner_entry_mem_idealLattice F E σ k r J Λ P f T A s hV _ hgN p
      · exact GlobalTheory.T.integralUnipotent_antidiagonal_mem_skewLattice F E σ k r J Λ P f T A s hV _ hgN a fun w =>
          GlobalTheory.T.re_antidiagonal_entry_eq_zero_of_flagDepth k r _ a (hgm g w) (hdep g _ hβ w))
    (by
      have lift : ∀ (β : Bk r) (l : InfinitePlace E → VM k r β),
          (∃ γ ∈ GN (σ : E →+* E) J Λ P, (∀ w, cM k r β (Matrix.of.symm (gM A γ w)) = l w) ∧
            ∀ β' : Bk r, β' ≠ β → degB r β' ≤ degB r β → ∀ w, cM k r β' (Matrix.of.symm (gM A γ w)) = 0) →
          ∃ g : G, (fun w => cM k r β (ρ g o w)) = l ∧ ∀ β', β' ≠ β → degB r β' ≤ degB r β →
            (fun w => cM k r β' (ρ g o w)) = 0 := by
        rintro β l ⟨γ, hγ, hl, h0⟩
        obtain ⟨u, rfl⟩ := hGu γ hγ
        refine ⟨⟨u, (hG u).2 hγ⟩, funext fun w => ?_, fun β' h h' => funext fun w => ?_⟩
        · rw [hρo]; exact hl w
        · rw [hρo]; exact h0 β' h h' w
      rintro (p | a | p | a) l hl
      · exact lift _ _ (GlobalTheory.T.exists_integral_unipotent_lift_entry F E σ k r J Λ P f T A s hV p l hl)
      · exact lift _ _ (GlobalTheory.T.lift_row_middleSpace_integralPoint F E σ k r J Λ P f T A s hV a l hl)
      · exact lift _ _ (GlobalTheory.T.exists_integral_unipotent_lift_corner F E σ k r J Λ P f T A s hV p l hl)
      · exact lift _ _ (GlobalTheory.T.exists_integral_unipotent_lift_antidiagonal F E σ k r J Λ P f T A s hV a l hl))
    (fun g hg => by
      have h1' : ∀ w, gm g w = 1 := fun w => eq_one_of_dep (hdep g _ (fun β _ => hg β) w)
      exact Subtype.ext (Units.ext (ha3 _ h1')))
  obtain ⟨hNm, hN0⟩ := GlobalTheory.T.pi_unipotentModel_measurable_full_measure (InfinitePlace E) k r
  obtain ⟨hDm, hDv⟩ := GlobalTheory.T.measure_unipotent_tuples_free_entry_blocks (InfinitePlace E) k r DU DH DC DG hDUm hDHm hDCm hDGm
  set Dset : Set (InfinitePlace E → Mt k r) := {x | (∀ w, Matrix.of (x w) ∈ Nset k r) ∧
    ∀ β : Bk r, (fun w => cM k r β (x w)) ∈ blkSet (InfinitePlace E) k r DU DH DC DG β} with hDset
  have hstrict : ∀ x ∈ NN, ∃! g : G, ρ g x ∈ Dset := fun x hx => by
    obtain ⟨g, hg, hu⟩ := tw x hx
    exact ⟨g, ⟨hρN g x hx, hg⟩, fun g' hg' => hu g' hg'.2⟩
  have conv : ∀ S : Set (InfinitePlace E → Mt k r), (∀ x ∈ NN, ∃! g : G, ρ g x ∈ S) ↔
      ∀ x ∈ NN, ∃! γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E,
        (InN (σ : E →+* E) J P γ ∧ latMap γ Λ = Λ) ∧ actM A γ x ∈ S := fun S => by
    refine forall₂_congr fun x hx => ?_
    constructor
    · rintro ⟨g, hg, hu⟩
      refine ⟨_, ⟨(hG _).1 g.2, hg⟩, fun γ hγ => ?_⟩
      obtain ⟨u, rfl⟩ := hGu γ hγ.1
      exact congrArg (fun g : G => ((g : (MM k r E)ˣ) : MM k r E)) (hu ⟨u, (hG u).2 hγ.1⟩ hγ.2)
    · rintro ⟨γ, hγ, hu⟩
      obtain ⟨u, rfl⟩ := hGu γ hγ.1
      refine ⟨⟨u, (hG u).2 hγ.1⟩, hγ.2, fun g hg => ?_⟩
      exact Subtype.ext (Units.ext (hu _ ⟨(hG _).1 g.2, hg⟩))
  haveI : Countable G := by
    haveI := countable_units E (2 * r + k + 1)
    infer_instance
  refine ⟨⟨Dset, hDm, (conv Dset).1 hstrict⟩, fun 𝓓 h𝓓 => ?_⟩
  have hEq := GlobalTheory.T.strictFundamentalDomain_measure_eq (G := G) _ ρ NN 𝓓 Dset hNm hN0 h𝓓.1 hDm hρ1 hρm hρN
    (fun g => GlobalTheory.T.unipotentModelProductAction_measurePreserving E k r A _ (hgm g)) ((conv 𝓓).2 h𝓓.2) hstrict
  beta_reduce
  rw [hEq, hDv]
  simp only [hDUv, hDHv, hDCv, hDGv]
  have hd : 0 < |(NumberField.discr F : ℝ)| := abs_pos.2 (by exact_mod_cast NumberField.discr_ne_zero F)
  rw [← GlobalTheory.T.unipotentRadical_blockCovolumes_prod _ (Fintype.card (InfinitePlace E)) k r s hd h9]
  have nnU : ∀ p : UTr r, 0 ≤ (2⁻¹ : ℝ) ^ Fintype.card (InfinitePlace E) * |(NumberField.discr F : ℝ)| ^ (1 - 2 * ((r - p.1.1.val : ℕ) : ℝ) + 2 * ((r - p.1.2.val : ℕ) : ℝ)) * (s p.1.1 / s p.1.2) ^ (2 * Fintype.card (InfinitePlace E)) := fun p => by
    have := h9 p.1.1; have := h9 p.1.2; positivity
  have nnC : ∀ p : UTr r, 0 ≤ (2⁻¹ : ℝ) ^ Fintype.card (InfinitePlace E) * |(NumberField.discr F : ℝ)| ^ (1 - 2 * ((r - p.1.1.val : ℕ) : ℝ) - 2 * ((r - p.1.2.val : ℕ) : ℝ)) * (s p.1.1 * s p.1.2) ^ (2 * Fintype.card (InfinitePlace E)) := fun p => by
    have := h9 p.1.1; have := h9 p.1.2; positivity
  have nnH : ∀ a : Fin r, 0 ≤ ((2⁻¹ : ℝ) ^ Fintype.card (InfinitePlace E) * |(NumberField.discr F : ℝ)| ^ (1 - 2 * ((r - a.val : ℕ) : ℝ)) * s a ^ (2 * Fintype.card (InfinitePlace E))) ^ (k + 1) := fun a => by
    have := h9 a; positivity
  have nnG : ∀ a : Fin r, 0 ≤ |(NumberField.discr F : ℝ)| ^ (1 / 2 - 2 * ((r - a.val : ℕ) : ℝ)) * (s a ^ 2) ^ Fintype.card (InfinitePlace E) := fun a => by
    have := h9 a; positivity
  rw [← ENNReal.ofReal_prod_of_nonneg fun p _ => nnU p, ← ENNReal.ofReal_prod_of_nonneg fun a _ => nnH a,
    ← ENNReal.ofReal_prod_of_nonneg fun p _ => nnC p, ← ENNReal.ofReal_prod_of_nonneg fun a _ => nnG a,
    ofReal_five _ _ _ _ _ (by positivity) (Finset.prod_nonneg fun p _ => nnU p) (Finset.prod_nonneg fun a _ => nnH a)
      (Finset.prod_nonneg fun p _ => nnC p) (Finset.prod_nonneg fun a _ => nnG a),
    ENNReal.ofReal_pow (by norm_num)]
  simp

end GlobalTheory.SnMass.VolN
end
end

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass
open scoped TensorProduct ENNReal nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.covolume_integral_unipotentRadical_real_points : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (k r : ℕ) (J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E) (Λ : Submodule (𝓞 E) (Fin (2 * r + k + 1) → E)) (P : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) E) (f : Matrix (Fin (2 * r + k + 1)) (Fin r) E) (T : F) (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (s : Fin r → ℝ), IsCMExt F E σ → Algebra.FormallyUnramified (𝓞 F) (𝓞 E) → IsHermND σ J → GlobalTheory.SgGlob.SelfDual (σ : E →+* E) J Λ → IsFrame (σ : E →+* E) J (algebraMap F E T) P → IsDual (σ : E →+* E) J P f → tupLat (id1 E r) (sideM P f) ≤ Λ → IsModelAt J A → (∀ a, 0 < s a) → Adapted A P f s → AllSome (IsDomN (σ : E →+* E) J Λ P A) fun 𝓓 => Measure.pi (fun _ : InfinitePlace E => haarLie (Nset k r) 1) 𝓓 = ENNReal.ofReal (|(NumberField.discr F : ℝ)| ^ (-(((k : ℝ) + 1) * (r : ℝ) ^ 2) - 4 * ((r : ℝ) ^ 3 - r) / 3 - 3 * (r : ℝ) / 2) * (∏ a : Fin r, s a ^ (4 * (r - (a : ℕ)) + 2 * k)) ^ Fintype.card (InfinitePlace E)) := by
  atlas_forward_decl GlobalTheory.SnMass.VolN.covolume_N
end
