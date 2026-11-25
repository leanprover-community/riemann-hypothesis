module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittCoreEmbeddingPreservesSupportedUnitarySubgro
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIntegralBasisOfLatticeAtPlaceStable
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.MarkSpec
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIntegralTraceIdempotentAtTamePlace
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSelfDualLatticeAtPlaceComapUnitarySupported
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticeAtPlaceSplitsHyperbolicPlusCore
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticeHyperbolicLineIdealsAtPlace
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnfoldingBasePointFourierJacobiGroup
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerBF
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSelfDualLatticeAtPlaceLatticeCompletion
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticesSingleOrbitTamePlace
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.TypeStar
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentFourierJacobiGroupStructure
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittHyperbolicAnisotropicCommuteLevi

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFlagDualMatrix, Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFlagDualBasisSelfDualLatticeAtPlace, Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFlagDualBasisSelfDualLatticeAtPlaceStatement, Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIsotropicDualColumnsSelfDualLatticeAtPlace, Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsUnitarySupportedAtPlaceOfDualIsotropicFram, Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFlagStabiliserMoveLatticeSplitWitt, Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlagStabilizerEqUnipotentTorusLeviAtPlace, Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlagStabilizerEqUnipotentTorusLeviAtPlaceStatement, Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaDecompositionSelfDualWittSplitAtPlace

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFlagDualMatrix =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFlagDualMatrix", "h": "module\n\npublic import Mathlib.Algebra.Algebra.Basic\npublic import Mathlib.Data.Matrix.Mul\npublic import Mathlib.LinearAlgebra.BilinearMap\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.PiTensorProduct\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\nimport Std.Tactic.BVDecide.Normalize.Prop\npublic import Mathlib.Algebra.Group.Subgroup.Finite\npublic import Mathlib.LinearAlgebra.Matrix.ToLin\n\n"}
section -- clump:auto
@[expose] public section

namespace GlobalTheory.IwaFlag

variable {R V : Type} [CommRing R] [AddCommGroup V] [Module R V] {ρ : ℕ} {c : R →+* R} {ε : R} {O : AddSubgroup R}
  {h : V →ₗ[R] V →ₛₗ[c] R} {M : AddSubgroup V}

def Princ (ε : R) (O : AddSubgroup R) : Prop :=
  ∀ J : AddSubgroup R, (∀ a ∈ J, ε * a = a) → (∀ o ∈ O, ∀ a ∈ J, o * a ∈ J) → (∃ m : ℕ, 0 < m ∧ (m : R) * ε ∈ J) →
    (∃ N : ℕ, 0 < N ∧ ∀ a ∈ J, (N : R) * a ∈ O) → ∃ α ∈ J, ∃ α', ε * α' = α' ∧ α * α' = ε ∧ ∀ a ∈ J, α' * a ∈ O

theorem smul_mem_of_sd (hmul : ∀ a ∈ O, ∀ b ∈ O, a * b ∈ O) (hM₁ : ∀ y ∈ M, ε • y = y)
    (hM₂ : ∀ y, ε • y = y → (y ∈ M ↔ ∀ x ∈ M, h y x ∈ O)) {o : R} (ho : o ∈ O) {y : V} (hy : y ∈ M) : o • y ∈ M := by
  refine (hM₂ _ (by rw [smul_comm, hM₁ y hy])).2 fun x hx => ?_
  rw [map_smul, LinearMap.smul_apply, smul_eq_mul]
  exact hmul _ ho _ ((hM₂ y (hM₁ y hy)).1 hy x hx)

theorem exists_triangular (hεc : c ε = ε) (hmul : ∀ a ∈ O, ∀ b ∈ O, a * b ∈ O) (hP : Princ ε O)
    (hM₁ : ∀ y ∈ M, ε • y = y) (hM₂ : ∀ y, ε • y = y → (y ∈ M ↔ ∀ x ∈ M, h y x ∈ O))
    (X : (Fin ρ → R) →ₗ[R] V) (f : Fin ρ → V) (hXf : ∀ t k, h (X t) (f k) = t k) (N : ℕ) (hN : 0 < N)
    (he : ∀ k, X (Pi.single k ((N : R) * ε)) ∈ M) (hf : ∀ k, ((N : R) * ε) • f k ∈ M) (i : Fin ρ) :
    ∃ (b : Fin ρ → R) (α' : R), (∀ l, i < l → b l = 0) ∧ X b ∈ M ∧ ε * α' = α' ∧ b i * α' = ε ∧
      ∀ t : Fin ρ → R, (∀ l, i < l → t l = 0) → X t ∈ M → α' * t i ∈ O := by
  have hfix : ∀ t, X t ∈ M → ∀ k, ε * t k = t k := fun t ht k => by
    have := congrArg (fun z => h z (f k)) (hM₁ _ ht)
    simpa only [map_smul, LinearMap.smul_apply, smul_eq_mul, hXf] using this
  let J : AddSubgroup R :=
    { carrier := {a | ∃ t : Fin ρ → R, (∀ l, i < l → t l = 0) ∧ X t ∈ M ∧ t i = a}
      zero_mem' := ⟨0, fun _ _ => rfl, by rw [map_zero]; exact M.zero_mem, rfl⟩
      add_mem' := by
        rintro _ _ ⟨t, h1, h2, rfl⟩ ⟨s, g1, g2, rfl⟩
        exact ⟨t + s, fun l hl => by simp [h1 l hl, g1 l hl], by rw [map_add (f := _)]; exact M.add_mem h2 g2, rfl⟩
      neg_mem' := by
        rintro _ ⟨t, h1, h2, rfl⟩
        exact ⟨-t, fun l hl => by simp [h1 l hl], by rw [map_neg]; exact M.neg_mem h2, rfl⟩ }
  obtain ⟨α, ⟨b, hb1, hb2, rfl⟩, α', h1, h2, h3⟩ := hP J
    (by rintro _ ⟨t, -, h2, rfl⟩; exact hfix t h2 i)
    (by
      rintro o ho _ ⟨t, h1, h2, rfl⟩
      exact ⟨o • t, fun l hl => by simp [h1 l hl], by rw [map_smul]; exact smul_mem_of_sd hmul hM₁ hM₂ ho h2, rfl⟩)
    ⟨N, hN, Pi.single i ((N : R) * ε), fun l hl => Pi.single_eq_of_ne hl.ne' _, he i, Pi.single_eq_same _ _⟩
    ⟨N, hN, by
      rintro _ ⟨t, -, h2, rfl⟩
      have := (hM₂ _ (hM₁ _ h2)).1 h2 _ (hf i)
      rwa [map_smulₛₗ, hXf, map_mul, map_natCast, hεc, smul_eq_mul, mul_assoc, hfix t h2 i] at this⟩
  exact ⟨b, α', hb1, hb2, h1, h2, fun t ht1 ht2 => h3 _ ⟨t, ht1, ht2, rfl⟩⟩

theorem exists_step (hcc : ∀ a, c (c a) = a) (hεε : ε * ε = ε) (hεc : c ε = ε) (hεO : ε ∈ O) (hOε : ∀ a ∈ O, ε * a = a)
    (hmul : ∀ a ∈ O, ∀ b ∈ O, a * b ∈ O) (hcO : ∀ a ∈ O, c a ∈ O) (hP : Princ ε O)
    (hM₁ : ∀ y ∈ M, ε • y = y) (hM₂ : ∀ y, ε • y = y → (y ∈ M ↔ ∀ x ∈ M, h y x ∈ O))
    (X : (Fin ρ → R) →ₗ[R] V) (f : Fin ρ → V) (hXf : ∀ t k, h (X t) (f k) = t k) (N : ℕ) (hN : 0 < N)
    (he : ∀ k, X (Pi.single k ((N : R) * ε)) ∈ M) (hf : ∀ k, ((N : R) * ε) • f k ∈ M)
    (b : Fin ρ → Fin ρ → R) (hb₁ : ∀ i l, i < l → b i l = 0) (hb₂ : ∀ i, X (b i) ∈ M) (j : Fin ρ) (α' : R)
    (hα : b j j * α' = ε) (hJ : ∀ t : Fin ρ → R, (∀ l, j < l → t l = 0) → X t ∈ M → α' * t j ∈ O)
    (ih : ∀ z : Fin ρ → R, (∀ i, z i ∈ O) → ∃ y ∈ M, ∀ i, i < j → h (X (b i)) y = z i) :
    ∃ w ∈ M, (∀ i, i < j → h (X (b i)) w = 0) ∧ h (X (b j)) w = ε := by
  classical
  have hint : ∀ i, ∀ y ∈ M, h (X (b i)) y ∈ O := fun i => (hM₂ _ (hM₁ _ (hb₂ i))).1 (hb₂ i)
  have hsm : ∀ {o : R}, o ∈ O → ∀ {y : V}, y ∈ M → o • y ∈ M := fun ho _ hy => smul_mem_of_sd hmul hM₁ hM₂ ho hy
  let K : AddSubgroup R :=
    { carrier := {a | ∃ y ∈ M, (∀ i, i < j → h (X (b i)) y = 0) ∧ h (X (b j)) y = a}
      zero_mem' := ⟨0, M.zero_mem, fun _ _ => map_zero _, map_zero _⟩
      add_mem' := by
        rintro _ _ ⟨t, h1, h2, rfl⟩ ⟨s, g1, g2, rfl⟩
        exact ⟨t + s, M.add_mem h1 g1, fun l hl => by rw [map_add (f := _), h2 l hl, g2 l hl, add_zero], map_add _ _ _⟩
      neg_mem' := by
        rintro _ ⟨t, h1, h2, rfl⟩
        exact ⟨-t, M.neg_mem h1, fun l hl => by rw [map_neg, h2 l hl, neg_zero], map_neg _ _⟩ }
  have hKO : ∀ o ∈ O, ∀ a ∈ K, o * a ∈ K := by
    rintro o ho _ ⟨t, h1, h2, rfl⟩
    exact ⟨c o • t, hsm (hcO o ho) h1, fun l hl => by rw [map_smulₛₗ, h2 l hl, smul_zero],
      by rw [map_smulₛₗ, hcc, smul_eq_mul]⟩
  have hαN : α' * ((N : R) * ε) ∈ O := by
    have := hJ (Pi.single j ((N : R) * ε)) (fun l hl => Pi.single_eq_of_ne hl.ne' _) (he j)
    rwa [Pi.single_eq_same] at this
  have hNK : (N : R) * ε * b j j ∈ K :=
    ⟨_, hf j, fun i hi => by rw [map_smulₛₗ, hXf, hb₁ i j hi, smul_zero],
      by rw [map_smulₛₗ, hXf, map_mul, map_natCast, hεc, smul_eq_mul]⟩
  obtain ⟨β, hβ, β', h1, h2, h3⟩ := hP K
    (by rintro _ ⟨t, h1, -, rfl⟩; exact hOε _ (hint j t h1)) hKO
    ⟨N * N, Nat.mul_pos hN hN, by
      have e : ((N * N : ℕ) : R) * ε = α' * ((N : R) * ε) * ((N : R) * ε * b j j) := by
        push_cast
        linear_combination (-(N : R) * N * ε * ε) * hα - ((N : R) * N * (ε + 1)) * hεε
      rw [e]; exact hKO _ hαN _ hNK⟩
    ⟨1, one_pos, by rintro _ ⟨t, h1, -, rfl⟩; rw [Nat.cast_one, one_mul]; exact hint j t h1⟩
  choose g hg hg' using fun i : Fin ρ => ih (Pi.single i ε) fun l => by
    by_cases hl : l = i
    · rw [hl, Pi.single_eq_same]; exact hεO
    · rw [Pi.single_eq_of_ne hl]; exact O.zero_mem
  let s := Finset.univ.filter (· < j)
  let t : Fin ρ → R := β' • b j - ∑ i ∈ s, (β' * h (X (b j)) (g i)) • b i
  have hXt : X t = β' • X (b j) - ∑ i ∈ s, (β' * h (X (b j)) (g i)) • X (b i) := by

    simp only [t, map_sub, map_sum, map_smul]
  have htM : X t ∈ M := by
    refine (hM₂ _ ?_).2 fun y hy => ?_
    · rw [hXt, smul_sub, Finset.smul_sum, smul_smul, h1]
      congr 1
      exact Finset.sum_congr rfl fun i _ => by rw [smul_smul, ← mul_assoc, h1]
    · have hy' : y - ∑ i ∈ s, c (h (X (b i)) y) • g i ∈ M :=
        M.sub_mem hy (M.sum_mem fun i _ => hsm (hcO _ (hint i y hy)) (hg i))
      have hK : h (X (b j)) (y - ∑ i ∈ s, c (h (X (b i)) y) • g i) ∈ K := by
        refine ⟨_, hy', fun l hl => ?_, rfl⟩

        rw [map_sub, map_sum, Finset.sum_eq_single l]
        · rw [map_smulₛₗ, hcc, hg' l l hl, Pi.single_eq_same, smul_eq_mul, mul_comm, hOε _ (hint l y hy), sub_self]
        · intro i _ hi
          rw [map_smulₛₗ, hg' i l hl, Pi.single_eq_of_ne hi.symm, smul_zero]
        · intro hl'; exact absurd (by simpa [s] using hl) hl'
      have := h3 _ hK
      convert this using 1
      rw [hXt]

      simp only [map_sub, map_sum, map_smul, map_smulₛₗ, LinearMap.sub_apply, LinearMap.sum_apply,
      LinearMap.smul_apply, smul_eq_mul, hcc, mul_sub, Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun i _ => by ring
  have hz : ∀ l, j ≤ l → (∑ i ∈ s, (β' * h (X (b j)) (g i)) • b i) l = 0 := fun l hl => by
    rw [Finset.sum_apply]
    exact Finset.sum_eq_zero fun i hi => by
      rw [Pi.smul_apply, hb₁ i l (lt_of_lt_of_le (Finset.mem_filter.1 hi).2 hl), smul_zero]
  have hβ' : β' ∈ O := by
    have := hJ t (fun l hl => by
      simp only [t]
      rw [Pi.sub_apply, hz l hl.le, Pi.smul_apply, hb₁ j l hl, smul_zero, sub_zero]) htM
    simp only [t] at this
    rw [Pi.sub_apply, hz j le_rfl, Pi.smul_apply, sub_zero, smul_eq_mul] at this
    have e : α' * (β' * b j j) = β' := by linear_combination β' * hα + h1
    rwa [e] at this
  have := hKO _ hβ' _ hβ
  rw [mul_comm, h2] at this
  exact this

theorem exists_flag_dual (hcc : ∀ a, c (c a) = a) (hεε : ε * ε = ε) (hεc : c ε = ε) (hεO : ε ∈ O)
    (hOε : ∀ a ∈ O, ε * a = a) (hmul : ∀ a ∈ O, ∀ b ∈ O, a * b ∈ O) (hcO : ∀ a ∈ O, c a ∈ O) (hP : Princ ε O)
    (hM₁ : ∀ y ∈ M, ε • y = y) (hM₂ : ∀ y, ε • y = y → (y ∈ M ↔ ∀ x ∈ M, h y x ∈ O))
    (X : (Fin ρ → R) →ₗ[R] V) (f : Fin ρ → V) (hXf : ∀ t k, h (X t) (f k) = t k) (N : ℕ) (hN : 0 < N)
    (he : ∀ k, X (Pi.single k ((N : R) * ε)) ∈ M) (hf : ∀ k, ((N : R) * ε) • f k ∈ M) :
    ∃ b : Fin ρ → Fin ρ → R, (∀ i l, i < l → b i l = 0) ∧ (∀ i l, ε * b i l = b i l) ∧ (∀ i, X (b i) ∈ M) ∧
      ∃ y : Fin ρ → V, (∀ j, y j ∈ M) ∧ ∀ i j, h (X (b i)) (y j) = if i = j then ε else 0 := by
  classical
  choose b α' hb₁ hb₂ _ hα hJ using exists_triangular hεc hmul hP hM₁ hM₂ X f hXf N hN he hf
  have hint : ∀ i, ∀ y ∈ M, h (X (b i)) y ∈ O := fun i => (hM₂ _ (hM₁ _ (hb₂ i))).1 (hb₂ i)
  have key : ∀ n : ℕ, n ≤ ρ → ∀ z : Fin ρ → R, (∀ i, z i ∈ O) → ∃ y ∈ M, ∀ i : Fin ρ, i.1 < n → h (X (b i)) y = z i := by
    intro n
    induction n with
    | zero => exact fun _ z _ => ⟨0, M.zero_mem, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
    | succ n ih =>
      intro hn z hz
      let j : Fin ρ := ⟨n, hn⟩
      obtain ⟨w, hw, hw₁, hw₂⟩ := exists_step hcc hεε hεc hεO hOε hmul hcO hP hM₁ hM₂ X f hXf N hN he hf b hb₁ hb₂ j
        (α' j) (hα j) (hJ j) (ih (Nat.le_of_succ_le hn))
      obtain ⟨y, hy, hy'⟩ := ih (Nat.le_of_succ_le hn) z hz
      have ho : z j - h (X (b j)) y ∈ O := O.sub_mem (hz j) (hint j y hy)
      refine ⟨y + c (z j - h (X (b j)) y) • w, M.add_mem hy (smul_mem_of_sd hmul hM₁ hM₂ (hcO _ ho) hw), fun i hi => ?_⟩
      rw [map_add (f := _), map_smulₛₗ, hcc, smul_eq_mul]
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | hi
      · rw [hw₁ i hi, hy' i hi, mul_zero, add_zero]
      · have : i = j := Fin.ext hi
        rw [this, hw₂, mul_comm, hOε _ ho, add_sub_cancel]
  choose y hy hy' using fun j : Fin ρ => key ρ le_rfl (Pi.single j ε) fun l => by
    by_cases hl : l = j
    · rw [hl, Pi.single_eq_same]; exact hεO
    · rw [Pi.single_eq_of_ne hl]; exact O.zero_mem
  refine ⟨b, hb₁, fun i k => ?_, hb₂, y, hy, fun i j => ?_⟩
  · have := congrArg (fun z => h z (f k)) (hM₁ _ (hb₂ i))
    simpa only [map_smul, LinearMap.smul_apply, smul_eq_mul, hXf] using this
  · rw [hy' j i i.2, Pi.single_apply]

open Matrix in
def sesq (c : R →+* R) {n : ℕ} (G : Matrix (Fin n) (Fin n) R) : (Fin n → R) →ₗ[R] (Fin n → R) →ₛₗ[c] R :=
  LinearMap.mk₂'ₛₗ (RingHom.id R) c (fun x y => ∑ i, ∑ j, c (y i) * G i j * x j)
    (fun x x' y => by simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib])
    (fun a x y => by
      simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring)
    (fun x y y' => by simp only [Pi.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib])
    (fun a x y => by
      simp only [Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring)

open Matrix in
theorem sesq_col {n p q : ℕ} (G : Matrix (Fin n) (Fin n) R) (A : Matrix (Fin n) (Fin p) R) (B : Matrix (Fin n) (Fin q) R)
    (i : Fin p) (j : Fin q) : sesq c G (fun k => A k i) (fun k => B k j) = ((B.map c)ᵀ * (G * A)) j i := by
  simp only [sesq, LinearMap.mk₂'ₛₗ_apply, Matrix.mul_apply, transpose_apply, map_apply, Finset.mul_sum, mul_assoc]

open scoped Matrix in
open Matrix in
theorem exists_flag_dual_matrix {n : ℕ} {M : AddSubgroup (Fin n → R)} (G : Matrix (Fin n) (Fin n) R)
    (hcc : ∀ a, c (c a) = a) (hεε : ε * ε = ε) (hεc : c ε = ε) (hεO : ε ∈ O)
    (hOε : ∀ a ∈ O, ε * a = a) (hmul : ∀ a ∈ O, ∀ b ∈ O, a * b ∈ O) (hcO : ∀ a ∈ O, c a ∈ O) (hP : Princ ε O)
    (hM₁ : ∀ y ∈ M, ∀ i, ε * y i = y i)
    (hM₂ : ∀ y : Fin n → R, (∀ i, ε * y i = y i) → (y ∈ M ↔ ∀ x ∈ M, ∑ i, ∑ j, c (x i) * G i j * y j ∈ O))
    (E F : Matrix (Fin n) (Fin ρ) R) (hEF : (F.map c)ᵀ * (G * E) = 1) (N : ℕ) (hN : 0 < N)
    (he : ∀ k, (fun l => (N : R) * ε * E l k) ∈ M) (hf : ∀ k, (fun l => (N : R) * ε * F l k) ∈ M) :
    ∃ b : Matrix (Fin ρ) (Fin ρ) R, (∀ i j, j < i → b i j = 0) ∧ (∀ i j, ε * b i j = b i j) ∧
      (∀ i, (fun k => (E * b) k i) ∈ M) ∧ ∃ c' : Matrix (Fin n) (Fin ρ) R, (∀ i, (fun k => c' k i) ∈ M) ∧
        (c'.map c)ᵀ * (G * (E * b)) = ε • (1 : Matrix (Fin ρ) (Fin ρ) R) := by
  classical
  obtain ⟨b, h1, h2, h3, y, h4, h5⟩ := exists_flag_dual (h := sesq c G) (M := M) hcc hεε hεc hεO hOε hmul hcO hP
    (fun y hy => funext (hM₁ y hy)) (fun y hy => hM₂ y (congrFun hy)) E.mulVecLin (fun k l => F l k)
    (fun t k => by
      have := sesq_col (c := c) G (E * Matrix.of fun l (_ : Fin 1) => t l) F 0 k
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_assoc _ G, hEF, Matrix.one_mul] at this
      exact this) N hN
    (fun k => by
      convert he k using 1
      ext l
      simp [mul_comm]) hf
  refine ⟨Matrix.of fun i j => b j i, fun i j hij => h1 j i hij, fun i j => h2 j i, h3, Matrix.of fun k j => y j k, h4, ?_⟩
  ext j i
  rw [← sesq_col]
  refine (h5 i j).trans ?_
  by_cases hij : i = j
  · subst hij; simp
  · simp [hij, Matrix.one_apply_ne (Ne.symm hij)]

end GlobalTheory.IwaFlag
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFlagDualMatrix =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFlagDualBasisSelfDualLatticeAtPlace =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFlagDualBasisSelfDualLatticeAtPlace", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittCoreEmbeddingPreservesSupportedUnitarySubgro\npublic import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFlagDualMatrix\npublic import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIntegralBasisOfLatticeAtPlaceStable\nimport Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq\nimport Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators\nimport Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\nimport Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNatMulSelfDualLatticeAtPlaceIntegral\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix

namespace GlobalTheory.IwaFlag

variable {D : D7} {v : Pl D}

def intGrpAt (D : D7) (v : Pl D) : AddSubgroup (AE D) where
  carrier := intAt D (· = v)
  zero_mem' := ⟨zero_mem _, by rw [RingHom.map_zero]; exact zero_mem _⟩
  add_mem' := fun ha hb => ⟨add_mem ha.1 hb.1, by rw [RingHom.map_add (f := _)]; exact add_mem ha.2 hb.2⟩
  neg_mem' := fun ha => ⟨neg_mem ha.1, by rw [RingHom.map_neg]; exact neg_mem ha.2⟩

theorem mul_mem_intAt {a b : AE D} (ha : a ∈ intAt D (· = v)) (hb : b ∈ intAt D (· = v)) : a * b ∈ intAt D (· = v) :=
  ⟨Ideal.mul_mem_left _ _ hb.1, by rw [RingHom.map_mul]; exact FrameLat.mul_mem_intAE ha.2 hb.2⟩

theorem exists_nat_isIntegral_fin {ι : Type} [Fintype ι] (z : ι → D.host.E) :
    ∃ d : ℕ, 0 < d ∧ ∀ l, IsIntegral ℤ ((d : D.host.E) * z l) := by
  classical
  choose c hc hi using fun p : ι => GlobalTheory.IwaPlace.SDBound.exists_nat_mul_isIntegral (z p)
  refine ⟨∏ p, c p, Finset.prod_pos fun p _ => hc p, fun l => ?_⟩
  rw [← Finset.prod_erase_mul Finset.univ c (Finset.mem_univ l), Nat.cast_mul, mul_assoc]
  refine IsIntegral.mul ?_ (hi l)
  rw [← Int.cast_natCast]
  exact isIntegral_algebraMap (R := ℤ)

theorem mul_incA_mem {ε : AE D} (hεI : ε ∈ intAt D (· = v)) {o : D.host.E} (ho : IsIntegral ℤ o) :
    ε * incA D o ∈ intAt D (· = v) := by
  have h : finPart D (incA D o) ∈ intAE D :=
    AddSubgroup.subset_closure ⟨1, fun w => by rw [map_one]; exact one_mem _, ⟨o, ho⟩, rfl⟩
  exact ⟨Ideal.mul_mem_right _ _ hεI.1, by rw [RingHom.map_mul]; exact FrameLat.mul_mem_intAE hεI.2 h⟩

theorem princ_intGrpAt {ε : AE D} (hεε : ε * ε = ε) (hεc : cA D ε = ε) (hεI : ε ∈ intAt D (· = v))
    (hε : ∀ a, a ∈ idAt D (· = v) ↔ ε * a = a) (ht : Tame D v) : Princ ε (intGrpAt D v) := by
  rintro J h1 h2 ⟨m, hm, h3⟩ ⟨N, hN, h4⟩
  obtain ⟨β, β', g1, g2, g3, g4, g5⟩ := GlobalTheory.IwaPlace.FreeAt.exists_basis D 1 v ε (J.comap (Pi.evalAddMonoidHom (fun _ : Fin 1 => AE D) 0))
    ht hεε hεc hεI hε
    (fun y hy i => by rw [Subsingleton.elim i 0]; exact (hε _).2 (h1 _ hy))
    (fun a ha y hy => h2 a ha _ hy)
    ⟨m, hm, fun y hy => by
      have := h2 _ (hy 0) _ h3
      rw [mul_left_comm, mul_comm (y 0), (hε _).1 (hy 0).1] at this
      exact this⟩
    ⟨N, hN, fun y hy i => by rw [Subsingleton.elim i 0]; exact h4 _ hy⟩
  have e3 : β 0 0 * β' 0 0 = ε := by
    have := congrFun (congrFun g3 0) 0
    rwa [Matrix.mul_apply, Fin.sum_univ_one, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at this
  have ev : ∀ (a : AE D) (i : Fin 1), (β' *ᵥ fun _ => a) i = β' 0 0 * a := fun a i => by
    rw [Subsingleton.elim i 0, Matrix.mulVec, dotProduct, Fin.sum_univ_one]
  refine ⟨β 0 0, (g5 (fun _ => β 0 0) fun _ => g1 0 0).2 fun i => ?_, β' 0 0, (hε _).1 (g2 0 0), e3, fun a ha => ?_⟩
  · rw [ev, mul_comm, e3]; exact hεI
  · have := (g5 (fun _ => a) fun _ => (hε _).2 (h1 a ha)).1 ha 0
    rw [ev] at this
    exact this

end GlobalTheory.IwaFlag

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFlagDualBasisSelfDualLatticeAtPlace =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFlagDualBasisSelfDualLatticeAtPlaceStatement =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFlagDualBasisSelfDualLatticeAtPlaceStatement", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittCoreEmbeddingPreservesSupportedUnitarySubgro\npublic import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFlagDualBasisSelfDualLatticeAtPlace\nimport Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq\nimport Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix

theorem _root_.GlobalTheory.T.exists_flag_dual_basis_selfDualLatticeAtPlace : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (v : Pl D) (ε : AE D) (hεε : ε * ε = ε) (hεc : cA D ε = ε) (hεI : ε ∈ intAt D (· = v)) (hε : ∀ a, a ∈ idAt D (· = v) ↔ ε * a = a), Tame D v → ∀ M : AddSubgroup (Fin S.rank → AE D), IsSDAt S v M → ∃ b : Mx D ρ ρ, (∀ i j, j < i → b i j = 0) ∧ (∀ i j, b i j ∈ idAt D (· = v)) ∧ (∀ i, (fun k => (d.jX * b) k i) ∈ M) ∧ ∃ c' : Mx D S.rank ρ, (∀ i, (fun k => c' k i) ∈ M) ∧ adj c' * (gA S * (d.jX * b)) = ε • (1 : Mx D ρ ρ) := by
  intro D S S₀ ρ d v ε hεε hεc hεI hε ht M ⟨hsupp, ⟨m, hm, hmul⟩, hdual⟩
  obtain ⟨K, hK, hint⟩ := GlobalTheory.IwaFlag.exists_nat_isIntegral_fin
    (Sum.elim (fun p : Fin S.rank × Fin ρ => d.e p.1 p.2)
      (fun p : Fin S.rank × Fin ρ => d.e' p.1 p.2))
  have hcol (z : Fin S.rank → D.host.E) (hz : ∀ l, IsIntegral ℤ ((K : D.host.E) * z l)) :
      (fun l => ((m * K : ℕ) : AE D) * ε * incA D (z l)) ∈ M := by
    have hscale : (fun l => ((m * K : ℕ) : AE D) * ε * incA D (z l)) =
        (m : AE D) • fun l => ε * incA D ((K : D.host.E) * z l) := by
      funext l
      rw [Pi.smul_apply, smul_eq_mul, RingHom.map_mul, map_natCast, Nat.cast_mul]
      ring
    rw [hscale]
    exact hmul _ fun l => GlobalTheory.IwaFlag.mul_incA_mem hεI (hz l)
  have hflag := GlobalTheory.IwaFlag.exists_flag_dual_matrix
    (c := cA D) (O := GlobalTheory.IwaFlag.intGrpAt D v) (M := M) (gA S)
    cA_cA hεε hεc hεI (fun a ha => (hε a).1 ha.1)
    (fun _ ha _ hb => GlobalTheory.IwaFlag.mul_mem_intAt ha hb)
    (fun a ha => ⟨(hε _).2 (by rw [← hεc, ← RingHom.map_mul, (hε a).1 ha.1]),
      (FrameLat.cA_int_iff a).2 ha.2⟩)
    (GlobalTheory.IwaFlag.princ_intGrpAt hεε hεc hεI hε ht)
    (fun y hy i => (hε _).1 (hsupp y hy i))
    (fun y hy => hdual y fun i => (hε _).2 (hy i)) d.jX d.jY d.gram_YX (m * K) (Nat.mul_pos hm hK)
    (fun k => hcol (fun l => d.e l k) fun l => hint (Sum.inl (l, k)))
    (fun k => hcol (fun l => d.e' l k) fun l => hint (Sum.inr (l, k)))
  obtain ⟨b, h1, h2, h3, c', h4, h5⟩ := hflag
  exact ⟨b, h1, fun i j => (hε _).2 (h2 i j), h3, c', h4, h5⟩
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFlagDualBasisSelfDualLatticeAtPlaceStatement =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIsotropicDualColumnsSelfDualLatticeAtPlace =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIsotropicDualColumnsSelfDualLatticeAtPlace", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittCoreEmbeddingPreservesSupportedUnitarySubgro\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix
open scoped TensorProduct

namespace GlobalTheory.IwaPlace.DualIso

variable {D : D7}

theorem intAE_mul_mem' {x y : Af D.host.F ⊗[D.host.F] D.host.E} (hx : x ∈ intAE D) (hy : y ∈ intAE D) :
    x * y ∈ intAE D := by
  refine AddSubgroup.closure_induction₂ (p := fun x y _ _ => x * y ∈ intAE D) ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy
  · rintro _ _ ⟨a, ha, u, rfl⟩ ⟨b, hb, v, rfl⟩
    refine AddSubgroup.subset_closure ⟨a * b, fun w => ?_, u * v, ?_⟩
    · rw [map_mul]; exact mul_mem (ha w) (hb w)
    · rw [Algebra.TensorProduct.tmul_mul_tmul]; rfl
  · intro x _; rw [zero_mul]; exact zero_mem _
  · intro x _; rw [mul_zero]; exact zero_mem _
  · intro x y z _ _ _ h1 h2; rw [add_mul]; exact add_mem h1 h2
  · intro x y z _ _ _ h1 h2; rw [mul_add]; exact add_mem h1 h2
  · intro x y _ _ h; rw [neg_mul]; exact neg_mem h
  · intro x y _ _ h; rw [mul_neg]; exact neg_mem h

theorem intAt_mul_mem {v : Pl D} {a b : AE D} (ha : a ∈ intAt D (· = v)) (hb : b ∈ intAt D (· = v)) :
    a * b ∈ intAt D (· = v) :=
  ⟨Ideal.mul_mem_left _ _ hb.1, by rw [map_mul]; exact intAE_mul_mem' ha.2 hb.2⟩

theorem hermAt_smul_left (S : HSp D) (o : AE D) (y x : Fin S.rank → AE D) :
    hermAt S (o • y) x = o * hermAt S y x := by
  simp only [hermAt, Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem smul_mem_of_isSDAt {S : HSp D} {v : Pl D} {M : AddSubgroup (Fin S.rank → AE D)} (hM : IsSDAt S v M)
    {o : AE D} (ho : o ∈ intAt D (· = v)) {y : Fin S.rank → AE D} (hy : y ∈ M) : o • y ∈ M := by
  refine (hM.2.2 _ fun i => ?_).2 fun x hx => ?_
  · simp only [Pi.smul_apply, smul_eq_mul]; exact Ideal.mul_mem_left _ _ (hM.1 y hy i)
  · rw [hermAt_smul_left]; exact intAt_mul_mem ho ((hM.2.2 y (hM.1 y hy)).1 hy x hx)

end GlobalTheory.IwaPlace.DualIso

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIsotropicDualColumnsSelfDualLatticeAtPlace =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsUnitarySupportedAtPlaceOfDualIsotropicFram =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsUnitarySupportedAtPlaceOfDualIsotropicFram", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame\npublic import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittCoreEmbeddingPreservesSupportedUnitarySubgro\nimport Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Tactic.TypeStar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix

namespace GlobalTheory.IwaPlace.BuildQ

variable {D : D7}

theorem mulVec_colMul {m n k : ℕ} (M : Mx D m n) (X : Mx D n k) (i : Fin k) (a : AE D) :
    M *ᵥ colMul X i a = fun r => a * (M * X) r i := by
  funext r
  simp only [colMul, Matrix.mulVec, dotProduct, Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

theorem adj_diagonal {n : ℕ} (f : Fin n → AE D) :
    adj (Matrix.diagonal f) = Matrix.diagonal (fun i => cA D (f i)) := by
  ext i j; simp [adj, Matrix.diagonal_apply]; split_ifs <;> simp_all [eq_comm]

theorem mul_tail₃ {a m n p k : ℕ} {A : Mx D a m} {B : Mx D m n} {B' : Mx D n p} {C : Mx D a p}
    (h : A * (B * B') = C) (X : Mx D p k) :
    A * (B * (B' * X)) = C * X := by
  rw [← h]; simp only [Matrix.mul_assoc]

end GlobalTheory.IwaPlace.BuildQ

namespace GlobalTheory.IwaPlace.BuildQ

variable {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ)

theorem smul_eq_of_mem {P : Pl D → Prop} {ε : AE D} (hε : ∀ a, a ∈ idAt D P ↔ ε * a = a)
    {m n : ℕ} {x : Mx D m n} (hx : ∀ i j, x i j ∈ idAt D P) : ε • x = x := by
  ext i j; rw [Matrix.smul_apply, smul_eq_mul, (hε _).1 (hx i j)]

theorem one_sub_mul_self {ε : AE D} (hεε : ε * ε = ε) : (1 - ε) * ε = 0 := by
  rw [sub_mul, one_mul, hεε, sub_self]

theorem one_sub_sq {ε : AE D} (hεε : ε * ε = ε) : (1 - ε) * (1 - ε) = 1 - ε := by
  rw [mul_sub, mul_one, one_sub_mul_self hεε, sub_zero]

theorem diag_absorb {ε : AE D} {n : ℕ} {α : Fin n → AE D} (hαε : ∀ i, ε * α i = α i) :
    ε • Matrix.diagonal α = Matrix.diagonal α := by
  ext i j
  simp only [Matrix.smul_apply, Matrix.diagonal_apply, smul_eq_mul]
  split_ifs with h
  · exact hαε i
  · rw [mul_zero]

theorem diag_const {ε : AE D} {n : ℕ} {α β : Fin n → AE D} (hαβ : ∀ i, α i * β i = ε) :
    (Matrix.diagonal fun i => α i * β i) = ε • (1 : Mx D n n) := by
  have : (fun i => α i * β i) = fun _ => ε := funext hαβ
  rw [this]
  ext i j
  by_cases h : i = j
  · subst h; simp
  · simp [h]

end GlobalTheory.IwaPlace.BuildQ

namespace GlobalTheory.IwaPlace.BuildQ

variable {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ)

theorem smul_shift {ε : AE D} (hεε : ε * ε = ε) {m n : ℕ} {x : Mx D m n} (hx : ε • x = x) (y : Mx D m n) :
    ε • (x + (1 - ε) • y - y) = x + (1 - ε) • y - y := by
  have e : x + (1 - ε) • y - y = x - ε • y := by
    rw [sub_smul, one_smul]; abel
  rw [e, smul_sub, hx, smul_smul, hεε]

theorem scalar_X {R : Type*} [CommRing R] {ε a b x y : R} (ha : ε * a = a) (hab : a * b = ε) (hx : ε * x = x) :
    a * (x * b + (1 - ε) * y) = x := by
  linear_combination x * hab + hx - y * ha

end GlobalTheory.IwaPlace.BuildQ

open GlobalTheory.IwaPlace.BuildQ in

end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsUnitarySupportedAtPlaceOfDualIsotropicFram =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFlagStabiliserMoveLatticeSplitWitt =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFlagStabiliserMoveLatticeSplitWitt", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittCoreEmbeddingPreservesSupportedUnitarySubgro\npublic import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame\npublic import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua\npublic import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.MarkSpec\npublic import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFlagDualBasisSelfDualLatticeAtPlaceStatement\npublic import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIntegralTraceIdempotentAtTamePlace\npublic import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIsotropicDualColumnsSelfDualLatticeAtPlace\npublic import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsUnitarySupportedAtPlaceOfDualIsotropicFram\npublic import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSelfDualLatticeAtPlaceComapUnitarySupported\npublic import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticeAtPlaceSplitsHyperbolicPlusCore\npublic import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticeHyperbolicLineIdealsAtPlace\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix

noncomputable section

namespace GlobalTheory.IwaPlace

theorem iwasawa_flag_move : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (L : Lat S) (L₀ : Lat S₀) (v : Pl D), Tame D v → IsSDAt S v (latV S L (· = v)) → MonoAt d L L₀ v → ∀ h ∈ grpAt S (· = v), ∃ q ∈ grpAt S (· = v), (∃ a : Mx D ρ ρ, (∀ i j, j < i → a i j = 0) ∧ mt S q ⬝ d.jX = d.jX ⬝ a) ∧ ∃ Λ₀ : AddSubgroup (Fin S₀.rank → AE D), IsSDAt S₀ v Λ₀ ∧ ∀ z : Fin S.rank → AE D, (∀ i, z i ∈ idAt D (· = v)) → (mt S (h⁻¹ * q) *ᵥ z ∈ latV S L (· = v) ↔ (∀ i, colMul d.jX i ((d.pX *ᵥ z) i) ∈ latV S L (· = v)) ∧ (∀ i, colMul d.jY i ((d.pY *ᵥ z) i) ∈ latV S L (· = v)) ∧ d.p0 *ᵥ z ∈ Λ₀) := by
  intro D S S₀ ρ d L L₀ v hT hL hM h hh
  obtain ⟨⟨ε, hεε, hεc, hεI, hε, -⟩, -⟩ := _root_.GlobalTheory.FinPl.localComponents D (· = v)
  have hMsd := _root_.GlobalTheory.IwaPlace.SdComap.isSDAt_comap D S v h⁻¹ (inv_mem hh) _ hL
  set M := (latV S L (· = v)).comap (Matrix.mulVecLin (mt S h⁻¹)).toAddMonoidHom with hMdef
  obtain ⟨b, hbu, hbI, hbM, c', hc'M, hpair⟩ := GlobalTheory.T.exists_flag_dual_basis_selfDualLatticeAtPlace D S S₀ ρ d v ε hεε hεc hεI hε hT M hMsd
  obtain ⟨w, hw, hw1⟩ := _root_.GlobalTheory.IwaPlace.exists_trace_one_at_tame D v ε hεε hεc hεI hε hT
  obtain ⟨c'', hc''M, hpair', hiso⟩ := _root_.GlobalTheory.IwaPlace.DualIso.dual_isotropic D S S₀ ρ d v ε hεε hεc hεI hε M hMsd w hw hw1 b c' hbI hbM hc'M hpair
  obtain ⟨α, β, hα, hβ, hαβ, hX, hY⟩ := _root_.GlobalTheory.IwaIdeals.ideals_at_place D S S₀ ρ d L L₀ v ε hεε hεc hεI hε hL hM
  have hc''I : ∀ i j, c'' i j ∈ idAt D (· = v) := fun i j => hMsd.1 _ (hc''M j) i
  obtain ⟨q, hq, hqX, hqα, hqβ⟩ := _root_.GlobalTheory.IwaPlace.exists_grpAt_of_dual_frames D S S₀ ρ d v ε hεε hεc hεI hε α β b c'' hα hβ hαβ hbI hc''I hpair' hiso
  have hNsd := _root_.GlobalTheory.IwaPlace.SdComap.isSDAt_comap D S v q hq M hMsd
  obtain ⟨Λ₀, hΛ, hz⟩ := _root_.GlobalTheory.IwaDecomp.selfDual_split D S S₀ ρ d v ε hεε hεc hεI hε _ α β hNsd hα hβ hαβ
    (fun i => by
      rw [AddSubgroup.mem_comap]
      change mt S q *ᵥ colMul d.jX i (α i) ∈ M
      rw [hqα]; exact hbM i)
    (fun i => by
      rw [AddSubgroup.mem_comap]
      change mt S q *ᵥ colMul d.jY i (cA D (β i)) ∈ M
      rw [hqβ]; exact hc''M i)
  refine ⟨q, hq, ⟨b ⬝ Matrix.diagonal β + (1 - ε) • (1 : Mx D ρ ρ), fun i j hji => ?_, hqX⟩, Λ₀, hΛ, fun z hz' => ?_⟩
  · rw [Matrix.add_apply, Matrix.mul_diagonal, hbu i j hji, Matrix.smul_apply, Matrix.one_apply_ne (ne_of_gt hji)]
    simp
  · have e1 : (mt S (h⁻¹ * q) *ᵥ z ∈ latV S L (· = v)) ↔
        z ∈ (M.comap (Matrix.mulVecLin (mt S q)).toAddMonoidHom) := by
      rw [AddSubgroup.mem_comap, hMdef, AddSubgroup.mem_comap]
      change _ ↔ mt S h⁻¹ *ᵥ (mt S q *ᵥ z) ∈ _
      rw [Matrix.mulVec_mulVec, ← mt_mul]
    rw [e1, hz z hz']
    refine and_congr (forall_congr' fun i => (hX i _ (mulVec_mem_idAt _ hz' i)).symm)
      (and_congr (forall_congr' fun i => (hY i _ (mulVec_mem_idAt _ hz' i)).symm) Iff.rfl)

end GlobalTheory.IwaPlace

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFlagStabiliserMoveLatticeSplitWitt =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlagStabilizerEqUnipotentTorusLeviAtPlace =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlagStabilizerEqUnipotentTorusLeviAtPlace", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame\npublic import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua\npublic import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.MarkSpec\npublic import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnfoldingBasePointFourierJacobiGroup\npublic import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittCoreEmbeddingPreservesSupportedUnitarySubgro\npublic import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerBF\nimport Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentFourierJacobiGroupStructure\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\nimport Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittLeviTransvectionMemCompactAtPlace\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IwaFlag

variable {D : D7}

theorem mul_left_mem {R : Type} [CommRing R] {I : Ideal R} {l m k : ℕ} (A : Matrix (Fin l) (Fin m) R)
    {M : Matrix (Fin m) (Fin k) R} (h : ∀ i j, M i j ∈ I) (i : Fin l) (j : Fin k) : (A * M) i j ∈ I := by
  rw [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun x _ => Ideal.mul_mem_left _ _ (h x j)

theorem mul_right_mem {R : Type} [CommRing R] {I : Ideal R} {l m k : ℕ} {M : Matrix (Fin l) (Fin m) R}
    (B : Matrix (Fin m) (Fin k) R) (h : ∀ i j, M i j ∈ I) (i : Fin l) (j : Fin k) : (M * B) i j ∈ I := by
  rw [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun x _ => Ideal.mul_mem_right _ _ (h i x)

end GlobalTheory.IwaFlag

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlagStabilizerEqUnipotentTorusLeviAtPlace =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaDecompositionSelfDualWittSplitAtPlace =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaDecompositionSelfDualWittSplitAtPlace", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame\npublic import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittCoreEmbeddingPreservesSupportedUnitarySubgro\npublic import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFlagStabiliserMoveLatticeSplitWitt\npublic import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlagStabilizerEqUnipotentTorusLeviAtPlaceStatement\npublic import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSelfDualLatticeAtPlaceLatticeCompletion\npublic import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticesSingleOrbitTamePlace\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix

noncomputable section

namespace GlobalTheory.IwaPlace

variable {D : D7}

theorem flag_times_stab : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (L : Lat S) (L₀ : Lat S₀) (v : Pl D), Tame D v → IsSelfDualC S L → IsSelfDualC S₀ L₀ → MonoAt d L L₀ v → ∀ h ∈ grpAt S (· = v), ∃ p ∈ grpAt S (· = v), (∃ a : Mx D ρ ρ, (∀ i j, j < i → a i j = 0) ∧ mt S p ⬝ d.jX = d.jX ⬝ a) ∧ Moves S (p⁻¹ * h) L L (· = v) := by
  intro D S S₀ ρ d L L₀ v hT hL hL₀ hM h hh
  obtain ⟨q, hq, ⟨a, ha, hqa⟩, Λ₀, hΛ, hz⟩ := _root_.GlobalTheory.IwaPlace.iwasawa_flag_move D S S₀ ρ d L L₀ v hT (_root_.GlobalTheory.IwaPlace.LocSD.isSDAt_latV D S L v hL) hM h hh
  obtain ⟨γ, hγ, hγL⟩ := _root_.GlobalTheory.IwaOrbit.selfDual_orbit D S₀ v _ Λ₀ hT (_root_.GlobalTheory.IwaPlace.LocSD.isSDAt_latV D S₀ L₀ v hL₀) hΛ
  refine ⟨q * d.emb0 γ, mul_mem hq (wittCoreEmbedding_preserves_supportedUnitarySubgroup d hγ), ⟨a, ha, ?_⟩, ?_⟩
  · rw [mt_mul, Matrix.mul_assoc, d.wittDecomp_anisotropicEmbedding_inclX, hqa]
  · intro y hy
    obtain ⟨z, hzdef⟩ : ∃ z, z = mt S ((q * d.emb0 γ)⁻¹ * h) *ᵥ y := ⟨_, rfl⟩
    rw [← hzdef]
    have hzI : ∀ i, z i ∈ idAt D (· = v) := by rw [hzdef]; exact mulVec_mem_idAt _ hy
    have hw : y = mt S (h⁻¹ * q) *ᵥ (mt S (d.emb0 γ) *ᵥ z) := by
      rw [hzdef, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← mt_mul, ← mt_mul]
      have : h⁻¹ * q * d.emb0 γ * ((q * d.emb0 γ)⁻¹ * h) = 1 := by group
      rw [this, mt_one, Matrix.one_mulVec]
    have key := hz (mt S (d.emb0 γ) *ᵥ z) (mulVec_mem_idAt _ hzI)
    rw [← hw] at key
    rw [key, hM z, Matrix.mulVec_mulVec, d.wittDecomp_projX_anisotropicEmbedding, Matrix.mulVec_mulVec, d.wittDecomp_projY_anisotropicEmbedding, Matrix.mulVec_mulVec, d.wittDecomp_projAnisotropic_anisotropicEmbedding,
      ← Matrix.mulVec_mulVec, ← hγL _ (mulVec_mem_idAt _ hzI)]

theorem iwasawa_at_place : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (L : Lat S) (L₀ : Lat S₀) (v : Pl D), Tame D v → IsSelfDualC S L → IsSelfDualC S₀ L₀ → MonoAt d L L₀ v → ∀ h ∈ grpAt S (· = v), ∃ n ∈ flagN d, n ∈ grpAt S (· = v) ∧ ∃ t : GL (Fin ρ) (AE D), (∀ i j, i ≠ j → t.1 i j = 0) ∧ d.levi t ∈ grpAt S (· = v) ∧ ∃ γ ∈ grpAt S₀ (· = v), ∃ κ, InK S L (· = v) κ ∧ h = n * d.levi t * d.emb0 γ * κ := by
  intro D S S₀ ρ d L L₀ v hT hL hL₀ hM h hh
  obtain ⟨p, hp, hflag, hmv⟩ := flag_times_stab D S S₀ ρ d L L₀ v hT hL hL₀ hM h hh
  obtain ⟨n, hn, hnv, t, ht, htv, γ, hγ, hpe⟩ := GlobalTheory.IwaFlag.flag_stab D S S₀ ρ d v p hp hflag
  refine ⟨n, hn, hnv, t, ht, htv, γ, hγ, p⁻¹ * h, ⟨mul_mem (inv_mem hp) hh, hmv⟩, ?_⟩
  rw [← hpe]; group

end GlobalTheory.IwaPlace

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaDecompositionSelfDualWittSplitAtPlace =====
