module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeckeCharacterRestriction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharacterOfIdeleClass
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharExponentOfInfinityType
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ClozelCohomologicalModel
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocallyConstantOrbit
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIdempotentElemCharIdem
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSphericalFactorOfSphericalSubquotient
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterSphericalProductSpehQuotients
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEquivDetCharacterOfIrreducibleRankLeOne
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.NotIsTemperedGLDetRepTwo
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteUnitaryClassSetFinite
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvenCardOfNotLone
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFixedIff
import Formalism.LocalRingCardinality.SpanPowerMembership.LocAtA
import Mathlib.Tactic.Linter.Style
import Std.Tactic.BVDecide.Normalize.Prop

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateSymplecticCharacterExists, Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologicalLocalComponentExponents

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateSymplecticCharacterExists =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateSymplecticCharacterExists", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd\npublic import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt\npublic import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeckeCharacterRestriction\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharacterOfIdeleClass\nimport Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt\nimport Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteUnitaryClassSetFinite\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharExponentOfInfinityType\nimport Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvenCardOfNotLone\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Connected.Separation\nimport Mathlib.Topology.MetricSpace.Ultra.TotallySeparated\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.CuspRep

noncomputable section

end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateSymplecticCharacterExists =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologicalLocalComponentExponents =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologicalLocalComponentExponents", "h": "module\n\npublic import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ClozelCohomologicalModel\npublic import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocallyConstantOrbit\npublic import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU\npublic import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateSymplecticCharacterExists\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIdempotentElemCharIdem\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSphericalFactorOfSphericalSubquotient\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterSphericalProductSpehQuotients\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed\npublic import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEquivDetCharacterOfIrreducibleRankLeOne\npublic import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.NotIsTemperedGLDetRepTwo\nimport Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFixedIff\nimport Formalism.LocalRingCardinality.SpanPowerMembership.LocAtA\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\nimport Std.Tactic.BVDecide.Normalize.Prop\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

namespace GlobalTheory.TempSat

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.GenericUnitary ValuativeRel Matrix

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)]
  [Fintype n] [DecidableEq n] {W Y : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup Y] [Module ℂ Y]

def RowMax (L j₀ : n) (x : GL n k) : Prop := ∀ j, valuation k (x.val L j) ≤ valuation k (x.val L j₀)

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem RowMax.ne_zero {L j₀ : n} {x : GL n k} (h : RowMax L j₀ x) : valuation k (x.val L j₀) ≠ 0 := fun h0 => by
  have h1 : ∀ j, x.val L j = 0 := fun j => by simpa [h0] using h j
  have h2 := congrFun (congrFun x.mul_inv L) L
  simp [Matrix.mul_apply, h1] at h2

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem rowMax_left {L j₀ : n} {p : GL n k} (hp : ∀ i, i ≠ L → p.val L i = 0) (x : GL n k) :
    RowMax L j₀ (p * x) ↔ RowMax L j₀ x := by
  have e : ∀ (y : Matrix n n k) j, (p.val * y) L j = p.val L L * y L j := fun y j => by
    rw [Matrix.mul_apply, Finset.sum_eq_single L (fun i _ hi => by rw [hp i hi, zero_mul]) (by simp)]
  have h0 : valuation k (p.val L L) ≠ 0 := fun h0 => by
    have h2 := congrFun (congrFun p.mul_inv L) L
    rw [e, (Valuation.zero_iff _).1 h0] at h2
    simp at h2
  simp only [RowMax, Units.val_mul, e, map_mul]
  exact forall_congr' fun j => mul_le_mul_iff_right₀ (zero_lt_iff.2 h0)

theorem RowMax.right {L j₀ : n} {x g : GL n k} (h : RowMax L j₀ x) (hg : g ∈ KOne k n) : RowMax L j₀ (x * g) := by
  have hM := StepData.mem_KOne.1 hg
  have e : ∀ j, (x * g).val L j = x.val L j + ∑ i, x.val L i * (g.val - 1) i j := fun j => by
    rw [← Matrix.mul_apply, Matrix.mul_sub, Matrix.mul_one]; simp
  have h1 : ∀ j, valuation k (∑ i, x.val L i * (g.val - 1) i j) < valuation k (x.val L j₀) := fun j =>
    Valuation.map_sum_lt _ h.ne_zero fun i _ => by
      rw [map_mul]
      exact (mul_le_mul_left (h i) _).trans_lt (mul_lt_of_lt_one_right (zero_lt_iff.2 h.ne_zero) (hM i j))
  intro j
  rw [e, e, Valuation.map_add_eq_of_lt_left _ (h1 j₀)]
  exact Valuation.map_add_le _ (h j) (h1 j).le

theorem map_eq_zero_of_equivariant (e : (Σ a, m a) ≃ n) {ρ : Representation ℂ (Levi k m) W} {L j₀ : n} (hne : j₀ ≠ L)
    (hL : ∀ p ∈ parab k e, ∀ i, i ≠ L → p.val L i = 0) (ξ : GL n k →* ℂˣ) (hξ : ∀ g ∈ KO k n, ξ g = 1)
    (f₀ : IndSp e ρ) (hf₀ : ∀ g, parInd e ρ g f₀ = (ξ g : ℂ) • f₀)
    (l : IndSp e ρ →ₗ[ℂ] Y) (hl : ∀ g f, l (parInd e ρ g f) = (ξ g : ℂ) • l f) : l f₀ = 0 := by
  classical
  have h0 : ∀ x g, f₀.1.1 (x * g) = (ξ g : ℂ) • f₀.1.1 x := fun x g =>
    congrArg (fun f : IndSp e ρ => f.1.1 x) (hf₀ g)
  have hfix : f₀ ∈ fixed (parInd e ρ) (KO k n) := IwahoriInj.mem_fixed.2 fun g hg => by
    rw [hf₀, hξ g hg, Units.val_one, one_smul]
  by_cases ht : f₀.1.1 1 = 0
  · rw [SatInd.eq_zero_of_apply_one e hfix ht, map_zero]
  let fA : IndSp e ρ := ⟨⟨fun x => if RowMax L j₀ x then f₀.1.1 x else 0, fun p x => by
      simp only [rowMax_left (hL p p.2)]
      split_ifs
      · exact f₀.1.2 p x
      · exact (map_zero _).symm⟩,
    mem_smoothPart_of_nhds (Filter.mem_of_superset (StepData.isOpen_KOne.mem_nhds (one_mem _)) fun g hg => by
      refine Subtype.ext (funext fun x => ?_)
      show (if RowMax L j₀ (x * g) then f₀.1.1 (x * g) else 0) = if RowMax L j₀ x then f₀.1.1 x else 0
      have hi : RowMax L j₀ (x * g) ↔ RowMax L j₀ x :=
        ⟨fun h => by simpa using h.right (inv_mem hg), fun h => h.right hg⟩
      simp only [hi, h0, hξ g (StepData.KOne_le_KO hg), Units.val_one, one_smul])⟩
  obtain ⟨ϖ, hϖ⟩ := exists_uniformizer k
  have hϖ1 : valuation k (ϖ : k) < 1 := hϖ ▸ uniformizer_lt_one
  let s : GL n k := diagT k n (Pi.mulSingle j₀ ϖ)
  have hs : ∀ (x : GL n k) j, (x * s).val L j = x.val L j * ((Pi.mulSingle j₀ ϖ : n → kˣ) j : k) := fun x j => by
    rw [Units.val_mul, val_diagT, Matrix.mul_diagonal]
  have hsA : ∀ x, RowMax L j₀ (x * s) → RowMax L j₀ x := fun x h j => by
    by_cases hj : j = j₀
    · rw [hj]
    · have := h j
      rw [hs, hs, Pi.mulSingle_eq_of_ne hj, Pi.mulSingle_eq_same, Units.val_one, mul_one, map_mul] at this
      exact this.trans (mul_le_of_le_one_right' hϖ1.le)
  let v : IndSp e ρ := fA - (((ξ s)⁻¹ : ℂˣ) : ℂ) • parInd e ρ s fA
  have hlv : l v = 0 := by
    simp only [v, map_sub, map_smul, hl, smul_smul, Units.inv_mul, one_smul, sub_self]
  have hv : ∀ x, v.1.1 x = if RowMax L j₀ x ∧ ¬ RowMax L j₀ (x * s) then f₀.1.1 x else 0 := fun x => by
    show (if RowMax L j₀ x then f₀.1.1 x else 0) -
      (((ξ s)⁻¹ : ℂˣ) : ℂ) • (if RowMax L j₀ (x * s) then f₀.1.1 (x * s) else 0) = _
    by_cases h2 : RowMax L j₀ (x * s)
    · simp [h2, hsA x h2, h0, smul_smul]
    · simp [h2]
  have hK : ∀ g ∈ KO k n, f₀.1.1 g = f₀.1.1 1 := fun g hg => by
    simpa [hξ g hg] using h0 1 g
  obtain ⟨S, hS, hF⟩ := IwahoriInj.exists_orbit (isSmooth_parInd e ρ) (SplitFlip.isCompact_KO (k := k) (n := n)) v
  let c : IndSp e ρ → ℕ := fun u => if u.1.1 1 = 0 then 0 else 1
  have hc : ∀ u ∈ S, u.1.1 1 = (c u : ℂ) • f₀.1.1 1 := fun u hu => by
    obtain ⟨g, hg, rfl⟩ := (hS u).1 hu
    simp only [c, parInd_apply, one_mul, hv, hK g hg]
    split_ifs <;> simp_all
  let g₀ : GL n k := IwahoriInj.elem hne.symm 1
  have hint : ∀ y : k, valuation k y ≤ 1 → StepData.IntM (Matrix.transvection L j₀ y) := fun y hy =>
    StepData.intM_one.add fun i j => by
      rw [Matrix.single_apply]
      split_ifs
      exacts [hy, zero_mem _]
  have hg₀ : g₀ ∈ KO k n := StepData.mem_KO.2 ⟨hint 1 (by simp), hint (-1) (by simp)⟩
  have hg₁ : ∀ j, g₀.val L j = if j = L ∨ j = j₀ then 1 else 0 := fun j => by
    show Matrix.transvection L j₀ (1 : k) L j = _
    rw [Matrix.transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
    by_cases a : j = L
    · simp [a, hne]
    · by_cases b : j = j₀
      · simp [b, hne.symm]
      · simp [a, b, Ne.symm a, Ne.symm b]
  have hc₀ : c (parInd e ρ g₀ v) = 1 := by
    have a1 : RowMax L j₀ g₀ := fun j => by
      rw [hg₁, hg₁ j₀, if_pos (Or.inr rfl)]
      split_ifs <;> simp
    have a2 : ¬ RowMax L j₀ (g₀ * s) := fun h => by
      have := h L
      rw [hs, hs, hg₁, hg₁, if_pos (Or.inl rfl), if_pos (Or.inr rfl), Pi.mulSingle_eq_of_ne hne.symm,
        Pi.mulSingle_eq_same] at this
      exact hϖ1.not_ge (by simpa using this)
    simp only [c, parInd_apply, one_mul, hv, hK g₀ hg₀, a1, a2, not_false_eq_true, and_self, if_true, if_neg ht]
  have hN : 0 < ∑ u ∈ S, c u :=
    Finset.sum_pos' (fun _ _ => Nat.zero_le _) ⟨_, (hS _).2 ⟨g₀, hg₀, rfl⟩, by rw [hc₀]; exact one_pos⟩
  have hF2 : ∑ u ∈ S, u = ((∑ u ∈ S, c u : ℕ) : ℂ) • f₀ := by
    refine sub_eq_zero.1 (SatInd.eq_zero_of_apply_one e (sub_mem hF (Submodule.smul_mem _ _ hfix)) ?_)
    let ev : IndSp e ρ →ₗ[ℂ] W := ⟨⟨fun f => f.1.1 1, fun _ _ => rfl⟩, fun _ _ => rfl⟩
    show ev (∑ u ∈ S, u - ((∑ u ∈ S, c u : ℕ) : ℂ) • f₀) = 0

    rw [map_sub, map_sum, map_smul, Nat.cast_sum, Finset.sum_smul, sub_eq_zero]
    exact Finset.sum_congr rfl hc
  have h3 := congrArg l hF2

  rw [map_sum, map_smul, Finset.sum_eq_zero fun u hu => by
  obtain ⟨g, -, rfl⟩ := (hS u).1 hu
  rw [hl, hlv, smul_zero]] at h3
  exact (smul_eq_zero.1 h3.symm).resolve_left (by exact_mod_cast hN.ne')

theorem deg_eq_one_of_isCusp (x : IrrGL (k := k)) (hx : x.IsCusp) (hs : IsSpherical x.rep) : x.1 = 1 := by
  by_contra hne
  have h2 : 2 ≤ x.1 := by have := hx.1; omega
  let e : (Σ _ : Fin x.1, Fin 1) ≃ Fin x.1 := Equiv.sigmaUnique _ _
  have hij : (⟨0, by omega⟩ : Fin x.1) ≠ ⟨1, by omega⟩ := by simp
  have hb : unipRad k e ≠ ⊥ := fun h => by
    have h1 : IwahoriInj.elem hij (1 : k) ∈ unipRad k e := mem_unipRad.2 ⟨fun i j (hji : j < i) => by
      show Matrix.transvection _ _ (1 : k) i j = 0
      rw [Matrix.transvection, Matrix.add_apply, Matrix.one_apply_ne hji.ne', Matrix.single_apply_of_ne, add_zero]
      rintro ⟨rfl, rfl⟩
      simp at hji, fun a i j => by
      show Matrix.transvection _ _ (1 : k) a a = _
      rw [Matrix.transvection, Matrix.add_apply, Matrix.one_apply_eq, Matrix.single_apply_of_ne, add_zero,
        Subsingleton.elim i j, Matrix.one_apply_eq]
      rintro ⟨rfl, h⟩
      exact hij h.symm⟩
    rw [h, Subgroup.mem_bot] at h1
    have h3 := congrArg (fun g : GL (Fin x.1) k => g.val ⟨0, by omega⟩ ⟨1, by omega⟩) h1
    simp [IwahoriInj.elem, Matrix.transvection] at h3
  have hle : unipRad k e ≤ unipB k (Fin x.1) := fun g hg =>
    (mem_unipB k).2 ⟨(mem_unipRad.1 hg).1, fun i => ((mem_unipRad.1 hg).2 i 0 0).trans (Matrix.one_apply_eq _)⟩
  have htop := Submodule.Quotient.subsingleton_iff.1 (hx.2.2 _ _ e hb)
  obtain ⟨v, hv, h0⟩ := (Submodule.ne_bot_iff _).1 hs
  have hI : v ∈ fixed x.rep (iwahori k (Fin x.1)) := fun h => hv ⟨h.1, iwahori_le_KO k _ h.2⟩
  have h3 : iwahoriProj x.rep ⟨v, hI⟩ = 0 := Subtype.ext ((Submodule.Quotient.mk_eq_zero _).2
    (IwahoriInj.twKer_mono hle (htop ▸ Submodule.mem_top)))
  exact h0 (congrArg Subtype.val ((injective_iff_map_eq_zero _).1
    (IwahoriInj.iwahoriProj_injective k _ _ x.rep x.2.rep.smooth) _ h3))

theorem exists_span_of_deg_one (x : IrrGL (k := k)) (hx : x.1 = 1) : ∃ t : x.2.rep.V, ∀ v, ∃ c : ℂ, v = c • t := by
  have : Subsingleton (Fin x.1) := hx ▸ inferInstance
  obtain ⟨ψ, -, ⟨e⟩⟩ := RankLeOne.exists_equiv_detRep k (Fin x.1) _ x.rep x.2.rep.smooth x.2.rep.irr
  exact ⟨e.toLinearEquiv.symm 1, fun v => ⟨e.toLinearEquiv v, by
    rw [← map_smul, smul_eq_mul, mul_one, LinearEquiv.symm_apply_apply]⟩⟩

theorem not_isSpherical_quotient_parInd (e : (Σ a, m a) ≃ n) {ρ : Representation ℂ (Levi k m) W} {L j₀ : n} (hne : j₀ ≠ L)
    (hL : ∀ p ∈ parab k e, ∀ i, i ≠ L → p.val L i = 0) {t : W} (hline : ∀ w : W, ∃ c : ℂ, w = c • t)
    (ξ : GL n k →* ℂˣ) (hξ : ∀ g ∈ KO k n, ξ g = 1)
    (f₀ : IndSp e ρ) (hf₀ : ∀ g, parInd e ρ g f₀ = (ξ g : ℂ) • f₀) (h0 : f₀ ≠ 0)
    {σ : Representation ℂ (GL n k) Y} (hσ : σ.IsIrreducible)
    (q : (parInd e ρ).IntertwiningMap σ) (hq : Function.Surjective q) : ¬ IsSpherical σ := by
  intro hs
  obtain ⟨y, hy, hy0⟩ := (Submodule.ne_bot_iff _).1 hs
  rw [← map_fixed_of_surjective (isSmooth_parInd e ρ) SplitFlip.isCompact_KO hq] at hy
  obtain ⟨f, hf, rfl⟩ := hy
  have hfix : f₀ ∈ fixed (parInd e ρ) (KO k n) := IwahoriInj.mem_fixed.2 fun g hg => by
    rw [hf₀, hξ g hg, Units.val_one, one_smul]
  have ht : f₀.1.1 1 ≠ 0 := fun h => h0 (SatInd.eq_zero_of_apply_one _ hfix h)
  obtain ⟨c, hc⟩ := hline (f.1.1 1)
  obtain ⟨d, hd'⟩ := hline (f₀.1.1 1)
  have hd0 : d ≠ 0 := by rintro rfl; exact ht (by rw [hd', zero_smul])
  have hff : f = (c / d) • f₀ := by
    refine sub_eq_zero.1 (SatInd.eq_zero_of_apply_one _ (sub_mem hf (Submodule.smul_mem _ _ hfix)) ?_)
    show f.1.1 1 - (c / d) • f₀.1.1 1 = 0
    rw [hc, hd', smul_smul, div_mul_cancel₀ _ hd0, sub_self]
  have hq0 : q.toLinearMap f₀ ≠ 0 := fun h0 => hy0 (by rw [hff, map_smul, h0, smul_zero])
  have hqi : ∀ g f, q.toLinearMap (parInd e ρ g f) = σ g (q.toLinearMap f) := fun g f => q.isIntertwining _ _ g f
  have hall : ∀ g z, σ g z = (ξ g : ℂ) • z := by
    have := (((GlobalTheory.CuspRep.isIrreducible_iff σ).1 hσ).2 (Submodule.span ℂ {q.toLinearMap f₀}) fun g z hz => by
      obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.1 hz
      rw [map_smul, ← hqi, hf₀, map_smul]
      exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))).resolve_left
        fun h => hq0 (Submodule.span_singleton_eq_bot.1 h)
    intro g z
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.1
      (this ▸ Submodule.mem_top : z ∈ Submodule.span ℂ {q.toLinearMap f₀})
    rw [map_smul, ← hqi, hf₀, map_smul, smul_comm]
  exact hq0 (map_eq_zero_of_equivariant e hne hL ξ hξ f₀ hf₀ q.toLinearMap fun g f => (hqi g f).trans (hall _ _))

theorem tprod_line {X : α → Type} [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (t : ∀ a, X a)
    (ht : ∀ a v, ∃ c : ℂ, v = c • t a) (w : PiTensorProduct ℂ X) : ∃ c : ℂ, w = c • PiTensorProduct.tprod ℂ t := by
  classical
  induction w using PiTensorProduct.induction_on with
  | smul_tprod r v =>
    choose c hc using fun a => ht a (v a)
    exact ⟨r * ∏ a, c a, by
      rw [funext hc, MultilinearMap.map_smul_univ, smul_smul]
      simp⟩
  | add a b ha hb =>
    obtain ⟨c, rfl⟩ := ha
    obtain ⟨d, rfl⟩ := hb
    exact ⟨c + d, (add_smul _ _ _).symm⟩

theorem not_isSpherical_quotient {h N : ℕ} (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N) (h1 : ∀ a, (x a).1 = 1)
    (hN : 2 ≤ N) {χ : kˣ →* ℂˣ} (hχ : IsUnram χ) (φ : (detRep (Fin N) χ).IntertwiningMap (prodIrr x hd))
    (hφ : Function.Injective φ) {σ : Representation ℂ (GL (Fin N) k) Y} (hσ : σ.IsIrreducible)
    (q : (prodIrr x hd).IntertwiningMap σ) (hq : Function.Surjective q) : ¬ IsSpherical σ := by
  have hξ : ∀ g ∈ KO k (Fin N), detChar (Fin N) χ g = 1 := fun g hg => hχ _ (StepData.valuation_det_of_mem_KO hg)
  have hf₀ : ∀ g, prodIrr x hd g (φ.toLinearMap 1) = (detChar (Fin N) χ g : ℂ) • φ.toLinearMap 1 := fun g =>
    (φ.isIntertwining _ _ g 1).symm.trans
      ((congrArg φ.toLinearMap (ofChar_apply _ _ _)).trans (map_smul φ.toLinearMap _ _))
  choose t htt using fun a => exists_span_of_deg_one (x a) (h1 a)
  have hblk : ∀ j : Fin N, (blk (stdBlocks (fun a => (x a).1) hd) j).val = j.val := fun j => by
    obtain ⟨⟨a, i⟩, rfl⟩ := (stdBlocks (fun a => (x a).1) hd).surjective j
    have := i.2
    have h2 := h1 a
    rw [blk_apply, stdBlocks_val]
    simp only [h1, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
    omega
  refine not_isSpherical_quotient_parInd (stdBlocks (fun a => (x a).1) hd) (L := ⟨N - 1, by omega⟩)
    (j₀ := ⟨0, by omega⟩) (fun h => by simp at h; omega) (fun p hp i hi => mem_parab.1 hp _ _ ?_) (tprod_line t htt) _ hξ
    (φ.toLinearMap 1) hf₀ (fun h0 => one_ne_zero (hφ (h0.trans (map_zero φ.toLinearMap).symm))) hσ q hq
  rw [Fin.lt_def, hblk, hblk]
  have := i.2
  have : (i : ℕ) ≠ N - 1 := fun h => hi (Fin.ext h)
  simp only
  omega

theorem deg_eq_one_of_isLSeg [CharZero k] {Δ : Segment k} {y : IrrGL (k := k)} (hL : IsLSeg Δ y.rep) (hs : IsSpherical y.rep) :
    y.1 = 1 := by
  obtain ⟨hd, hc⟩ := id hL
  have hsph := LocLanglands.SphFac.isSpherical_factor k Δ.len _ Δ.term hd _ y.rep hc.isSubquotient hs
  have h0 : Δ.term ⟨0, Δ.len_pos⟩ = Δ.first := by simp [Segment.term]
  have hs1 : IsSpherical Δ.first.rep := h0 ▸ hsph _
  obtain ⟨θ, hθ, e⟩ := TemperedTests.exists_eq_ofChar Δ.first (deg_eq_one_of_isCusp _ Δ.isCusp_first hs1)
  have hu : IsUnram θ := fun z hz => by
    rw [e] at hs1
    obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 hs1
    let T := (equivRep (IrrRep.det (Fin 1) θ hθ)).symm
    have hz' : diagT k (Fin 1) (fun _ => z) ∈ KO k (Fin 1) :=
      iwahori_le_KO k _ (diagT_mem_iwahori fun _ => hz)
    have h2 := T.toIntertwiningMap.isIntertwining _ _ (diagT k (Fin 1) fun _ => z) v
    replace h2 := (congrArg T.toLinearEquiv (IwahoriInj.mem_fixed.1 hv _ hz')).symm.trans h2
    have h3 : GeneralLinearGroup.det (diagT k (Fin 1) fun _ => z) = z := Units.ext (by simp [val_diagT])
    have h4 : T.toLinearEquiv v = (θ (GeneralLinearGroup.det (diagT k (Fin 1) fun _ => z)) : ℂ) • T.toLinearEquiv v :=
      h2.trans (ofChar_apply (detChar (Fin 1) θ) _ (T.toLinearEquiv v))
    rw [h3] at h4
    exact Units.ext (smul_left_injective ℂ (T.toLinearEquiv.map_ne_zero_iff.2 hv0) (h4.symm.trans (one_smul _ _).symm))
  obtain ⟨l, hl, rfl⟩ : ∃ l hl, Δ = Segment.ofChar θ hθ l hl := ⟨_, Δ.len_pos, Segment.ext_first e rfl⟩
  by_contra hne
  have hp : 0 < y.1 := hL.deg_eq ▸ Nat.mul_pos hl one_pos
  obtain ⟨φ, hφ⟩ := embeds_detRep_segment hθ hl hd
  obtain ⟨hi, q, hq, -⟩ := hc
  exact not_isSpherical_quotient _ hd (fun _ => rfl) (by omega) (isUnram_mul hu (isUnram_absPow k _)) φ hφ hi q hq hs

end Local

open NumberField IsDedekindDomain GlobalTheory.CuspRep in
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField in
theorem norm_satake_eq_one : GlobalTheory.Published.ClozelCohomological → GlobalTheory.Published.CohomologicalCsdTempered →
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ), 1 ≤ a → ∀ P : CuspSub E a, P.IsCsd →
  ∀ m : (E →+* ℂ) → Multiset ℂ, (∀ τ, P.HasInfChar τ (m τ)) → (∀ τ, (m τ).Nodup) →
  ∀ f : ℂ, (∀ τ, ∀ z ∈ m τ, ∃ k : ℤ, z = f + k) →
  ∀ (w : HeightOneSpectrum (𝓞 E)) (σ : SmIrr (GL (Fin a) (w.adicCompletion E))), P.IsLocComp w σ →
    ∀ S : Multiset ℂˣ, GlobalTheory.LFun.HasSatGL w σ.ρ S → ∀ s ∈ S, ‖(s : ℂ)‖ = 1 := by
  intro hC hT E _ _ _ a ha P hP m hm hnd f hf w σ hσ S hS
  refine norm_eq_one_of_isTemperedGL ?_ hS
  rcases ha.eq_or_lt with rfl | ha2
  · exact GKCoh.Tests.tempered_rank_one E P hP w σ hσ
  obtain ⟨j, hj⟩ : ∃ j : ℤ, 2 * f = j := by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    obtain ⟨z, hz⟩ := Multiset.card_pos_iff_exists_mem.1 ((hm τ).1 ▸ ha : 0 < (m τ).card)
    obtain ⟨k, hk⟩ := hf τ z hz
    rw [infChar_conjugate hP (hm τ) (hm _)] at hz
    obtain ⟨z', hz', e⟩ := Multiset.mem_map.1 hz
    obtain ⟨k', hk'⟩ := hf _ z' hz'
    exact ⟨-k - k', by push_cast; linear_combination -hk - hk' - e⟩
  obtain ⟨η, hu, hcsd, hη⟩ : ∃ η : Formalism.L2.Host.HChar E, η.IsUnitary ∧ (CG.ofChar η).IsCsd ∧
      ∀ τ, ∃ n : ℤ, f + expo η τ = n + ((a : ℂ) - 1) / 2 := by
    rcases Int.even_or_odd' (j - a + 1) with ⟨i, hi | hi⟩
    · have hi' : (j : ℂ) - a + 1 = 2 * i := by exact_mod_cast hi
      refine ⟨1, fun _ => norm_one, (CG.isCsd_ofChar 1).2 fun o => ?_, fun τ => ⟨i, ?_⟩⟩
      · exact CG.thetaInv_of (fun _ => rfl) (fun z => by
          have : dchi (1 : Formalism.L2.Host.HChar E) = 0 := fderiv_extZero (continuous_chiInf _) fun z => by simp [chiInf]
          simp [this]) o
      · rw [CG.expo_one]; linear_combination hj / 2 + hi' / 2
    · have hi' : (j : ℂ) - a + 1 = 2 * i + 1 := by exact_mod_cast hi
      obtain ⟨η, h1, h2, h3⟩ := _root_.GlobalTheory.HalfCsd.exists_unitary_csd_half E
      refine ⟨η, h1, h2, fun τ => ?_⟩
      obtain ⟨k, hk⟩ := h3 τ
      exact ⟨i + k + 1, by rw [hk]; push_cast; linear_combination hj / 2 + hi' / 2⟩
  have hreg : (CG.mk (P.twist η)).IsRegAlg := (CG.isRegAlg_iff _).2 fun τ => by
    have h1 : (CG.mk (P.twist η)).HasInfChar τ ((m τ).map (· + expo η τ)) := (hm τ).twist η
    rw [h1.infChar_eq]
    refine ⟨(hnd τ).map (add_left_injective _), fun z' hz' => ?_⟩
    obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.1 hz'
    obtain ⟨k, hk⟩ := hf τ z hz
    obtain ⟨n, hn⟩ := hη τ
    exact ⟨n + k, by push_cast; linear_combination hk + hn⟩
  have hcsd' : (P.twist η).IsCsd := CG.IsCsd.twist (π := CG.mk P) hcsd hP
  exact isTemperedGL_of_twist hu (hT E a ha2 _ hcsd' (hC E a ha _ hreg) w _ (hσ.twist η))

end GlobalTheory.TempSat
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologicalLocalComponentExponents =====
