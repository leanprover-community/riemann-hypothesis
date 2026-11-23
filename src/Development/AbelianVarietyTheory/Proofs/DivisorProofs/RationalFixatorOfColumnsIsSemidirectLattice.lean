module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsLv
public import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactSpaceAxis
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsUniqueIsProdMeasureFinAway
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicFixatorEqUnipotentRadicalMulCommonFixatorStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCovolumeCommonAdelicFixatorOfColumnsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsotropicFrameDecompositionSubgroupPropertiesStatement
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

namespace GlobalTheory.SphEis

theorem semiLat_fixG : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E)
    (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ →
    ∃ (ν : Measure (unipRad σ J C)) (π : Measure (fixG σ J C ⊓ fixG σ J D : Subgroup (GAd σ J))) (DN : Set (unipRad σ J C))
      (DM : Set (fixG σ J C ⊓ fixG σ J D : Subgroup (GAd σ J))),
      SemiLat (unipRad σ J C) (fixG σ J C ⊓ fixG σ J D : Subgroup (GAd σ J)) (ratPts σ J ⊓ fixG σ J C) ν π DN DM := by
  intro F E _ _ _ _ _ σ n J j m C D Z J₀ H
  have key : ∀ {P : Subgroup (GAd σ J)}, P ≤ fixG σ J C →
      (ratPts σ J ⊓ fixG σ J C).subgroupOf P = (ratPts σ J).subgroupOf P := fun h => by
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun e => e.1, fun e => ⟨e, h x.2⟩⟩
  obtain ⟨hC, -, cM, cN, hN, hP, hd, hn, -⟩ := GlobalTheory.T.isotropicFrameDecomposition_subgroup_properties F E σ n J j m C D Z J₀ H
  haveI := locallyCompact_unipRad H.cm H.herm hC
  obtain ⟨ν, DN, hν, hDN, h1⟩ := exists_mass_one (cocompact_unipRad H.cm H.herm hC)
  haveI : LocallyCompactSpace (fixG σ J C ⊓ fixG σ J D : Subgroup (GAd σ J)) := cM.locallyCompactSpace
  have hDM := GlobalTheory.AutomorphicL2Unitary.isFundamentalDomain_stdDom
    ((ratPts σ J).subgroupOf (fixG σ J C ⊓ fixG σ J D : Subgroup (GAd σ J))) Measure.haar
  refine ⟨ν, Measure.haar, DN, _,
    { closedN := cN
      closedM := cM
      norm := fun x hx u hu => (hn x (hP hx.1) u).1 hu
      disj := hd
      dec := ?_
      haarN := hν
      haarM := inferInstance
      domN := by rw [key hN]; exact hDN
      domM := by rw [key inf_le_left]; exact hDM
      finN := by rw [h1]; exact ENNReal.one_ne_top
      finM := GlobalTheory.T.finiteCovolume_common_adelicFixatorOfColumns F E σ n J j m C D Z J₀ H _ _ inferInstance hDM }⟩
  rintro γ ⟨hγ, hf⟩
  obtain ⟨u, hu, x, hx, e, hr⟩ := GlobalTheory.T.adelicFixator_eq_unipotentRadical_mul_commonFixator F E σ n J j m C D Z J₀ H γ hf
  refine ⟨u, hu, x, hx, ⟨?_, hN hu⟩, ⟨hr hγ, hx.1⟩, e⟩
  have : u = γ * x⁻¹ := by rw [e, mul_inv_cancel_right]
  rw [this]
  exact (ratPts σ J).mul_mem hγ ((ratPts σ J).inv_mem (hr hγ))

end GlobalTheory.SphEis
