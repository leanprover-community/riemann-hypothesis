module

public import Formalism.LocalToGlobal.IndefiniteReal.PeterssonHilbertSpace
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEqAlt
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsReadingLaws
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RankOneUnitary
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Formalism.AlgebraicWeights.IsAlgWeight
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import ReciprocityTheory.Automorphisms.PlaceA
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.RecTie

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin

noncomputable section

namespace GlobalTheory.RowModCanon

open MeasureTheory Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.PeterssonHilbertSpace
open scoped InnerProductSpace

theorem ipM_smul_measure {D : D7} {V : Formalism.BasicNotions.TH.HSp D} {S : D.what₂.Tau → Formalism.BasicNotions.TH.SPar} (M : DSModel V S)
    (hne : SmNonzero M) (ν : Measure (GA D V)) (𝓕 : Set (GA D V)) {a : ℝ} (ha : 0 ≤ a) (T T' : MMap M)
    (h : ∃ c, IsMultIP M ν 𝓕 T T' c) :
    ipM M (ENNReal.ofReal a • ν) 𝓕 T T' = (a : ℂ) * ipM M ν 𝓕 T T' := by
  have h1 := ipM_spec M ν 𝓕 T T' h
  have h2 : IsMultIP M (ENNReal.ofReal a • ν) 𝓕 T T' ((a : ℂ) * ipM M ν 𝓕 T T') := by
    intro v v'
    obtain ⟨hi, he⟩ := h1 v v'
    refine ⟨?_, ?_⟩
    · rw [IntegrableOn, Measure.restrict_smul]
      exact hi.smul_measure ENNReal.ofReal_ne_top
    · rw [Measure.restrict_smul, integral_smul_measure, he, ENNReal.toReal_ofReal ha, Complex.real_smul, mul_assoc]
  have h3 := ipM_spec M _ 𝓕 T T' ⟨_, h2⟩
  choose w hw using hne
  have hw' : ∀ τ, (w τ : M.H τ) ≠ 0 := fun τ h => hw τ (Submodule.coe_eq_zero.1 h)
  have hv0 : ∏ τ, ⟪(w τ : M.H τ), (w τ : M.H τ)⟫_ℂ ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun τ _ => inner_self_ne_zero.2 (hw' τ)
  exact hasPeterssonInner_unique M _ 𝓕 T T' w hv0 h3 h2

end GlobalTheory.RowModCanon

namespace GlobalTheory.RowModCanon

open MeasureTheory Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Lev
  Formalism.IndefR.Links Formalism.IndefR.RecTie


end GlobalTheory.RowModCanon
