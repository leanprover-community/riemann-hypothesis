module

public import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.InterNumConsEqCokernel
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberNonnegOfNefAmpleAddNefStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.GeometricallyReducedOfPerfectField
public import Development.WeilBound.CoreStatements.PublishedTheorems.NefNumerics.NefRiemannRoch.IntersectionNumberNonnegEffective
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory.KleimanDim

theorem interNum_nonneg_of_ample_tens_nef : ∀ (k : Type) [Field k] [Infinite k] (d : ℕ),
    (∀ (Y : Scheme.{0}) [Algebra k Γ(Y, ⊤)], IsProjOver (strHom k (X := Y)) → topologicalKrullDim Y ≤ (d : ℕ) →
      ∀ A N : LB Y, IsAmpleLB A → IsNef k N → IsAmpleLB (tens A N)) →
    ∀ (X : Scheme.{0}) [Algebra k Γ(X, ⊤)], IsProjOver (strHom k (X := X)) →
      (∀ (E : X.Modules) [IsFiniteQC E], suppDim E ≤ (d : ℕ) → ∀ P : Fin d → LB X,
        (∀ i, IsNef k (P i)) → 0 ≤ interNum k E P) := by
  intro k _ _ d H X _ hX E _ hE P hP
  refine SheafCycle.interNum_nonneg_of_interNumRed_nonneg k X hX d E hE P (fun i => (hP i).isLB) ?_
  intro Z hZirr hZdim
  haveI := ReducedSubgroup.isReduced_subscheme_vanishingIdeal Z
  letI : Algebra k Γ((Scheme.IdealSheafData.vanishingIdeal Z).subscheme, ⊤) :=
    ((redι Z).appTop.hom.comp (algebraMap k Γ(X, ⊤))).toAlgebra
  have hcompat : ∀ r : k, (redι Z).appTop.hom (algebraMap k Γ(X, ⊤) r) =
      algebraMap k Γ((Scheme.IdealSheafData.vanishingIdeal Z).subscheme, ⊤) r := fun r => rfl
  rw [InterModel.interNumRed_eq_interNumOn k (redι Z) Z (range_redι Z) P,
    interNumOn_eq_interNum_pull hcompat (fun i => (hP i).isLB)]
  have hYproj : IsProjOver (strHom k (X := (Scheme.IdealSheafData.vanishingIdeal Z).subscheme)) := by
    rw [← comp_strHom hcompat]
    exact ProjSpace.isProjOver_comp_of_isClosedImmersion (redι Z) hX
  have hYdim : topologicalKrullDim (Scheme.IdealSheafData.vanishingIdeal Z).subscheme ≤ (d : WithBot ℕ∞) := by
    have hmem : ∀ y, (redι Z) y ∈ (Z : Set X) := fun y => by
      rw [← range_redι Z]; exact Set.mem_range_self y
    have hind := ((redι Z).isClosedEmbedding.isInducing.codRestrict hmem).topologicalKrullDim_le
    rw [hZdim] at hind
    exact hind
  have hsupp : suppDim (QCoh.structureModule (Scheme.IdealSheafData.vanishingIdeal Z).subscheme) ≤ (d : WithBot ℕ∞) :=
    (QCoh.suppDim_le _).trans hYdim
  exact T.intersectionNumber_nonneg_of_nef_ample_add_nef k _ hYproj (fun A N hA hN => H _ hYproj hYdim A N hA hN) d _ hsupp
    (fun i => (P i).pull (redι Z)) (fun i => (hP i).pull_of_isClosedImmersion (redι Z) hcompat)

end GlobalTheory.KleimanDim
