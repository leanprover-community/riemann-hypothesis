module

public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsChartDimBound
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.CurvePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDivSuppAC
public import Mathlib.RingTheory.Ideal.Height

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1

universe u v w

theorem ChartDimBound.proof : ChartDimBound.Statement.{u, v, w} := by
  intro K _ ι _ F _ V i hV hi
  classical
  obtain ⟨hVp, hVh, -⟩ := hV
  let f : K → MRingOver F ι := fun k => X ⟨k, i k⟩ - 1
  let t : Set (MRingOver F ι ⧸ V) := Set.range (Ideal.Quotient.mk V ∘ f)
  have hspan : Ideal.span t = (Ideal.span (Set.range f)).map (Ideal.Quotient.mk V) := by
    rw [Ideal.map_span, ← Set.range_comp]
  let e : (MRingOver F ι ⧸ V) ⧸ Ideal.span t ≃+* MRingOver F ι ⧸ chartIdeal V i :=
    (Ideal.quotEquivOfEq hspan).trans (DoubleQuot.quotQuotEquivQuotSup V _)
  have : IsDomain (MRingOver F ι ⧸ V) := Ideal.Quotient.isDomain V
  have : Algebra.FiniteType F (MRingOver F ι ⧸ V) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ F V) (Ideal.Quotient.mkₐ_surjective F V)
  have : IsNoetherianRing (MRingOver F ι ⧸ V) := Algebra.FiniteType.isNoetherianRing F _
  have hne : Ideal.span t ≠ ⊤ := by
    have : Nontrivial (MRingOver F ι ⧸ chartIdeal V i) :=
      Ideal.Quotient.nontrivial_iff.mpr (chartIdeal_ne_top hVh hi)
    have : Nontrivial ((MRingOver F ι ⧸ V) ⧸ Ideal.span t) := e.toEquiv.nontrivial
    exact Ideal.Quotient.nontrivial_iff.mp this
  obtain ⟨M, hM, htM⟩ := Ideal.exists_le_maximal _ hne
  obtain ⟨s, hs⟩ := DimF.exists_height_of_isMaximal_of_field F (MRingOver F ι ⧸ V)
  have : M.IsPrime := hM.isPrime
  have h1 := Ideal.height_le_ringKrullDim_quotient_add_encard (p := M) t
    (fun x hx => htM (Ideal.subset_span hx))
  rw [ringKrullDim_eq_of_ringEquiv e] at h1
  have h2 : t.encard ≤ Fintype.card K := by
    calc t.encard = ((Ideal.Quotient.mk V ∘ f) '' Set.univ).encard := by rw [Set.image_univ]
      _ ≤ (Set.univ : Set K).encard := Set.encard_image_le _ _
      _ = Fintype.card K := by simp [Set.encard_univ]
  refine (ringKrullDim_le_iff_isMaximal_height_le _).mpr fun N hN => ?_
  rw [hs N hN, ← hs M hM]
  refine h1.trans ?_
  gcongr
  exact_mod_cast h2

end GroundTheory.Heights₂.Heights.Targets
