module

public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.CoeNonzeroLocusCanonicalEqComplRange
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.DivMemOfForallPowSuccDivPowMem

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.ZH GlobalTheory.Poinc
open GlobalTheory.SiegelTor

namespace GlobalTheory.EffCartierData

theorem idealSheaf_le_of_closedPoints : ∀ (X : Scheme.{0}) [CompactSpace X] (D : EffCartierData X)
    (K : X.IdealSheafData), (∀ x : X, IsClosed ({x} : Set X) → ∃ (W : X.affineOpens) (i : D.ι)
      (h : W.1 ≤ D.U i), x ∈ W.1 ∧ resG X h (D.f i) ∈ K.ideal W) → D.idealSheaf ≤ K := by
  intro X _ D K hK
  have hc : ∀ y : X, ∃ x : X, IsClosed ({x} : Set X) ∧ y ⤳ x := fun y => by
    obtain ⟨x, hx, hxc⟩ := (isClosed_closure (s := ({y} : Set X))).exists_closed_singleton
      ⟨y, subset_closure rfl⟩
    exact ⟨x, hxc, specializes_iff_mem_closure.2 hx⟩
  choose x hxc hyx using hc
  choose W i h hxW hmem using fun y => hK (x y) (hxc y)
  refine Scheme.IdealSheafData.le_of_iSup_eq_top W
    (eq_top_iff.2 fun y _ => TopologicalSpace.Opens.mem_iSup.2 ⟨y, (hyx y).mem_open (W y).1.isOpen (hxW y)⟩)
    fun y => ?_
  rw [D.ideal_idealSheaf (W y) (i y) (h y), Ideal.span_singleton_le_iff_mem]
  exact hmem y

end GlobalTheory.EffCartierData
