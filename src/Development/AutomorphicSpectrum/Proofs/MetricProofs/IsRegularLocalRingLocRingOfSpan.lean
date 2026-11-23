module

public import ReciprocityTheory.AnalyticForms.RegularLocalRings.JacChart
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
import Mathlib.Order.CompletePartialOrder
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
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.StalkLocA

@[expose] public section

namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Kreg

open MvPolynomial ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Ar.Cmp

theorem isRegularLocalRing_locRing_of_span :
    ∀ (m e : ℕ) (I : Ideal (MvPolynomial (Fin m) ℂ)) (t : Fin m → ℂ)
      (r : Fin e → MvPolynomial (Fin m) ℂ), (∀ h ∈ I, eval t h = 0) →
      ringKrullDim (locRing I t) = e →
      Ideal.span (Set.range fun l => algebraMap _ (locRing I t) (r l)) =
        Ideal.map (algebraMap _ (locRing I t)) (ptIdeal t) →
      IsRegularLocalRing (locRing I t) := by
  intro m e I t r hI hdim hspan
  obtain ⟨hloc, hnoeth⟩ := locRing_isLocalRing_isNoetherian I t hI
  haveI := hloc
  haveI := hnoeth
  have hle : I ≤ ptIdeal t := (le_ptIdeal_iff' I t).2 hI
  apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
  rw [maximalIdeal_locRing hle, ← hspan, hdim]
  have h1 : (Set.range fun l => algebraMap (MvPolynomial (Fin m) ℂ) (locRing I t) (r l)).ncard ≤ e := by
    rw [← Set.image_univ]
    calc _ ≤ (Set.univ : Set (Fin e)).ncard := Set.ncard_image_le Set.finite_univ
      _ = e := by rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]
  have h2 : (Ideal.span (Set.range fun l => algebraMap (MvPolynomial (Fin m) ℂ) (locRing I t) (r l))).spanFinrank ≤ e :=
    (Submodule.spanFinrank_span_le_ncard_of_finite (Set.finite_range _)).trans h1
  exact_mod_cast h2

end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Kreg
