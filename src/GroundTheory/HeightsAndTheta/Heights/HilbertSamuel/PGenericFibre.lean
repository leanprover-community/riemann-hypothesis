module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGenericFibre
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PGenericFibreDim
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.IsMultiHomogIdealIff
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
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.IntToRat
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ProjDefs

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

theorem GenericFibre.proof : GenericFibre.Statement := by
  intro Ω _ _ κ _ x D hP
  obtain ⟨-, ⟨hPp, ⟨S, hS, hPS⟩, hrel⟩, hhor, hdim⟩ := hP
  have : (coordIdeal ℤ x).IsPrime := hPp
  have hchar : ∀ m : ℤ, (C m : MvPolynomial (Ix κ) ℤ) ∈ coordIdeal ℤ x → m = 0 := by
    intro m hm
    have h1 : m ∈ (coordIdeal ℤ x).comap (C : ℤ →+* MRing (GlobalTheory κ)) := hm
    rw [show (coordIdeal ℤ x).comap (C : ℤ →+* MRing (GlobalTheory κ)) = ⊥ from hhor, Ideal.mem_bot] at h1
    exact h1
  obtain ⟨hqp, hcomap, hform⟩ := ReciprocityTheory.AnForm.R.extQ_spec (coordIdeal ℤ x) hchar
  have hq : ReciprocityTheory.AnForm.R.extQ (coordIdeal ℤ x) =
      (coordIdeal ℤ x).map (MvPolynomial.map (Int.castRingHom ℚ)) := rfl
  rw [← hq]
  refine ⟨⟨hqp, ?_, ?_⟩, ?_⟩
  · rw [GroundTheory.Heights₂.Heights.Bridge.isMultiHomogIdeal_iff]
    refine ⟨MvPolynomial.map (Int.castRingHom ℚ) '' S, ?_, ?_⟩
    · rintro _ ⟨f, hf, rfl⟩
      obtain ⟨b, hb⟩ := hS f hf
      exact ⟨b, fun m hm k => hb m (MvPolynomial.support_map_subset _ _ hm) k⟩
    · rw [hq, hPS, Ideal.map_span]
  · intro k
    obtain ⟨i, hi⟩ := hrel k
    refine ⟨i, fun hX => hi ?_⟩
    rw [← hcomap, Ideal.mem_comap, map_X]
    exact hX
  · rw [hdim] at hform
    simp only [Fintype.card_unit] at hform
    refine GroundTheory.Heights₂.Heights.ObjectsChow.GenericFibreDim.eq_natCast_of_add_one_eq (D + 1) _ ?_
    rw [hform]
    push_cast
    rfl

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
