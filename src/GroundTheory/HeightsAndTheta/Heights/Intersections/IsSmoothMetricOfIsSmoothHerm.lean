module

public import GroundTheory.HeightsAndTheta.Heights.Intersections.AnalyticResolutionHypothesesProjectiveLine
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.IsVerticalDivOfIsVerticalDivisorAlt
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.IntToRat

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

open MvPolynomial
open GroundTheory.Heights₂.Heights.NumbersDVR (MRing)

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]




theorem isProjVarQ_of_isArithVar {P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRing ι)} {e : ℕ}
    (hP : ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar P (e + 1)) :
    IsProjVarQ (P.map (MvPolynomial.map (Int.castRingHom ℚ))) e := by
  obtain ⟨-, ⟨hprime, ⟨S, hS, hPS⟩, hrel⟩, hhor, hdim⟩ := hP
  have := hprime
  have hch : ∀ m : ℤ, (C m : MvPolynomial (Σ k, ι k) ℤ) ∈ P → m = 0 := by
    intro m hm
    have hm' : m ∈ P.comap (C : ℤ →+* ReciprocityTheory.ChartRestriction.G.Geo.MRing ι) := Ideal.mem_comap.mpr hm
    rw [show P.comap (C : ℤ →+* ReciprocityTheory.ChartRestriction.G.Geo.MRing ι) = ⊥ from hhor, Ideal.mem_bot] at hm'
    exact hm'
  obtain ⟨hQ, hcomap, hd⟩ := ReciprocityTheory.AnForm.R.extQ_spec P hch
  refine ⟨(GroundTheory.Heights₂.Heights.NumbersDVR.Objects.isMultiProjPrime_iff _).mpr
    ⟨hQ, ⟨MvPolynomial.map (Int.castRingHom ℚ) '' S, ?_, ?_⟩, ?_⟩, ?_⟩
  · rintro _ ⟨f, hf, rfl⟩
    obtain ⟨a, ha⟩ := hS f hf
    exact ⟨a, fun m hm k => ha m (MvPolynomial.support_map_subset _ _ hm) k⟩
  · rw [hPS, Ideal.map_span]
  · intro k
    obtain ⟨i, hi⟩ := hrel k
    refine ⟨i, fun h => hi ?_⟩
    rw [← hcomap, Ideal.mem_comap, MvPolynomial.map_X]
    exact h
  · have hd' : ringKrullDim (MvPolynomial (Σ k, ι k) ℚ ⧸
        P.map (MvPolynomial.map (Int.castRingHom ℚ))) + 1 =
        ((e + 1 + Fintype.card K : ℕ) : WithBot ℕ∞) := by
      rw [← hdim]
      exact hd
    show ringKrullDim (MvPolynomial (Σ k, ι k) ℚ ⧸ P.map (MvPolynomial.map (Int.castRingHom ℚ))) =
      ((e + Fintype.card K : ℕ) : WithBot ℕ∞)
    generalize ringKrullDim (MvPolynomial (Σ k, ι k) ℚ ⧸
      P.map (MvPolynomial.map (Int.castRingHom ℚ))) = d at hd'
    induction d using WithBot.recBotCoe with
    | bot =>
      rw [WithBot.bot_add] at hd'
      exact absurd hd' (WithBot.bot_ne_coe)
    | coe d =>
      induction d using ENat.recTopCoe with
      | top =>
        have h3 : (⊤ : ℕ∞) + 1 = ((e + 1 + Fintype.card K : ℕ) : ℕ∞) := by exact_mod_cast hd'
        rw [top_add] at h3
        exact absurd h3.symm (ENat.natCast_ne_top _)
      | coe n =>
        have h1 : n + 1 = e + 1 + Fintype.card K := by exact_mod_cast hd'
        have h2 : n = e + Fintype.card K := by omega
        rw [h2]
        rfl

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
