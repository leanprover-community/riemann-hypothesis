module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.MatchSmulAlt
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open MeasureTheory PositivityTheory.Rg.Tf.Geo

namespace UpperTheory.Gal.InertialTypesAlt.L

private theorem quotInt_smul {G T X : Type*} [Group G] [MeasurableSpace G] [MeasurableSpace T] [MeasurableSpace X]
    (μ : Measure X) (u : X → G) (j : T → G) (ν : Measure T) (c : ℂ) (Φ : X → ℂ) :
    quotInt μ u j ν (c • Φ) = c * quotInt μ u j ν Φ := by
  unfold quotInt
  split_ifs with h
  · simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]
    exact integral_const_mul _ _
  · simp

private theorem orb_smul {n : ℕ} {R : Type*} [CommRing R] [TopologicalSpace R] [MeasurableSpace (GL (Fin n) R)]
    (μ : Measure (GL (Fin n) R)) (γ : GL (Fin n) R) (ν : Measure (Subgroup.centralizer {γ})) (c : ℂ)
    (f : GL (Fin n) R → ℂ) : orb μ γ ν (c • f) = c * orb μ γ ν f := by
  unfold orb
  exact quotInt_smul μ id (fun t : Subgroup.centralizer {γ} => (t : GL (Fin n) R)) ν c
    (fun x => f (x⁻¹ * γ * x))

theorem matchSmul : MatchSmul := by
  intro F E _ _ _ _ _ σ n v c hc φ f h
  intro _ _ _ _ mE mF h1 h2 h3 h4 γ hγ ν hν
  obtain ⟨hA, hB⟩ := h mE mF h1 h2 h3 h4 γ hγ ν hν
  refine ⟨fun δ hδ => ?_, fun hn => ?_⟩
  · rw [hA δ hδ, one_mul, orb_smul]
  · have := hB hn
    rw [orb_smul] at this
    exact (mul_eq_zero.1 this).resolve_left hc

end UpperTheory.Gal.InertialTypesAlt.L

end
