module

public import Development.AbelianVarietyTheory.Definitions.Divisors.EntireEqOfHalfPlane
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedTransport

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport
open GlobalTheory.ToricTransport (coordIn)
open scoped nonZeroDivisors

namespace GlobalTheory.CMVal.ModFRat

theorem modF_rat : ∀ {E : Type} [Field E] [NumberField E] (y : (Af E)ˣ), ∃ q : ℚ, modF y = q := by
  intro E _ _ y
  refine ⟨∏ᶠ v : HeightOneSpectrum (𝓞 E), ((Ideal.absNorm v.asIdeal : ℕ) : ℚ) ^ (WithZero.log (Valued.v ((y : Af E) v))), ?_⟩
  have h := MonoidHom.map_finprod_of_injective ((Rat.castHom ℝ : ℚ →+* ℝ) : ℚ →* ℝ) Rat.cast_injective
    (fun v : HeightOneSpectrum (𝓞 E) => ((Ideal.absNorm v.asIdeal : ℕ) : ℚ) ^ (WithZero.log (Valued.v ((y : Af E) v))))
  simp only [MonoidHom.coe_coe, Rat.coe_castHom, Rat.cast_zpow, Rat.cast_natCast] at h
  rw [h]
  rfl

end GlobalTheory.CMVal.ModFRat
