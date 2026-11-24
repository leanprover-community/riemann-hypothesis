module

public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AbelContinuation
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.Chebotarev.EulerSum
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet

@[expose] public section

set_option autoImplicit false

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani

theorem norm_natCast_cpow_neg (n : ℕ) {s : ℂ} (hs : 1 < s.re) :
    ‖(n : ℂ) ^ (-s)‖ = (n : ℝ) ^ (-s.re) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h0 : -s ≠ 0 := fun h => by
      have : s = 0 := neg_eq_zero.mp h
      simp [this] at hs
      linarith
    have h1 : -s.re ≠ 0 := by linarith
    simp [Complex.zero_cpow h0, Real.zero_rpow h1]
  · simpa using Complex.norm_natCast_cpow_of_pos hn (-s)

theorem classSummable : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔣 𝔞 𝔟 : Ideal (𝓞 F)) (J : Type) [Fintype J]
    (r : J → ℕ) (y : J → 𝓞 F) (v : ∀ j, Fin (r j) → 𝓞 F), ClassParam 𝔣 𝔞 𝔟 r y v → ∀ s : ℂ, 1 < s.re →
      Summable (fun I : {I : Ideal (𝓞 F) // CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I 𝔞} => ((Ideal.absNorm I.1 : ℕ) : ℂ) ^ (-s)) := by
  intro F _ _ _ 𝔣 𝔞 𝔟 J _ r y v _ s hs
  have h := (ReciprocityTheory.Cheb.summable_absNorm_rpow_ideal F hs).subtype
    (fun I : Ideal (𝓞 F) => CoprimeTo F 𝔣 I ∧ RayRel F 𝔣 I 𝔞)
  refine Summable.of_norm (h.congr fun I => ?_)
  exact (norm_natCast_cpow_neg _ hs).symm

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani
