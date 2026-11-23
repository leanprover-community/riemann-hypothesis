module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain

namespace GlobalTheory.CMModel

theorem exists_prime_natCast_mem_pow_of_ringHom :
    ∀ (F H : Type) [Field F] [NumberField F] [Field H] [NumberField H] (f : F →+* H) (w : HeightOneSpectrum (𝓞 F)) (p n : ℕ), (p : 𝓞 F) ∈ w.asIdeal ^ n → ∃ P : Ideal (𝓞 H), P.IsPrime ∧ P ≠ ⊥ ∧ (p : 𝓞 H) ∈ P ^ n := by
  intro F H _ _ _ _ f w p n hp
  letI : Algebra F H := f.toAlgebra
  haveI := w.isMaximal
  obtain ⟨P, hPm, hP⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 H) w.asIdeal
  refine ⟨P, hPm.isPrime, Ideal.ne_bot_of_liesOver_of_ne_bot w.ne_bot P, ?_⟩
  have hle : w.asIdeal.map (algebraMap (𝓞 F) (𝓞 H)) ≤ P := by
    rw [Ideal.map_le_iff_le_comap]
    exact le_of_eq hP.over
  have h1 := Ideal.mem_map_of_mem (algebraMap (𝓞 F) (𝓞 H)) hp
  rw [Ideal.map_pow, map_natCast] at h1
  exact Ideal.pow_right_mono hle n h1

end GlobalTheory.CMModel
