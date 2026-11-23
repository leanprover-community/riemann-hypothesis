module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SelfDualAt
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StandardAdditiveCharacterLocalNeOneSplitPrime
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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

@[expose] public section

open NumberField IsDedekindDomain

namespace GlobalTheory.St.G.SplitUnram

theorem not_sq_dvd_of_splitsIn : ∀ (E : Type) [Field E] [NumberField E] (T : ℕ), T.Prime → GlobalTheory.St.G.SplitsIn E T →
    ∀ w : HeightOneSpectrum (𝓞 E), (T : 𝓞 E) ∈ w.asIdeal → ¬ w.asIdeal ^ 2 ∣ Ideal.span {(T : 𝓞 E)} := by
  intro E _ _ T hT hs w hw hdvd
  have := w.isPrime
  have hnd := GlobalTheory.St.G.PsiLoc.not_dvd_different hT hs w.asIdeal hw
  have hun : Algebra.IsUnramifiedAt ℤ w.asIdeal := not_dvd_differentIdeal_iff.1 hnd
  have he : w.asIdeal.ramificationIdx ℤ = 1 := Ideal.ramificationIdx_eq_one_iff.2 hun
  have hp : Prime (T : ℤ) := Nat.prime_iff_prime_int.mp hT
  have hmax : (Ideal.span {(T : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hmap : Ideal.map (algebraMap ℤ (𝓞 E)) (Ideal.span {(T : ℤ)}) = Ideal.span {((T : ℕ) : 𝓞 E)} := by
    rw [Ideal.map_span]; simp
  have hle : Ideal.map (algebraMap ℤ (𝓞 E)) (Ideal.span {(T : ℤ)}) ≤ w.asIdeal := by
    rw [hmap, Ideal.span_le]; simpa using hw
  have : w.asIdeal.LiesOver (Ideal.span {(T : ℤ)}) :=
    ⟨hmax.eq_of_le (Ideal.comap_ne_top _ w.isPrime.ne_top) (Ideal.map_le_iff_le_comap.mp hle)⟩
  have hb : Ideal.span {(T : ℤ)} ≠ ⊥ := by simpa using hT.ne_zero
  rw [← Ideal.ramificationIdx'_eq_ramificationIdx (Ideal.span {(T : ℤ)}) w.asIdeal hb] at he
  have h2 := (Ideal.ramificationIdx'_ne_one_iff hle).2
  rw [hmap] at h2
  exact h2 (Ideal.le_of_dvd hdvd) he

end GlobalTheory.St.G.SplitUnram
