module

public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
public import Development.AutomorphicArithmetic.PrimeDiscriminants.SmallRam
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
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

theorem UpperTheory.Ram.not_dvd_QS_of_notMem_sq :
    ∀ {φ : Formalism.HC.Frame} (H : Formalism.HC.HostAx φ), H.toHostRaw.Exact → ∀ (E' : Type) [Field E'] [NumberField E'] (_ : E' ≃+* H.E) (P : HeightOneSpectrum (𝓞 E')) (p : ℕ), p.Prime →
      (p : 𝓞 E') ∈ P.asIdeal → (p : 𝓞 E') ∉ P.asIdeal ^ 2 → ¬ p ∣ H.QS ∧ (H.QS : 𝓞 E') ∉ P.asIdeal := by
  intro φ H hex E' _ _ f P p hp hpP hpP2
  haveI hPp : P.asIdeal.IsPrime := P.isPrime
  let g : 𝓞 H.E ≃+* 𝓞 E' := (NumberField.RingOfIntegers.mapRingEquiv f).symm
  let Q : Ideal (𝓞 H.E) := P.asIdeal.comap g
  haveI : Q.IsPrime := Ideal.comap_isPrime g P.asIdeal
  have hndvd : ¬ p ∣ H.QS := by
    intro hdvd
    have hmem : ((p : ℕ) : 𝓞 H.E) ∈ Q := by
      show g (p : 𝓞 H.E) ∈ P.asIdeal
      rw [map_natCast]
      exact hpP
    have h2 := H.mem_sq_of_dvd_QS hex hp hdvd Q hmem
    have h3 : g (p : 𝓞 H.E) ∈ P.asIdeal ^ 2 := Ideal.le_comap_pow g 2 h2
    rw [map_natCast] at h3
    exact hpP2 h3
  refine ⟨hndvd, fun hQS => ?_⟩
  have hcop : p.Coprime H.QS := (Nat.Prime.coprime_iff_not_dvd hp).2 hndvd
  have hb := Nat.gcd_eq_gcd_ab p H.QS
  rw [hcop.gcd_eq_one] at hb
  apply P.isPrime.ne_top
  rw [Ideal.eq_top_iff_one]
  have h1 := congrArg (Int.cast : ℤ → 𝓞 E') hb
  push_cast at h1
  rw [h1]
  exact add_mem (P.asIdeal.mul_mem_right _ hpP) (P.asIdeal.mul_mem_right _ hQS)
