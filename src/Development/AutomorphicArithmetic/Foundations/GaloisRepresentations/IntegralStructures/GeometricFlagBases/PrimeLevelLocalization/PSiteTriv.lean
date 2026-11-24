module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.PrimeProj
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PFormPerfSt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.L2.Host GlobalTheory.HeckeGal
open GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKDef
open GlobalTheory.LFun (KGL satEig)
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 Plc GLw AfQ sim mat comp rat loc lev SameK IsCen Shape IsForm IsKap mOf)
open UpperTheory.Gal.W2.Seed (Arith Setup)
open scoped TensorProduct Classical

namespace UpperTheory.Gal.Int.Geo.Pl

theorem atPrime_of {E : Type} [Field E] [NumberField E] [IsCMField E] {A : Arith E} {n p : ℕ} [Fact p.Prime] (S : Setup A n p)
    {q : ℕ} (hq : q.Prime) (hp : q ≠ p) (hg : A.Good q) {r : ℤ} (hr : (q : ℤ) ∣ r ^ 2 - A.tr * r + A.nm) {w : Plc E}
    (hw : (q : 𝓞 E) ∈ w.asIdeal) (hω : A.ω - (r : 𝓞 E) ∈ w.asIdeal) : AtPrime S.D q r w.asIdeal :=
  ⟨hq, hp, hg.1.1, hr, W2.Seed.pFormPerfSt E A n q hg.2, w.isMaximal, by
    refine Ideal.span_le.2 ?_
    rintro y (rfl | rfl)
    exacts [hw, hω]⟩

theorem siteTriv_of (hS : Sides) (hL : LevBasic) : SiteTriv := by
  intro E _ _ _ A n p _ S x hx N q hq hp hg hN w hw
  obtain ⟨r, hr, hω⟩ := (hS E A x hx q hq hg.1 w hw).2.2.2.2.2.1
  have h1 : ordCompl[q] N.1 = N.1 := by
    rw [Nat.factorization_eq_zero_of_not_dvd hN]; simp
  refine ⟨⟨q, r, ⊤, S.L.KN N.1, hg, atPrime_of S hq hp hg hr hw hω, ?_, ?_, ?_⟩, rfl, rfl⟩
  · rw [h1]
    exact ⟨N.2.1, ((Nat.Prime.coprime_iff_not_dvd hq).2 hN).symm, N.2.2, top_sup_eq _, 0, le_top⟩
  · rw [h1, Ideal.mul_top]
    exact (hL p S.D S.G S.L).2.2.1 N.1
  · rw [h1, Ideal.mul_top]
    exact Ideal.mem_span_singleton_self _

end UpperTheory.Gal.Int.Geo.Pl
