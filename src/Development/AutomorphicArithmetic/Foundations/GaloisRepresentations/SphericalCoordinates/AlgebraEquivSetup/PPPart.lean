module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.LevRefine
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.UG UpperTheory.Gal.W2.Seed
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 AfQ Plc sim mat comp rat lev ZU)
open scoped TensorProduct Classical

theorem UpperTheory.Gal.W2.Seed.pPPart :
    JEq → PPart := by
  intro hJ E _ _ _ A n p _ S T g
  have hext := (hJ E A n p S T.toAdT T.μ T.mu T.a T.j T.j_mx).1
  have hoff : ∀ w : Plc E, (p : 𝓞 E) ∉ w.asIdeal → comp w (T.sec (T.j g)) = comp w g :=
    fun w hw => (T.j_eq (T.sec (T.j g)) g).1 (T.j_sec _) w hw
  have hk1 : ∀ w : Plc E, (p : 𝓞 E) ∉ w.asIdeal → comp w ((T.sec (T.j g))⁻¹ * g) = 1 := by
    intro w hw
    rw [map_mul, map_inv, hoff w hw, inv_mul_cancel]
  have hk2 : ∀ w : Plc E, (p : 𝓞 E) ∈ w.asIdeal → comp w ((T.sec (T.j g))⁻¹ * g) = comp w g := by
    intro w hw
    rw [map_mul, map_inv, T.sec_p _ w hw, inv_one, one_mul]
  refine ⟨(T.sec (T.j g))⁻¹ * g, by group, hk1, hk2, fun h => hext _ _ fun w => ?_⟩
  rw [map_mul (comp w) (T.sec h), map_mul (comp w) _ (T.sec h)]
  by_cases hw : (p : 𝓞 E) ∈ w.asIdeal
  · rw [T.sec_p h w hw, one_mul, mul_one]
  · rw [hk1 w hw, one_mul, mul_one]
