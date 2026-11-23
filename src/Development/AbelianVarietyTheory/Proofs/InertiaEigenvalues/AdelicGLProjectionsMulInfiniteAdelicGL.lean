module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIdempotentElemIdemSf
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.SchurExt
open scoped ContDiff Topology

namespace GlobalTheory.SchurExt

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

theorem idemS_mul_sInf (S : Finset (HeightOneSpectrum (𝓞 E))) (x : Cinf E) : idemS S * sInf E x = sInf E x :=
  Prod.ext (one_mul _) (mul_zero _)

theorem one_sub_idemS_mul_sInf (S : Finset (HeightOneSpectrum (𝓞 E))) (x : Cinf E) :
    (1 - idemS S) * sInf E x = 0 := by
  rw [sub_mul, one_mul, idemS_mul_sInf, sub_self]

theorem prS_infGL (S : Finset (HeightOneSpectrum (𝓞 E))) (a : ℕ) (y : GL (Fin a) (Cinf E)) :
    prS S a (infGL E a y) = infGL E a y := by
  ext i j
  change (1 : Matrix (Fin a) (Fin a) (Ad E)) i j - idemS S * (1 : Matrix (Fin a) (Fin a) (Ad E)) i j +
      idemS S * ((1 : Matrix (Fin a) (Fin a) (Ad E)) i j - sInf E ((1 : Matrix (Fin a) (Fin a) (Cinf E)) i j) +
        sInf E (y i j)) =
    (1 : Matrix (Fin a) (Fin a) (Ad E)) i j - sInf E ((1 : Matrix (Fin a) (Fin a) (Cinf E)) i j) + sInf E (y i j)
  rw [mul_add, mul_sub, idemS_mul_sInf, idemS_mul_sInf]
  ring

theorem prO_infGL (S : Finset (HeightOneSpectrum (𝓞 E))) (a : ℕ) (y : GL (Fin a) (Cinf E)) :
    prO S a (infGL E a y) = 1 := by
  ext i j
  change (1 : Matrix (Fin a) (Fin a) (Ad E)) i j - (1 - idemS S) * (1 : Matrix (Fin a) (Fin a) (Ad E)) i j +
      (1 - idemS S) * ((1 : Matrix (Fin a) (Fin a) (Ad E)) i j - sInf E ((1 : Matrix (Fin a) (Fin a) (Cinf E)) i j) +
        sInf E (y i j)) =
    (1 : Matrix (Fin a) (Fin a) (Ad E)) i j
  rw [mul_add, mul_sub, one_sub_idemS_mul_sInf, one_sub_idemS_mul_sInf]
  ring

theorem prS_prO_mul_infGL : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)
    (S : Finset (HeightOneSpectrum (𝓞 E))) (g : GA E a) (y : GL (Fin a) (Cinf E)),
    prS S a (g * infGL E a y) = prS S a g * infGL E a y ∧ prO S a (g * infGL E a y) = prO S a g := by
  intro E _ _ _ a S g y
  refine ⟨?_, ?_⟩
  · rw [map_mul, prS_infGL]
  · rw [map_mul, prO_infGL, mul_one]

end GlobalTheory.SchurExt
