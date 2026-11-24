module

public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open GlobalTheory.AbLaw

namespace GlobalTheory.FormalAlg

variable {R : Type} [CommRing R] {W : Scheme.{0}}

def baseIdeal (f : W ⟶ Spec (CommRingCat.of R)) (J : Ideal R) : W.IdealSheafData :=
  Scheme.IdealSheafData.ofIdealTop (J.map (cst f ⊤))

theorem baseIdeal_ideal (f : W ⟶ Spec (CommRingCat.of R)) (J : Ideal R) (U : W.affineOpens) :
    (baseIdeal f J).ideal U = J.map (cst f U.1) := by
  rw [baseIdeal, Scheme.IdealSheafData.ofIdealTop_ideal, Ideal.map_map]
  congr 1
  ext r
  exact rs_cst f le_top r

def IsSystem (f : W ⟶ Spec (CommRingCat.of R)) (I : Ideal R) (t : ℕ → W.IdealSheafData) : Prop :=
  ∀ e, t e = t (e + 1) ⊔ baseIdeal f (I ^ (e + 1))

def Reduces (f : W ⟶ Spec (CommRingCat.of R)) (I : Ideal R) (T : W.IdealSheafData)
    (t : ℕ → W.IdealSheafData) : Prop :=
  ∀ e, T ⊔ baseIdeal f (I ^ (e + 1)) = t e

def Alg (f : W ⟶ Spec (CommRingCat.of R)) (I : Ideal R) : Prop :=
  ∀ t : ℕ → W.IdealSheafData, IsSystem f I t → (∀ e, IsProper ((t e).subschemeι ≫ f)) →
    ∃ T : W.IdealSheafData, IsProper (T.subschemeι ≫ f) ∧ Reduces f I T t

theorem IsSystem.baseIdeal_le {f : W ⟶ Spec (CommRingCat.of R)} {I : Ideal R}
    {t : ℕ → W.IdealSheafData} (h : IsSystem f I t) (e : ℕ) : baseIdeal f (I ^ (e + 1)) ≤ t e := by
  rw [h e]
  exact le_sup_right

end GlobalTheory.FormalAlg
