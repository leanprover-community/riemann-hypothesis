module

public import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
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

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC

namespace LateralTheory.E.t_E6Cut

def ConnK (R : Type) [CommRing R] (F : Shv R) (c : ℤ) {K L : Cx R} (f : K ⟶ L) : Prop :=
  ∀ n : ℤ, (n < c - 1 → Function.Bijective (HK.pull R f F n)) ∧ (n < c → Function.Injective (HK.pull R f F n))

def Conn (R : Type) [CommRing R] (F : Shv R) (c : ℤ) {E E' : Spc} (f : E ⟶ E') : Prop := ConnK R F c ((chains R).map f)

def EtLoc (T : Scheme.{0}) (P : ∀ V : Scheme.{0}, (V ⟶ T) → Prop) : Prop :=
  ∃ S ∈ Scheme.etaleTopology.{0} T, ∀ (V : Scheme.{0}) (k : V ⟶ T), S k → P V k

def sxMap {E E' : Spc} (f : E ⟶ E') {p : ℕ} {T : Scheme.{0}} (x : Sx E p T) : Sx E' p T :=
  (f.app (op (SimplexCategory.mk p))).app (op T) x

def sxRes {E : Spc} {p : ℕ} {V T : Scheme.{0}} (k : V ⟶ T) (x : Sx E p T) : Sx E p V :=
  (E.obj (op (SimplexCategory.mk p))).map k.op x

end LateralTheory.E.t_E6Cut
