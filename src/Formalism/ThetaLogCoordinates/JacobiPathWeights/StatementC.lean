module

public import Formalism.ThetaLogCoordinates.JacobiPathWeights.LiftWord
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open scoped BigOperators
open Finset MvPolynomial

namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases

def FactX2wedge : Prop :=
  ∀ (R : Type) [CommRing R] (n : ℕ) (K : Form R n) (X : Fin n → R) (m : Matrix (Fin n) (Fin n) R),
    actF (wedgeF K X) m = wedgeF (actF K m) (Matrix.vecMul X m)

def FactX2contr : Prop :=
  ∀ (R : Type) [CommRing R] (n : ℕ) (K : Form R n) (Y : Fin n → R) (m : (Matrix (Fin n) (Fin n) R)ˣ),
    actF (contrF K Y) (↑m : Matrix _ _ R) =
      contrF (actF K (↑m : Matrix _ _ R)) (Matrix.vecMul Y (↑m⁻¹ : Matrix _ _ R).transpose)

def MinorMap : Prop :=
  ∀ (R R' : Type) [CommRing R] [CommRing R'] (φ : R →+* R') (n : ℕ) (m : Matrix (Fin n) (Fin n) R)
    (I J : Finset (Fin n)), φ (minorF m I J) = minorF (m.map φ) I J

def ContractWedge : Prop :=
  ∀ (R : Type) [CommRing R] (n : ℕ) (K : Form R n) (X Y : Fin n → R),
    contrF (wedgeF K X) Y = (fun I => (∑ a, X a * Y a) * K I) - wedgeF (contrF K Y) X

end Formalism.InvariantFactorPaths.GelfandTsetlinBases
