module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ConstGen
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.Out

open Semi

def stdSymp (g : ℕ) (i j : Fin (2 * g)) : ℤ :=
  if (i : ℕ) < g ∧ (j : ℕ) = (i : ℕ) + g then 1
  else if (j : ℕ) < g ∧ (i : ℕ) = (j : ℕ) + g then -1 else 0

variable {S : Scheme.{0}}

abbrev baseOver (S : Scheme.{0}) : Over S := Over.mk (𝟙 S)

def linComb {A : Over S} [GrpObj A] {T : Over S} {n : ℕ} (y : Fin n → (T ⟶ A)) (a : Fin n → ℕ) :
    T ⟶ A :=
  (List.ofFn fun i => y i ^ a i).prod

structure Level (P : PolAV S) (k : ℕ) (ze : Γ(S, ⊤)ˣ) where

  pt : Fin (2 * P.g) → (baseOver S ⟶ P.A)

  prim : IsPrimitiveRoot ze k

  torsion : ∀ i, pt i ^ k = 1

  indep : ∀ (K : Type) [Field K] [IsAlgClosed K] (s : Spec (CommRingCat.of K) ⟶ S)
    (c c' : Fin (2 * P.g) → Fin k),
    linComb (fun i => (Over.homMk s (by simp) : Over.mk s ⟶ baseOver S) ≫ pt i) (fun i => (c i : ℕ)) =
      linComb (fun i => (Over.homMk s (by simp) : Over.mk s ⟶ baseOver S) ≫ pt i) (fun i => (c' i : ℕ)) →
    c = c'

  span : ∀ (K : Type) [Field K] [IsAlgClosed K] (s : Spec (CommRingCat.of K) ⟶ S)
    (y : Over.mk s ⟶ P.A), y ^ k = 1 →
    ∃ c : Fin (2 * P.g) → Fin k,
      linComb (fun i => (Over.homMk s (by simp) : Over.mk s ⟶ baseOver S) ≫ pt i) (fun i => (c i : ℕ)) = y

  pairing : ∀ i j, WeilIs P.A P.L k (pt i) (pt j) (ze ^ stdSymp P.g i j)

def Level.toPt {P : PolAV S} {k : ℕ} {ze : Γ(S, ⊤)ˣ} (lev : Level P k ze)
    (a : Fin (2 * P.g) → ZMod k) : baseOver S ⟶ P.A :=
  linComb lev.pt (fun i => (a i).val)

end ReciprocityTheory.ChartRestriction.G.Out
