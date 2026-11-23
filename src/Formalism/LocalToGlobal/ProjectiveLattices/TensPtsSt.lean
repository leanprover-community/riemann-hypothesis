module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
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

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

attribute [local instance] Over.cartesianMonoidalCategory

variable {X : Scheme.{0}} (A : Over X)

def powO : ℕ → Over X
  | 0 => 𝟙_ (Over X)
  | k + 1 => A ⊗ powO k

def prj : (k : ℕ) → Fin k → (powO A k ⟶ A)
  | 0, j => j.elim0
  | k + 1, j => Fin.cases (fst A (powO A k)) (fun j' => snd A (powO A k) ≫ prj k j') j

def tup {T : Over X} : (k : ℕ) → (Fin k → (T ⟶ A)) → (T ⟶ powO A k)
  | 0, _ => toUnit T
  | k + 1, a => lift (a 0) (tup k fun j => a j.succ)

variable [GrpObj A] [IsCommMonObj A] {O : Type} [CommRing O] (act : OAct O A)

def matMap {k : ℕ} (e : Fin k → Fin k → O) : powO A k ⟶ powO A k :=
  tup A k fun i => psum A (fun j => prj A k j ≫ act.act (e i j)) Finset.univ

abbrev tensSch {k : ℕ} (e : Fin k → Fin k → O) : Scheme.{0} :=
  pullback (lift (matMap A act e) (𝟙 (powO A k))).left (lift (𝟙 (powO A k)) (𝟙 (powO A k))).left

def tensO {k : ℕ} (e : Fin k → Fin k → O) : Over X :=
  Over.mk (pullback.fst _ _ ≫ (powO A k).hom : tensSch A act e ⟶ X)

def tensIncl {k : ℕ} (e : Fin k → Fin k → O) : tensO A act e ⟶ powO A k :=
  Over.homMk (pullback.fst _ _) rfl

def tcoord {k : ℕ} (e : Fin k → Fin k → O) (j : Fin k) : tensO A act e ⟶ A :=
  tensIncl A act e ≫ prj A k j


end Formalism.L2.Pj
