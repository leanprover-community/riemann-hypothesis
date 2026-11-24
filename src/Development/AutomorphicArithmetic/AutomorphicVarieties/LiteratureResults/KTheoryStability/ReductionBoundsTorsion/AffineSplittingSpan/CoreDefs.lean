module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.AffineSplittingSpan.SpanPrism
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

namespace PositivityTheory.KB.SplitAffineSpectral.NormTraceLemmas

variable {P Q : Type} [Group P] [Group Q]

abbrev Bi (P Q : Type) (a b : ℕ) : Type := (Fin a → Q) → (Fin b → P) → ℝ

def dh {a b : ℕ} (F : Bi P Q (a + 1) b) : Bi P Q (a + 2) b := fun x y => dc (fun x' => F x' y) x

def dv {a b : ℕ} (F : Bi P Q a (b + 1)) : Bi P Q a (b + 2) := fun x y => dc (F x) y

def PInv (pr : P →* Q) {a b : ℕ} (F : Bi P Q a b) : Prop :=
  ∀ (g : P) x y, F (fun i => pr g * x i) (fun j => g * y j) = F x y

def Ru (u : Q) {a b : ℕ} (F : Bi P Q a b) : Bi P Q a b := fun x y => F (fun i => x i * u) y

def Rt (t : P) {a b : ℕ} (F : Bi P Q a b) : Bi P Q a b := fun x y => F x (fun j => y j * t)

def Tc (t : P) {a b : ℕ} (F : Bi P Q a b) : Bi P Q a b := fun x y => F x (fun j => t⁻¹ * y j * t)

def Hv (t : P) {a b : ℕ} (F : Bi P Q a (b + 1)) : Bi P Q a b :=
  fun x y => PrismSpan.prism (fun p => p * t) (F x) y

def RuL (u : Q) (a b : ℕ) : Module.End ℝ (Bi P Q a b) where
  toFun := Ru u
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def TcL (t : P) (a b : ℕ) : Module.End ℝ (Bi P Q a b) where
  toFun := Tc t
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def cat {a c : ℕ} (x : Fin a → Q) (z : Fin c → Q) (n : ℕ) : Fin n → Q := fun i =>
  if h : (i : ℕ) < a then x ⟨i, h⟩ else if h' : (i : ℕ) - a < c then z ⟨(i : ℕ) - a, h'⟩ else 1

def zz (pr : P →* Q) {n : ℕ} (b : (Fin n → Q) → ℝ) (a c : ℕ) : Bi P Q a c :=
  fun x y => b (cat x (fun j => pr (y j)) n)

def Wtop (pr : P →* Q) {n : ℕ} (b : (Fin n → Q) → ℝ) : Bi P Q 1 n := fun _ y => b (fun j => pr (y j))

def QC {n : ℕ} (b : (Fin (n + 1) → Q) → ℝ) : Prop :=
  (∀ (g : Q) x, b (fun i => g * x i) = b x) ∧ dc b = 0

end PositivityTheory.KB.SplitAffineSpectral.NormTraceLemmas

end
