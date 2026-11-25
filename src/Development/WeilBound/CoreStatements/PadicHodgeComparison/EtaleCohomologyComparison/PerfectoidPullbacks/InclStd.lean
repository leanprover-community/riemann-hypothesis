module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SEqOne
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HarishChandraFormulaStatement
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

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.Pb

def stdI {b : Base} {L : b.Fun} (Q : ObjectProperty (Thick L)) (r : Option ℤ) (c : b.R) : IdF (sP Q).A :=
  (match r with
    | none => IdF.bot _
    | some r => sFil Q r).sup (IdF.span _ c)

theorem incl_std {b : Base} {L : b.Fun} {Q Q' : ObjectProperty (Thick L)} (h : Q' ≤ Q) (r : Option ℤ) (c : b.R) :
    (incl h).Le (stdI Q r c) (stdI Q' r c) := by
  intro T x hx
  cases r <;> exact hx

theorem incl_fil {b : Base} {L : b.Fun} {Q Q' : ObjectProperty (Thick L)} (h : Q' ≤ Q) (r : ℤ) :
    (incl h).Le (sFil Q r) (sFil Q' r) := by
  intro T x hx
  exact hx

def FlatT {b : Base} {L : b.Fun} : ObjectProperty (Thick L) := fun T => T.i.Flat

def Used {b : Base} {L : b.Fun} (Q : ObjectProperty (Thick L)) : Prop :=
  (b.p = 0 ∧ ∃ l s, Q = TF l s) ∨ (b.p ≠ 0 ∧ (Q = ⊤ ∨ Q = FlatT))

structure TFBase {R : Type} [CommRing R] {I : Ideal R} (γ : DividedPowers I) (l s : ℕ) : Prop where
  nil : pdP γ s = ⊥
  tf : ∀ (r : ℕ) (x : R), (l : R) * x ∈ pdP γ r → x ∈ pdP γ r
  dv : ∀ n : ℕ, n ≠ 0 → ∃ (k : ℕ) (u : R), (n : R) * u = (l : R) ^ k

section K
variable {K : Type} [CommRing K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K))

abbrev KS (s : ℕ) (𝒱 : Set X.Opens) : ObjectProperty (Thick (smFun X q)) :=
  St (γ := dividedPowersBot K) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) (TF 1 s) 𝒱

def resK (Q : ObjectProperty (Thick (smFun X q))) (j : ℕ) : HdR q j →ₗ[K] HO Q j := (CH.Mor.restrict (O (smFun X q)) Q.ι).pull j

def quoK (Q : ObjectProperty (Thick (smFun X q))) (r : ℤ) (j : ℕ) : HdR q j →ₗ[K] HQ Q 0 r j :=
  ((toSq (sFil Q 0) (sFil Q r) fun T => T.obj.pdPow_zero).pull j).comp (resK q Q j)

def cupK {i j n : ℕ} (h : i + j = n) (x : HdR q i) (y : HdR q j) : HdR q n := (CH.mulP (thA (smFun X q))).cup h x y

def oneK : HdR q 0 := CH.oneH (thA (smFun X q))

def powK (x : HdR q 2) : ∀ k : ℕ, HdR q (2 * k)
  | 0 => oneK q
  | k + 1 => cupK q (by omega) (powK x k) x

end K

end CrystallineSemistableComparison.Pb
