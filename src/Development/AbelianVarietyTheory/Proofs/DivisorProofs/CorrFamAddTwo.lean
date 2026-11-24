module

public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
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

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.RedChern

def defect (Q q : ℕ) (U : Scheme.{0}) (v : (Γ(U, ⊤))ˣ) : Sec ((res _ (tw q 1)).X 0) U :=
  (redMap Q q 1).app U 0 (kumT Q U v) - kumT q U (v ^ (Q / q))

def defectSec (Q q : ℕ) (U : Scheme.{0}) (u : (Γ(U, ⊤))ˣ) : Sec ((res _ (tw q 1)).X 0) U :=
  pick fun s => ∀ (V : Scheme.{0}) (g : V ⟶ U) (v : (Γ(V, ⊤))ˣ), v ^ Q = Units.map g.appTop.hom.toMonoidHom u →
    Sec.res g s = defect Q q V v

def corrFam (Q q : ℕ) {E : Spc} (L : E ⟶ ofCat (glCat 1)) :
    ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + 1 = s → ∀ U : Scheme.{0}, Sx E p U → Sec ((res _ (tw q 1)).X s) U
  | 1, s, h, U, x => Sec.map ((res _ (tw q 1)).XIsoOfEq (show (0 : ℤ) = s by omega)).hom
      (defectSec Q q U (lineUnit L x))
  | _, _, _, _, _ => 0

theorem corrFam_zero (Q q : ℕ) {E : Spc} (L : E ⟶ ofCat (glCat 1)) (s : ℤ) (h : -((0 : ℕ) : ℤ) + 1 = s)
    (U : Scheme.{0}) (x : Sx E 0 U) : corrFam Q q L 0 s h U x = 0 := rfl

theorem corrFam_add_two (Q q : ℕ) {E : Spc} (L : E ⟶ ofCat (glCat 1)) (p : ℕ) (s : ℤ)
    (h : -((p + 2 : ℕ) : ℤ) + 1 = s) (U : Scheme.{0}) (x : Sx E (p + 2) U) : corrFam Q q L (p + 2) s h U x = 0 := rfl

theorem corrFam_one (Q q : ℕ) {E : Spc} (L : E ⟶ ofCat (glCat 1)) (h : -((1 : ℕ) : ℤ) + 1 = 0) (U : Scheme.{0})
    (x : Sx E 1 U) : corrFam Q q L 1 0 h U x = defectSec Q q U (lineUnit L x) := by
  simp [corrFam, Sec.map]

end GlobalTheory.EtC.RedChern
