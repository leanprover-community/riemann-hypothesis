module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsDominantOfSection
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NumConsEqMulOfEffectiveDivisorSuppSection
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

theorem _root_.GlobalTheory.T.num_cons_eq_mul_of_effective_divisor_supp_section : ∀ (F : Type) [Field F] (Y : Var F) (W : Dbl Y), W.Small → ∀ Θ : CartierDiv W.Z, Θ.Eff → (Θ.supp : Set W.Z) = Set.range W.δ → ∃ μ : ℤ, μ ≠ 0 ∧ ∀ y : Fin Y.dim → CartierDiv W.Z, letI := algebraΓOfHom (W.p₁ ≫ Y.str); W.num (Fin.cons Θ y : Fin (Y.dim + 1) → CartierDiv W.Z) = μ * interNumRed F (⟨closure {W.δ (genericPoint Y.X)}, isClosed_closure⟩ : Closeds W.Z) fun i => toLB (y i) := by
  first | exact @GlobalTheory.FlagPush.Dbl.num_cons_eq_mul_of_supp_eq_range | exact GlobalTheory.FlagPush.Dbl.num_cons_eq_mul_of_supp_eq_range | (intros; apply GlobalTheory.FlagPush.Dbl.num_cons_eq_mul_of_supp_eq_range <;> assumption)
