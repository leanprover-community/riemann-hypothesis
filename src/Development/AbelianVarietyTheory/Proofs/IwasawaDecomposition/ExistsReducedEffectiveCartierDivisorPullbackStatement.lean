module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsReducedEffectiveCartierDivisorPullback
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

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.FlagBundle

theorem _root_.GlobalTheory.T.exists_reduced_effective_cartierDivisor_pullback : ∀ (F : Type) [Field F] (B Y : GlobalTheory.ProjVar.Var F) (φ : B.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ B.X) (D : B.Dv), (ratOf B).IsHom (ratOf Y) φ f → KeepsRad (ratOf B) (ratOf Y) φ f → D.Eff → (∀ (y : B.X) (g : B.Fnˣ), D.IsEqn y g → ∀ (a : B.Fn) (n : ℕ), RegAt y a → RegAt y (a ^ n / g) → RegAt y (a / g)) → ∃ D' : Y.Dv, D'.Eff ∧ (∀ y, y ∈ D'.supp ↔ f y ∈ D.supp) ∧ ∀ (y : Y.X) (g : Y.Fnˣ), D'.IsEqn y g → ∀ (a : Y.Fn) (n : ℕ), RegAt y a → RegAt y (a ^ n / g) → RegAt y (a / g) := by
  first | exact @GlobalTheory.FlagBundle.DivPull.exists_reduced_pullback | exact GlobalTheory.FlagBundle.DivPull.exists_reduced_pullback | (intros; apply GlobalTheory.FlagBundle.DivPull.exists_reduced_pullback <;> assumption)
