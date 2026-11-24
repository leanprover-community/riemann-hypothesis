module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsStrictIff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StrictlyConcavePolFanConeRealForms
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

theorem _root_.GlobalTheory.T.strictlyConcave_polFan_cone_real_forms : ∀ (X : Type) [AddCommGroup X] [Module.Finite ℤ X] (φ : InvFun ℤ) (N m : ℕ) (u : Fin m → LinearMap.BilinForm ℤ X) (w : (X × X) →₀ ℤ), IsPolFanOn (id : ℤ → ℤ) φ X → IsCone (id : ℤ → ℤ) φ u → StrictWith (id : ℤ → ℤ) φ N (linW w) u → (∀ B ∈ rcone u, (N : ℝ) * evalR φ B = evalW w B) ∧ ∀ B ∈ psdCone (bar := (id : ℤ → ℤ)) (X := X), (N : ℝ) * evalR φ B ≤ evalW w B ∧ ((N : ℝ) * evalR φ B = evalW w B → B ∈ rcone u) := by
  first | exact @GlobalTheory.PolCell.strictWith_real | exact GlobalTheory.PolCell.strictWith_real | (intros; apply GlobalTheory.PolCell.strictWith_real <;> assumption)
