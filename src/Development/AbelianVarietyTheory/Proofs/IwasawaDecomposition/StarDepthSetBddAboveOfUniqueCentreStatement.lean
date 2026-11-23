module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarDepthToFunNonneg
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarDepthSetBddAboveOfUniqueCentre
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell


theorem _root_.GlobalTheory.T.starDepthSet_bddAbove_of_unique_centre : ∀ (O : Type) [CommRing O] (bar : O → O) (ψ w : InvFun O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) (v : LinearMap.BilinForm ℤ X), IsCell bar ψ γ → B ∈ rcone γ → v ∈ balForms bar X → (∀ y, 0 ≤ v y y) → v ≠ 0 → (∀ v' ∈ balForms bar X, (∀ y, 0 ≤ v' y y) → w.evalZ v' = 1 → InRCone γ v' → v' = v) → ∀ (n : ℕ) (π : (Fin n → O) →ₗ[O] X), Function.Surjective π → BddAbove (depthSet bar ψ w n (fun a b => B (π a) (π b))) := by
  first | exact @GlobalTheory.PolFan.depthSet_bddAbove_of_unique_centre | exact GlobalTheory.PolFan.depthSet_bddAbove_of_unique_centre | (intros; apply GlobalTheory.PolFan.depthSet_bddAbove_of_unique_centre <;> assumption)
