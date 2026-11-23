module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArcZeroZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExtensionOfArcVanishingSmoothChart
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

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits Filter Topology NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.ShFam.BdArc (IsHolPts)

theorem _root_.GlobalTheory.T.exists_extension_of_arc_vanishing_smooth_chart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (X : FlagCover Y) (Z : Comp Xo c) (la : GlobalTheory.AllWt.Weight Dw) (σ : c.F →+* ℂ) (m : H0 (str₀ X Z) (L₀ X Z la) (U₀ X Z)), ArcZero X Z la σ m → ∀ (W : (Y₀ X Z).Opens) (hW : IsAffineOpen W) (i : (L₀ X Z la).ι) (p : Γ(Y₀ X Z, W)) (hi : W ≤ (L₀ X Z la).U i), IsDomain Γ(Y₀ X Z, W) → RingHom.Smooth (Spec.preimage ((show Sp Γ(Y₀ X Z, W) ⟶ Y₀ X Z from hW.fromSpec) ≫ str₀ X Z)).hom → p ≠ 0 → (∀ y' ∈ W, (y' ∈ bd₀ X Z ↔ y' ∉ (Y₀ X Z).basicOpen p)) → ∃ b : Γ(Y₀ X Z, W), (∀ y' (h : y' ∈ W) (h' : y' ∈ U₀ X Z), ger y' h b = H0.germ i y' h' (hi h) m) ∧ ∀ y' (h : y' ∈ W), y' ∈ bd₀ X Z → ger y' h b ∈ IsLocalRing.maximalIdeal ((Y₀ X Z).presheaf.stalk y') := by
  first | exact @GlobalTheory.CompHS.exists_extension_of_arcZero | exact GlobalTheory.CompHS.exists_extension_of_arcZero | (intros; apply GlobalTheory.CompHS.exists_extension_of_arcZero <;> assumption)
