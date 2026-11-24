module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsEntireUnitAppellHumbertFrameRatio
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
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TopLeWchartNsmul
import Formalism.LocalToGlobal.ProjectiveLattices.AlgebraMapCAt
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.ArcLineFunctions.ArcSPin
import Formalism.LocalToGlobal.ProjectiveLattices.JFDFree
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames CategoryTheory.MonObj GlobalTheory.AbelianLetters
open scoped LaurentSeries

theorem _root_.GlobalTheory.T.exists_entire_unit_appellHumbert_frame_ratio : ∀ (A' : Over (Sp ℂ)) [GrpObj A'] (X : Scheme.{0}) (L : LB X) (L' : LB A'.left), L.IsLB → L'.IsLB → ∀ (φ : A'.left ⟶ X) (w : LB.Iso L' (L.pull φ)), w.IsGen → ∀ (g g' : ℕ) (u : HolUnif A' L' g') (Hm : Matrix (Fin g') (Fin g') ℂ) (χ : u.Λ → ℂ), u.IsAH Hm χ → ∀ (e : (Fin g → ℂ) → (Sp ℂ ⟶ X)) (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)), (∀ z, (u.ex (F z)).left ≫ φ = e z) → ∀ (fr : L.ι → (Fin g → ℂ) → ℂ) (th : L.Sec) (θ : (Fin g → ℂ) → ℂ), (∀ j, DifferentiableOn ℂ (fr j) {z | ⊤ ≤ e z ⁻¹ᵁ L.U j}) → (∀ j z, ⊤ ≤ e z ⁻¹ᵁ L.U j → fr j z ≠ 0) → (∀ j j' z, ⊤ ≤ e z ⁻¹ᵁ (L.U j ⊓ L.U j') → fr j z = valAt' (e z) (L.U j ⊓ L.U j') (L.g j j').val * fr j' z) → (∀ j z, ⊤ ≤ e z ⁻¹ᵁ L.U j → valAt' (e z) (L.U j) (th.f j) = θ z * fr j z) → ∃ ρ : (Fin g → ℂ) → ℂ, Differentiable ℂ ρ ∧ (∀ z, ρ z ≠ 0) ∧ ∀ (la : Fin g → ℂ) (l : u.Λ), F la = l → ∀ z, θ (z + la) * ρ (z + la) = χ l * Complex.exp (Real.pi * hermForm Hm (F z) l + Real.pi / 2 * hermForm Hm l l) * (θ z * ρ z) := by
  first | exact @GlobalTheory.FrameCompare.exists_entire_unit_automorphy | exact GlobalTheory.FrameCompare.exists_entire_unit_automorphy | (intros; apply GlobalTheory.FrameCompare.exists_entire_unit_automorphy <;> assumption)
