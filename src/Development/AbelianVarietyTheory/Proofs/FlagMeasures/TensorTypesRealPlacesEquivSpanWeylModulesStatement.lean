module

public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TensorTypesRealPlacesEquivSpanWeylModules
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.Forms Formalism.UG Matrix NumberField IsDedekindDomain
open scoped InnerProductSpace TensorProduct

theorem _root_.GlobalTheory.T.tensor_types_realPlaces_equiv_span_weylModules : ∀ (ι : Type) [Fintype ι] (k n : ℕ) (h : k = n) (lam : ι → DomWeight n) (u : ι → Fin k → ℝ), (∀ τ (i : Fin k), u τ i = ((lam τ).w (Fin.cast h i) : ℝ) + ((rhoVec k i : ℚ) : ℝ)) → ∀ (Vl : ι → Type) [∀ τ, NormedAddCommGroup (Vl τ)] [∀ τ, InnerProductSpace ℂ (Vl τ)] (πl : ∀ τ, Matrix (Fin k) (Fin k) ℂ → (Vl τ →L[ℂ] Vl τ)), (∀ τ, IsHCTypeU k (u τ) (πl τ)) → ∀ (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] (tens : (∀ τ, Vl τ) → W), (∀ x y, ⟪tens x, tens y⟫_ℂ = ∏ τ, ⟪x τ, y τ⟫_ℂ) → Submodule.span ℂ (Set.range tens) = ⊤ → ∃ Jp : W →ₗ⋆[ℂ] MvPolynomial (ι × Fin n × Fin n) ℂ, (∀ ξ, Jp ξ ∈ CSpan lam) ∧ (∀ p ∈ CSpan lam, ∃ ξ, Jp ξ = p) ∧ (∀ ξ η, nfAll lam (Jp η) (Jp ξ) = ⟪η, ξ⟫_ℂ) ∧ ∀ (m : ι → Matrix (Fin n) (Fin n) ℂ), (∀ τ, m τ ∈ Matrix.unitaryGroup (Fin n) ℂ) → ∀ A : W →L[ℂ] W, (∀ x, A (tens x) = tens (fun τ => πl τ ((m τ).submatrix (Fin.cast h) (Fin.cast h)) (x τ))) → ∀ (G o : ι → Matrix (Fin n) (Fin n) ℂ), (∀ τ, IsUnit (o τ).det) → ∀ (ξ : W) (y y' : Frames G), IsTr (fun τ => o τ * m τ * (o τ)⁻¹) y' y → fnOf G (shiftOf lam) (fun τ => (o τ)⁻¹) (Jp (A ξ)) y = fnOf G (shiftOf lam) (fun τ => (o τ)⁻¹) (Jp ξ) y' := by
  first | exact @GlobalTheory.TenTypes.tensor_dict | exact GlobalTheory.TenTypes.tensor_dict | (intros; apply GlobalTheory.TenTypes.tensor_dict <;> assumption)
