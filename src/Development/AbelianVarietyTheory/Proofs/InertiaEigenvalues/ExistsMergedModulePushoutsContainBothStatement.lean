module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocMulVec
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMergedModulePushoutsContainBoth
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Formalism.SharpRestriction.LevelLetterCocycles.PairedCharacterCondition

@[expose] public section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition



theorem _root_.GlobalTheory.T.exists_merged_module_pushouts_contain_both : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (Xs : Set (D.nd.X i)) {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (a₁ : ℕ) (x₁ : Fin a₁ → D.nd.X i), (∀ j, x₁ j ∈ Xs) → ∀ (E₁ : Fin a₁ → Fin D.R.nV → KK D.nd i) (Y₁ : Submodule (D.nd.O i) (Fin a₁ → Fin D.R.nV → KK D.nd i)), Y₁.FG → ∀ (hst₁ : (∀ γ : GE D.nd, ∀ y ∈ Y₁, (fun j => (mapM (toK D.nd i) (rTwO D.nd i r (x₁ j)) γ).mulVec (y j)) ∈ Y₁)) (hE₁ : (∀ γ : GE D.nd, (fun j => (mapM (toK D.nd i) (rTwO D.nd i r (x₁ j)) γ).mulVec (E₁ j) - E₁ j) ∈ Y₁)) (a₂ : ℕ) (x₂ : Fin a₂ → D.nd.X i), (∀ j, x₂ j ∈ Xs) → ∀ (E₂ : Fin a₂ → Fin D.R.nV → KK D.nd i) (Y₂ : Submodule (D.nd.O i) (Fin a₂ → Fin D.R.nV → KK D.nd i)), Y₂.FG → ∀ (hst₂ : (∀ γ : GE D.nd, ∀ y ∈ Y₂, (fun j => (mapM (toK D.nd i) (rTwO D.nd i r (x₂ j)) γ).mulVec (y j)) ∈ Y₂)) (hE₂ : (∀ γ : GE D.nd, (fun j => (mapM (toK D.nd i) (rTwO D.nd i r (x₂ j)) γ).mulVec (E₂ j) - E₂ j) ∈ Y₂)), ∃ (a : ℕ) (x : Fin a → D.nd.X i) (_ : ∀ j, x j ∈ Xs) (E : Fin a → Fin D.R.nV → KK D.nd i) (Y : Submodule (D.nd.O i) (Fin a → Fin D.R.nV → KK D.nd i)) (_ : Y.FG) (hst : (∀ γ : GE D.nd, ∀ y ∈ Y, (fun j => (mapM (toK D.nd i) (rTwO D.nd i r (x j)) γ).mulVec (y j)) ∈ Y)) (hE : (∀ γ : GE D.nd, (fun j => (mapM (toK D.nd i) (rTwO D.nd i r (x j)) γ).mulVec (E j) - E j) ∈ Y)), GlobalTheory.Pass.LocDirect.pushSet i w hw r M x₁ E₁ Y₁ hst₁ hE₁ ⊆ GlobalTheory.Pass.LocDirect.pushSet i w hw r M x E Y hst hE ∧ GlobalTheory.Pass.LocDirect.pushSet i w hw r M x₂ E₂ Y₂ hst₂ hE₂ ⊆ GlobalTheory.Pass.LocDirect.pushSet i w hw r M x E Y hst hE := by
  first | exact @GlobalTheory.Pass.LocDirect.pushSet_merge | exact GlobalTheory.Pass.LocDirect.pushSet_merge | (intros; apply GlobalTheory.Pass.LocDirect.pushSet_merge <;> assumption)
