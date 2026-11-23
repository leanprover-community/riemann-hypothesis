module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBaseFrame
public import Formalism.LocalToGlobal.ProjectiveLattices.CompHt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBigCellSectionOverBasicOpenInterior
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

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical


theorem _root_.GlobalTheory.T.exists_bigCellSection_over_basicOpen_interior : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed (Xo := Xo) (c := c) → ∀ (U : TF.Y.X.affineOpens) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)), IsEigBasis TF U e v → ∀ (W : (Y₀ TF.X Z).Opens) (k : TF.X.F.J) (L N : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) Γ(Y₀ TF.X Z, W)), IsCell TF Z U e v W k L N → ∀ (a : Γ(TF.Y.X, U.1)), TF.Y.X.basicOpen a ≤ LogKS.interior TF.Y ⊓ barComp TF.Y Z ⊓ (TF.X.F.M k).U → (∃ w : Y₀ TF.X Z, w ∈ W ∧ w ∈ U₀ TF.X Z ∧ toBase TF Z w ∈ TF.Y.X.basicOpen a) → ∃ z₁ : Sp (Localization.Away (MvPolynomial.C a : MvPolynomial (VIx Dw) Γ(TF.Y.X, U.1))) ⟶ Y₀ TF.X Z, ⊤ ≤ z₁ ⁻¹ᵁ U₀ TF.X Z ∧ (∃ hU : ⊤ ≤ (z₁ ≫ toBase TF Z) ⁻¹ᵁ U.1, ∀ r, ev (z₁ ≫ toBase TF Z) U.1 hU r = algebraMap (MvPolynomial (VIx Dw) Γ(TF.Y.X, U.1)) (Localization.Away (MvPolynomial.C a : MvPolynomial (VIx Dw) Γ(TF.Y.X, U.1))) (MvPolynomial.C r)) ∧ ((z₁ ⁻¹ᵁ W : TopologicalSpace.Opens _) : Set (Sp (Localization.Away (MvPolynomial.C a : MvPolynomial (VIx Dw) Γ(TF.Y.X, U.1))))).Nonempty ∧ ∀ (S : Type) [CommRing S] (ψ : Localization.Away (MvPolynomial.C a : MvPolynomial (VIx Dw) Γ(TF.Y.X, U.1)) →+* S) (hW : ⊤ ≤ (spMap ψ ≫ z₁) ⁻¹ᵁ W) (σ : E →+* ℂ), ∃ b : Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) S, (∀ i j, i < j → b i j = 0) ∧ ∀ i j, ψ (algebraMap (MvPolynomial (VIx Dw) Γ(TF.Y.X, U.1)) _ (if h : i < j then MvPolynomial.X ⟨σ, ⟨(i, j), h⟩⟩ else if i = j then 1 else 0)) = ∑ m, b i m * ev (spMap ψ ≫ z₁) W hW ((L σ * N σ) m j) := by
  first | exact @GlobalTheory.LogPole.exists_cell_section_away | exact GlobalTheory.LogPole.exists_cell_section_away | (intros; apply GlobalTheory.LogPole.exists_cell_section_away <;> assumption)
