module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLieBase
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHolomorphicEigenFrameDirsInExpChart
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
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.InterPolyProdSum

@[expose] public section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts


theorem _root_.GlobalTheory.T.exists_holomorphic_eigenFrame_dirs_in_expChart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (C : FlagCpt T.Z e) (X : Var F) (j : X.X ⟶ gen T.Z) (f : C.Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e C X j f f₀ Eb A₀ → ∀ (y : GlobalTheory.CxPts X.str (σ.comp e.toRingHom)) (n g : ℕ) (ch₀ : OpenPartialHomeomorph (GlobalTheory.CxPts (genStr T.Z) σ) (Fin n → ℂ)) (ex : ExpMaps T.Z σ g), IsExpChart ch₀ ex → cxOf e σ hj y ∈ ch₀.source → ch₀ (cxOf e σ hj y) = 0 → ∃ A ∈ Eb.S (GlobalTheory.Cartier.under y), ∃ r : ℝ, 0 < r ∧ ∃ W : (Fin n → ℂ) → (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) → Fin g → ℂ, (∀ p k, DifferentiableOn ℂ (fun u => W u p k) (Metric.ball 0 r)) ∧ LinearIndependent ℂ (W 0) ∧ ∀ z : GlobalTheory.CxPts X.str (σ.comp e.toRingHom), cxOf e σ hj z ∈ ch₀.source → ch₀ (cxOf e σ hj z) ∈ Metric.ball 0 r → (∃ g' : EigFrame T.Z σ ((cxOf e σ hj z).1 ≫ genι T.Z), FrameAt e f₀ A₀ A z g') ∧ ∀ g' : EigFrame T.Z σ ((cxOf e σ hj z).1 ≫ genι T.Z), FrameAt e f₀ A₀ A z g' → Dirs ⟨cxOf e σ hj z, g'⟩ (fun w => (ex (cxOf e σ hj z) w).left) (W (ch₀ (cxOf e σ hj z))) := by
  first | exact @GlobalTheory.LieBase.exists_chart_dirs | exact GlobalTheory.LieBase.exists_chart_dirs | (intros; apply GlobalTheory.LieBase.exists_chart_dirs <;> assumption)
