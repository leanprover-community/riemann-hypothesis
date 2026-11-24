module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RenVar
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PointPoly
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SchubGamApply
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdmissibleChernFormProdGrassmannianBasisCopies
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

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical


theorem _root_.GlobalTheory.T.admissibleChernForm_prod_grassmannianBasisCopies : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (g : GlobalTheory.AllWt.Psi H → MvPolynomial (Bool × ℕ) ℝ), (∀ τ, g τ ∈ GlobalTheory.GrassTop.basis Dw.p Dw.q) → ∀ Θ : MvPolynomial ((E →+* ℂ) × ℕ) ℝ →ₗ[ℝ] ℝ, GlobalTheory.Schubert.admitted H Dw Θ → Θ (∏ τ, GlobalTheory.GrassTop.ren τ (g τ)) = (if ∀ τ, g τ = X (true, Dw.p) ^ Dw.q then (-1 : ℝ) ^ (Dw.p * Dw.q * Fintype.card (GlobalTheory.AllWt.Psi H)) else 0) * Θ (GlobalTheory.LieBase.pointPoly H Dw) := by
  first | exact @GlobalTheory.GrassTopProd.adm_apply_prod_ren_eq_ite_mul_pointPoly | exact GlobalTheory.GrassTopProd.adm_apply_prod_ren_eq_ite_mul_pointPoly | (intros; apply GlobalTheory.GrassTopProd.adm_apply_prod_ren_eq_ite_mul_pointPoly <;> assumption)
