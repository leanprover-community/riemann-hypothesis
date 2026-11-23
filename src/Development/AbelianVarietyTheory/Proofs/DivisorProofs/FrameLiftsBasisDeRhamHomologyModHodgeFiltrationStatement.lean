module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
public import Formalism.LocalToGlobal.ProjectiveLattices.IsCombAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameLiftsBasisDeRhamHomologyModHodgeFiltration
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

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory GlobalTheory.DeRham GlobalTheory.Cris
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.frameLifts_basis_deRhamHomology_mod_hodgeFiltration : GlobalTheory.Published.AbelianDeRham → ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {K : Type} [Field K] [Algebra c.F K] (y : FrPt Xo c K) {A : Over (Sp K)} [GrpObj A] {π : A.left ⟶ Xo.univ.t.G.left}, IsGrpPullback A Xo.univ.t.G y.x π → ∀ (ub : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → (epsR K ⟶ A)), (∀ σ k, (ub σ k).left ≫ π = y.u σ k) → ∀ (hb : (Σ σ : E →+* ℂ, Fin (Dw.mult σ)) → HdR A), (∀ k, IsLieImage (hb k) (ub k.1 k.2)) → Submodule.span K (Set.range hb) ⊔ Fil A = ⊤ ∧ LinearIndependent K (fun k => (Submodule.Quotient.mk (hb k) : HdR A ⧸ Fil A)) := by
  first | exact @GlobalTheory.LieBasis.lifts_basis_mod_fil | exact GlobalTheory.LieBasis.lifts_basis_mod_fil | (intros; apply GlobalTheory.LieBasis.lifts_basis_mod_fil <;> assumption)
