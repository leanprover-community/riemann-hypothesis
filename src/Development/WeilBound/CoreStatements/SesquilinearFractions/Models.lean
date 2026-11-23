module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCMFrame
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelActionBaseChangeStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelFreeOfSmoothStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelPullbackEquivalenceStatement
public import Development.WeilBound.CoreStatements.SesquilinearFractions.GLieIntA
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Henselian
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

noncomputable section

namespace PositivityTheory.Xgf.cm_lie_model_action

open PositivityTheory.Xgf.isogeny_decomposition_product

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l}
  {c : Coeff l} {g : ℕ} {ty : Fin g → (E →+* ℂ)} {FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty} {i : Fin FU.n}
  {Z : ∀ b : Bool, Curve0 H (sgnRt H b)} {P : (FU.Di i).La →+ (Fin g → ℂ)} {hP : IsPeriod (FU.Di i) ty P}

theorem models (X : CMPack Z c FU i hP) :
    ∃ (M : LieModel Xo.univ.t.G (under X.y) (Fin g → X.K)) (ρ : 𝓞 E →+* Module.End X.K (Fin g → X.K)),
      M.IsActOf Xo.univ.t.act.act ρ ∧
      ∃ (M1 : LieModel X.t.G (𝟙 (Sp X.K)) (Fin g → X.K))
        (M2 : LieModel X.B.t.G (𝟙 (Sp X.K) ≫ spMap (algebraMap (𝓞 X.K) X.K)) (Fin g → X.K)),
        (∀ e, (M1.pt e).left ≫ X.m.φ = (M.pt e).left) ∧ (∀ e, (M1.pt e).left ≫ X.m'.φ = (M2.pt e).left) := by
  obtain ⟨n, M, ρ, hρ, -⟩ := GlobalTheory.T.lie_model_action_base_change E H Xo.X Xo.univ.t X.K (under X.y)
  have h1 : under X.y = 𝟙 (Sp X.K) ≫ under X.y := by simp
  obtain ⟨M1, hM1⟩ := (GlobalTheory.T.lie_model_pullback_equivalence Xo.X (Sp X.K) Xo.univ.t.G X.t.G (under X.y) X.m.φ X.m.cart X.K (𝟙 _)
    (Fin n → X.K)).1 (castM h1 M)
  obtain ⟨M2, hM2⟩ := (GlobalTheory.T.lie_model_pullback_equivalence (Sp (𝓞 X.K)) (Sp X.K) X.B.t.G X.t.G (spMap (algebraMap (𝓞 X.K) X.K)) X.m'.φ
    X.m'.cart X.K (𝟙 _) (Fin n → X.K)).2 M1
  obtain ⟨bas⟩ := GlobalTheory.T.lie_model_free_of_smooth (Sp (𝓞 X.K)) X.B.t.G g (by have hd := X.B.dim; rwa [X.dim] at hd) X.K
    (𝟙 (Sp X.K) ≫ spMap (algebraMap (𝓞 X.K) X.K)) (Fin n → X.K) M2
  have hn : n = g := by
    have := Module.finrank_eq_card_basis bas
    simpa using this
  subst hn
  exact ⟨M, ρ, hρ, M1, M2, fun e => (hM1 e).trans (castM_left h1 M e), hM2⟩

end PositivityTheory.Xgf.cm_lie_model_action

end
