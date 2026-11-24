module

public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameChangeByMatricesReflAndComp
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameChangeCommBaseChange
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameChangeExistsUniqueOfSamePoint
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LowerTriIsUnitDet
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.ArcLineFunctions.ArcSPin

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames

namespace GlobalTheory.Frames

theorem frChg_calculus : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (S : Type) [CommRing S] [Algebra c.F S], (∀ (g g' : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S) (s s' : S) (y y' y'' : FrPt Xo c S), FrChg g s y y' → (FrChg g' s' y' y'' ↔ FrChg (fun τ => g' τ * g τ) (s' * s) y y'')) ∧ (∀ y : FrPt Xo c S, FrChg (fun _ => 1) 1 y y) ∧ (∀ (T : Type) [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T) (g : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S) (s : S) (y y' : FrPt Xo c S) (z z' : FrPt Xo c T), FrChg g s y y' → FrMap φ y z → (FrMap φ y' z' ↔ FrChg (fun τ => (g τ).map φ) (φ s) z z')) ∧ ∀ (t : Ix Dw → Sˣ) (y y' : FrPt Xo c S), FrBor t y y' ↔ ∃ g : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S, (∀ τ i, g τ i i = (t (some ⟨τ, i⟩) : S)) ∧ (∀ τ i j, i < j → g τ i j = 0) ∧ FrChg g (t none : S) y y' := by
  intro E _ _ _ H Dw l Xo c S _ _
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro g g' s s' y y' y'' h
    refine ⟨fun h' => (frChg_refl_and_comp E H Dw l Xo c S y y' y'').2 g g' s s' h h', fun h' => ?_⟩
    have hx : y'.x = y.x := h.1
    have hx' : y''.x = y.x := h'.1
    obtain ⟨g₀, a₀, hg₀, h₀⟩ := (frChg_exists_unique E H Dw l Xo c S y y').1 hx
    obtain ⟨rfl, rfl⟩ := (frChg_exists_unique E H Dw l Xo c S y y').2 _ _ _ _ h h₀
    obtain ⟨k, b, -, hk⟩ := (frChg_exists_unique E H Dw l Xo c S y' y'').1 (hx'.trans hx.symm)
    have hc := (frChg_refl_and_comp E H Dw l Xo c S y y' y'').2 _ _ _ _ h hk
    obtain ⟨e₁, e₂⟩ := (frChg_exists_unique E H Dw l Xo c S y y'').2 _ _ _ _ h' hc
    have e₃ : g' = k := by
      funext τ
      exact ((Matrix.isUnit_iff_isUnit_det _).2 (hg₀ τ)).mul_right_cancel (congrFun e₁ τ)
    have e₄ : s' = (b : S) := a₀.isUnit.mul_right_cancel e₂
    rw [e₃, e₄]
    exact hk
  · intro y
    exact (frChg_refl_and_comp E H Dw l Xo c S y y y).1
  · intro T _ _ φ g s y y' z z' h hm
    exact ChgBC.frChg_baseChange E H Dw l Xo c S T φ y y' z z' g s h hm
  · intro t y y'
    rw [(frBor_calculus E H Dw l Xo c S y y' y').1 t]
    exact ⟨fun ⟨g, a, b, c⟩ => ⟨g, b, a, c⟩, fun ⟨g, a, b, c⟩ => ⟨g, b, a, c⟩⟩

end GlobalTheory.Frames
