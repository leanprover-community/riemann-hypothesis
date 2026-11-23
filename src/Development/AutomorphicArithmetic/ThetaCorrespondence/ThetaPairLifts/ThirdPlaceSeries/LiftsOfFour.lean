module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftLambdaBound
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.LevelCarrying
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCoprimeOfNatCast
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRightActFunPull
import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeLeOfPullbackLePowFiniteEtale

@[expose] public section



section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.BadEmb
variable {K Γ A : Type} [Field K] [Group Γ] [CommRing A] [Algebra K A] (B : Subalgebra K A) (tr : Γ → A →ₐ[K] A)
  (t1 : ∀ f, tr 1 f = f) (tm : ∀ g h f, tr (g * h) f = tr g (tr h f)) (tB : ∀ g, ∀ f ∈ B, tr g f ∈ B)
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (hpq : 1 ≤ Dw.p + Dw.q) (hA : l.A.Coprime l.M)
  {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r)
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H)
theorem lifts_of_four_quantitative_conditions {Q₁ Q₂ Q₃ Q₄ R : ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (ι : Fm.Ix x) (p : Pt Fm x hx ι)
      (_i : Fin (Fm.D x ι).R.m) (_PP _C : ℝ), Prop}
    (h₁ : _root_.GlobalTheory.CovTop.LiftsCondition Q₁) (h₂ : _root_.GlobalTheory.CovTop.LiftsCondition Q₂) (h₃ : _root_.GlobalTheory.CovTop.LiftsCondition Q₃) (h₄ : _root_.GlobalTheory.CovTop.LiftsCondition Q₄)
    (h : ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (ι : Fm.Ix x) (p : Pt Fm x hx ι) (i : Fin (Fm.D x ι).R.m)
      (PP C₁ C₂ C₃ C₄ : ℝ), Q₁ Fm x hx ι p i PP C₁ → Q₂ Fm x hx ι p i PP C₂ → Q₃ Fm x hx ι p i PP C₃ →
      Q₄ Fm x hx ι p i PP C₄ → R Fm x hx ι p i PP 0) : _root_.GlobalTheory.CovTop.LiftsCondition R := by
  refine (((h₁.and h₂).and h₃).and h₄).imp fun Fm CH _ h' => ?_
  obtain ⟨⟨⟨⟨_, -, a1⟩, _, -, a2⟩, _, -, a3⟩, _, -, a4⟩ := h'
  obtain ⟨x0, h'⟩ := ((a1.and a2).and a3).and a4
  refine ⟨0, le_rfl, x0, fun x hx hle ι p hp i => ?_⟩
  obtain ⟨⟨⟨b1, b2⟩, b3⟩, b4⟩ := h' x hx hle ι p hp
  exact h Fm x hx ι p i _ _ _ _ _ (b1 i) (b2 i) (b3 i) (b4 i)
end GlobalTheory.BadEmb
end
end
