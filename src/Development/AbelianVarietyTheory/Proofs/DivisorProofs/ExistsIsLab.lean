module

public import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLabelledUniformisedModelThetaSystemTraitStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSystemRechartAffineOpenAtClassicalTraitStatement
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

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc

theorem exists_isLab : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s → ∀ (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsDiagEnd F W X₁.ρ.P X₁.u ε₁ → ∀ (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (c : CTrait X₁ p z₁), ∃ yy : X₁.S.Gam →+ ModN (X₁.S.r * X₁.S.N) (Fin 8 → c.T.D.toPre.X), IsLab X₁ ε₁ c yy := by
  intro g n F W Z i X₁ hg hn hodd himm he8 hth hproj ε₁ hdiag p _ z₁ c
  obtain ⟨c₀, hc, R', fg, frac, hth', hev, ρ', ε', u', hsame, hi₀, hle, hdiag', y₀, hy₀, hpt, hint⟩ :=
    GlobalTheory.T.thetaSystem_rechart_affineOpen_at_classicalTrait g n F W Z i X₁ hg hn hodd himm he8 hth hproj ε₁ hdiag p z₁ c
  obtain ⟨u, l, j, hq, hcong⟩ :=
    GlobalTheory.T.exists_labelled_uniformisedModel_thetaSystem_trait g n F W he8 X₁.o₁ X₁.Ω₁ _ ρ' ε' u' hdiag' p y₀ c.T c.ι c.int hpt hint
  let jm : ModN (X₁.S.r * X₁.S.N) u.D.toPre.X →+ ModN (X₁.S.r * X₁.S.N) (Fin 8 → c.T.D.toPre.X) :=
    QuotientAddGroup.map _ _ j.toAddMonoidHom (by
      rintro _ ⟨x, rfl⟩
      exact ⟨j x, by simp⟩)
  refine ⟨jm.comp l.yy, c₀, hc, R', fg, frac, hth', hev, ρ', ε', hsame, hi₀, hle, y₀, hy₀, u, l, j, hq, ?_, hcong⟩
  intro a χ ha
  simp only [AddMonoidHom.comp_apply, ha, jm]
  rfl

end GlobalTheory.Poinc
