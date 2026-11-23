module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsCan
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaTraceBaseChangeIff
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
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.KerScheme

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ThetaTraceBC

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeckeEx

theorem exists_isRigIso_baseChange : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {T Ω : Type} [CommRing T] [CommRing Ω] (χ : T →+* Ω) {x x' : Sp T ⟶ Xo.X} {x₁ x₁' : Sp Ω ⟶ Xo.X} {Ψ : Gx x ⟶ Gx x'} {Ψ₁ : Gx x₁ ⟶ Gx x₁'} {pm : Gx x₁ ⟶ Gx x} {pm' : Gx x₁' ⟶ Gx x'} {k : ℤ} {β : LB.Gen (isoLB Xo.univ.t.G Xo.univ.t.PP Ψ k)}, IsCan χ pm → IsCan χ pm' → Ψ₁ ≫ pm' = pm ≫ Ψ → Ψ₁ ≫ (fst (Over.mk x₁') Xo.univ.t.G).left = (fst (Over.mk x₁) Xo.univ.t.G).left → IsRigIso Xo.univ.t.G Xo.univ.t.PP Ψ k β → ∃ β₁ : LB.Gen (isoLB Xo.univ.t.G Xo.univ.t.PP Ψ₁ k), IsRigIso Xo.univ.t.G Xo.univ.t.PP Ψ₁ k β₁ ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Gx x₁) (z : Z) (J : (Z ⟶ Xo.univ.t.G.left) → Xo.univ.t.PP.L.ι), Good Xo.univ.t.PP.L z J → val β₁ r z J = val β (r ≫ pm) z J := by
  intro E _ _ _ H Dw l Xo T Ω _ _ χ x x' x₁ x₁' Ψ Ψ₁ pm pm' k β hc hc' hΨ h0 hβ
  let σ : (Over.mk x₁ : Over Xo.X) ⟶ Over.mk x := Over.homMk (spMap χ) hc.1.symm
  let σ' : (Over.mk x₁' : Over Xo.X) ⟶ Over.mk x' := Over.homMk (spMap χ) hc'.1.symm
  have epm : pm = (σ ▷ Xo.univ.t.G).left := GlobalTheory.HeckeFrCompare.gx_ext
    (by rw [hc.2.2, ← Over.comp_left, whiskerRight_fst]; rfl) (by rw [hc.2.1, ← Over.comp_left, whiskerRight_snd])
  have epm' : pm' = (σ' ▷ Xo.univ.t.G).left := GlobalTheory.HeckeFrCompare.gx_ext
    (by rw [hc'.2.2, ← Over.comp_left, whiskerRight_fst]; rfl) (by rw [hc'.2.1, ← Over.comp_left, whiskerRight_snd])
  obtain ⟨β₁, h₁, hv⟩ := isRigIso_pull (σ := σ) (σ' := σ') rfl (by rw [← epm, ← epm']; exact hΨ) h0 hβ
  exact ⟨β₁, h₁, fun Z r z J hJ => by rw [hv r z hJ, ← epm]⟩

end GlobalTheory.HeckeEx
