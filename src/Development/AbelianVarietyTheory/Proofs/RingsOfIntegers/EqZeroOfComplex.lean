module

public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsFramedPointBaseChangeAlgHom
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedModuliAlgebraicLawsChartWeightIntegrality
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointReducedFromTestRing
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.IndepPts
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.DetAlg
import Development.AbelianVarietyTheory.Definitions.Jets.ExistsSecTieFOfTies
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ChartChg

@[expose] public section

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

namespace GlobalTheory.CoverRoot

theorem eq_zero_of_complex {K : Type} [Field K] (σ : K →+* ℂ) (p : TRing K) (r : p.R)
    (h : ∀ χ : p.R →ₐ[K] CAt σ, χ r = 0) : r = 0 := by
  refine ReciprocityTheory.ChartRestriction.G.TB.detAlg_holds K p.n p.I p.rad r fun L _ _ _ ψ => ?_
  letI : Algebra K ℂ := σ.toAlgebra
  let e : L →ₐ[K] ℂ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  have h2 : e (ψ r) = 0 := h (e.comp ψ)
  exact (map_eq_zero_iff e e.injective).mp h2

theorem value_pow_eq_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n) (Cls : Type) [CommGroup Cls] [Finite Cls] (δ : Cls →* d.c₂.Fˣ) (gdet : FrPt d.Xo₂ d.c₂ (CAt d.c₂.F.val.toRingHom) → Cls), CMP Xo c d _ Cls δ gdet false → ∃ m₀ : ℕ, 0 < m₀ ∧ ∀ (k : Type) [Field k] [Algebra d.c₂.F k] (y₂ : FrPt d.Xo₂ d.c₂ k), evR d.Xo₂ d.c₂ d.cδ y₂ ^ m₀ = 1 := by
  intro E _ _ _ H Dw l Xo c n d Cls _ _ δ gdet h
  have hL : Laws := GlobalTheory.firstFiveLaws.1
  have hWD := (GlobalTheory.Frames.algebraic_laws hL.secBaseChange E H Dw d.l₂ d.Xo₂ d.c₂).2.2.1
  have hnat := h.1.1
  refine ⟨Nat.card Cls, Nat.card_pos, fun k _ _ y₂ => ?_⟩
  obtain ⟨p, φ, y', hy⟩ := GlobalTheory.Frames.allTest_of_secBaseChange hL.secBaseChange E H Dw d.l₂ d.Xo₂ d.c₂ k y₂
  have key : d.cδ p y' ^ Nat.card Cls - 1 = 0 := by
    refine eq_zero_of_complex d.c₂.F.val.toRingHom p _ fun χ => ?_
    obtain ⟨z, hz⟩ := GlobalTheory.FramedBaseChange.exists_frMap hL E H Dw d.l₂ d.Xo₂ d.c₂ _ _ χ y'
    have e1 : evR d.Xo₂ d.c₂ d.cδ z = χ (d.cδ p y') :=
      ReciprocityTheory.ChartRestriction.G.PullbackSections.evalAt_eq_of _ _ hWD d.cδ hnat p χ y' z hz
    have e2 := h.2 z
    rw [map_sub, map_pow, map_one, ← e1, e2, ← map_pow, if_neg (by simp), ← Units.val_pow_eq_pow_val, ← map_pow,
      pow_card_eq_one', map_one, Units.val_one, map_one, sub_self]
  have e3 : evR d.Xo₂ d.c₂ d.cδ y₂ = φ (d.cδ p y') :=
    ReciprocityTheory.ChartRestriction.G.PullbackSections.evalAt_eq_of _ _ hWD d.cδ hnat p φ y' y₂ hy
  rw [e3, ← map_pow, sub_eq_zero.mp key, map_one]

end GlobalTheory.CoverRoot
