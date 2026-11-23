module

public import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionGenericFiberPullbackLocalIsoStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFiberArithmeticVarietyIntegralProjectiveStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogNormSectionIntegrableMixedChernProjectiveStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernMeasureIntegralEqGenericFibreStatement
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
public import Development.AbelianVarietyTheory.Definitions.Divisors.ContinuousBcPt
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

namespace GlobalTheory.Mix

theorem intg_logSec_of_arithVar : GlobalTheory.Published.Principalisation → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (σ : k →+* ℂ) (L : Fin D → MLine p σ) (M : MLine p σ) (s : M.B.Sec), genericPoint X ∈ nonzeroLocus s → Intg L (M.logSec s) := by
  intro hP k _ X _ _ p D hX σ L M s hs
  have := hX.isDomain
  have := hX.finite
  have hσ : Function.Injective σ := by
    have hk : RingHom.ker σ = ⊥ := Ideal.eq_bot_of_comap_eq_bot (R := ℤ) (by
      ext n
      simp [Ideal.mem_comap, RingHom.mem_ker])
    exact (RingHom.injective_iff_ker_eq_bot σ).2 hk
  let K := FractionRing k
  obtain ⟨τ, rfl⟩ : ∃ τ : K →+* ℂ, σ = τ.comp (algebraMap k K) :=
    ⟨IsFractionRing.lift hσ, by ext a; simp⟩
  let G := Limits.pullback p (spMap (algebraMap k K))
  let j : G ⟶ X := Limits.pullback.fst _ _
  let q : G ⟶ Sp K := Limits.pullback.snd _ _
  have hp : IsPullback j q p (spMap (algebraMap k K)) := IsPullback.of_hasPullback _ _
  obtain ⟨hGi, hGn, hproj, hdim, hgen, -, hstalk, -, -⟩ := GlobalTheory.T.generic_fiber_arithmetic_variety_integral_projective k K X G p q j hp D hX
  obtain ⟨s', hs', -, -, hlog⟩ := GlobalTheory.T.exists_section_generic_fiber_pullback_local_iso k K X G p q j hp τ hstalk M s hs hgen
  have h1 := GlobalTheory.T.log_norm_section_integrable_mixedChern_projective hP K G q τ D hproj hdim (fun i => (L i).bc hp.w τ) (M.bc hp.w τ) s' hs'
  have h2 := ((GlobalTheory.T.mixedChernMeasure_integral_eq_genericFibre k K X G p q j hp τ D hX L).2 (M.logSec s)).1
  refine h2.1 ?_
  have e : (M.bc hp.w τ).logSec s' = fun y => M.logSec s (bcPt hp.w τ y) := funext hlog
  rwa [e] at h1

end GlobalTheory.Mix
