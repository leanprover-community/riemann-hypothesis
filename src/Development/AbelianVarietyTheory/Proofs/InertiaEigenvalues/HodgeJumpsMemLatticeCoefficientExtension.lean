module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InclIntegral
public import Formalism.AdmissibleDesigns.InvariantsEqBotIff
public import Formalism.SharpRestriction.LevelLetterCocycles.MatOfEquiv
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BaseCoef

namespace GlobalTheory.BaseCoef

theorem bot_emb_factor {l : ℕ} [Fact l.Prime] {LL LL' : FinExt l} (hL : LL.1 ≤ LL'.1)
    (τ' : ↥(Formalism.MainNotions.ElementDenominator.qlExt l).1 →ₐ[ℚ_[l]] ↥LL'.1) :
    ∃ τ : ↥(Formalism.MainNotions.ElementDenominator.qlExt l).1 →ₐ[ℚ_[l]] ↥LL.1, τ' = (incl hL).comp τ := by
  refine ⟨IntermediateField.inclusion (bot_le : (⊥ : IntermediateField ℚ_[l] _) ≤ LL.1), ?_⟩
  refine AlgHom.ext fun x => ?_
  obtain ⟨c, hc⟩ := IntermediateField.mem_bot.1 (show x.1 ∈ (⊥ : IntermediateField ℚ_[l] _) from x.2)
  have hx : x = algebraMap ℚ_[l] _ c := Subtype.ext hc.symm
  rw [hx, AlgHom.commutes, AlgHom.commutes]




theorem jumpsInV_extLat : ∀ (l : ℕ) [Fact l.Prime] (Pl : LocPrime l) (K' : FinExt l) (h : (Formalism.MainNotions.ElementDenominator.qlExt l).1 ≤ K'.1) (hN : (GKin h).Normal) (hF : (GKin h).FiniteIndex) (hS : ∀ (g : Gl l) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'), (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)).actB g (algebraMap ↥(K0 K') Pl.R.B c) = algebraMap ↥(K0 K') Pl.R.B c') (LL LL' : FinExt l) (hL : LL.1 ≤ LL'.1) (T : LocLat (Gl l) ℚ_[l] ↥LL.1 ↥(OL LL)) (k : ℕ) (b : Module.Basis (Fin k) ↥LL.1 T.V) (hb : IsLatBasis T b) (U : Set ℤ), (∀ τ, JumpsInV (pc Pl h hN hF hS).PD T.ρ τ U) → ∀ τ, JumpsInV (pc Pl h hN hF hS).PD (extLat hL T b hb).ρ τ U := by
  intro l _ Pl K' h hN hF hS LL LL' hL T k b hb U H τ' a ha
  obtain ⟨τ, rfl⟩ := bot_emb_factor hL τ'
  refine H τ a ?_
  have e1 := Formalism.MainNotions.N.K.Norm.isJumpV_congr (pc Pl h hN hF hS).PD b.equivFun
    (Formalism.MainNotions.UnusedSlot80.BCW.matOf_equiv b T.ρ) τ a
  have e2 := Formalism.MainNotions.N.GlobalTheory.coefficient_jump_general (pc Pl h hN hF hS).PD (incl hL)
    (Formalism.MainNotions.UnusedSlot80.BCW.matOf b T.ρ) τ a
  exact e1.2 (e2.2 ha)

end GlobalTheory.BaseCoef
