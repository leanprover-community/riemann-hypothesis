module

public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.DownKer

theorem kerA_down_left_inv : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (t : T) (i j : ℕ),
    i ≤ D.R.m → j < D.R.m → ∀ Ψ : WO (G.pS (.mu t i j)) (G.pT (.mu t i j)) → ℂ,
    IsThetaFunO W.ψ (G.pS (.mu t i j)) (G.pT (.mu t i j)) Ψ → ∀ h : GA D (G.V (.grid i j)),
    ∀ γ ∈ GQ (G.V (.grid i (j + 1))), ∀ g, W.kerA (.down t i j) Ψ (γ * g) h = W.kerA (.down t i j) Ψ g h := by
  intro D T L sc G W t i j hi hj Ψ hΨ h γ hγ g
  have hR : (Pair.mu t i j : Pair T).InRange D.R.m := ⟨hi, hj⟩
  have hw := W.om_is (.mu t i j) hR
  show (W.om (.mu t i j)) (h, γ * g) Ψ 0 = (W.om (.mu t i j)) (h, g) Ψ 0
  have e : ((h, γ * g) : GA D (G.pS (.mu t i j)) × GA D (G.pT (.mu t i j))) = (1, γ) * (h, g) := by
    simp
  rw [e, map_mul, Module.End.mul_apply]
  exact hw.om_aut 1 (one_mem _) γ hγ _ (hw.om_pres _ _ hΨ)

end GlobalTheory.DownKer
