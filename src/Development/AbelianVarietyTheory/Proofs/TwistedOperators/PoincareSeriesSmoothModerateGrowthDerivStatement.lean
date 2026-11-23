module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PoincareSeriesSmoothModerateGrowthDeriv
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

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical

theorem _root_.GlobalTheory.T.poincareSeries_smooth_moderateGrowth_deriv : GlobalTheory.Published.HarishChandraModules → ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (Λ : Lat V) (𝔪 : Ideal (𝓞 D.host.E)), IsSelfDualC V Λ → 𝔪 ≠ ⊥ → ∀ (v : ∀ τ, M.H τ), KDecay M v → ∀ c : GA D V, ∀ a : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KVec M, (poin θ M (congLev D.sp.cm V.gram Λ 𝔪) v c fun τ => a τ) ∈ GlobalTheory.Mem.AutSpace.SmFun θ V ∧ UnifModGrowth V θ (poin θ M (congLev D.sp.cm V.gram Λ 𝔪) v c fun τ => a τ) ∧ ∀ τ, ∀ X ∈ lieAt V τ, ∀ w : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ, (w : M.H τ) = dRep (M.rep τ) X (a τ) → (poin θ M (congLev D.sp.cm V.gram Λ 𝔪) v c fun τ' => Function.update a τ w τ') = Rder θ V τ X (poin θ M (congLev D.sp.cm V.gram Λ 𝔪) v c fun τ => a τ) := by
  first | exact @GlobalTheory.PoinDer.poin_smooth_growth_deriv | exact GlobalTheory.PoinDer.poin_smooth_growth_deriv | (intros; apply GlobalTheory.PoinDer.poin_smooth_growth_deriv <;> assumption)
