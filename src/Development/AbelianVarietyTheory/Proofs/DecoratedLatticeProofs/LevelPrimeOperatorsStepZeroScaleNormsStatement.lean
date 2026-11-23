module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.DoubleCollapse
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsTransportAdelicCorrection
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelPrimeOperatorsStepZeroScaleNorms
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.FinPl GlobalTheory.SeeSaw ValuativeRel IsLocalRing
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.levelPrime_operators_stepZero_scale_norms : ∀ (D : D7) (u : D.what₂.Word) (F : Formalism.L2.Forms.Forms0 D u) (θ : InfFam D), IsInfFam θ → RamUnitary D → CoCpt (D.sp.X 0) → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt D k) (I : List ι) (q : Unif k) (χ : ι → AddChar k Circle) (hχ : ∀ i, HasConductor (χ i) 1) (β : ∀ i, Frame (p i) (D.sp.X 0) (Fin (D.sp.X 0).rank)) (Q : ι → Pair k (Fin (D.sp.X 0).rank)), I.Nodup → (Function.Injective fun i => (p i).v) → (∀ (φ : D.what₂.Mu u) y i, RamAt (β i) (Q i) ((GlobalTheory.Core.Mi.chart0 F).rd θ (D.eMu u φ).1 y)) → ∀ η : ι → 𝓀[k]ˣ, (∀ φ : D.what₂.Mu u, ∃ φ' : D.what₂.Mu u, ∀ y, (GlobalTheory.Core.Mi.chart0 F).rd θ (D.eMu u φ').1 y = I.foldr (fun i f => sOp (β i) (Q i) q (resChar (χ i) (hχ i) q) (η i) f) ((GlobalTheory.Core.Mi.chart0 F).rd θ (D.eMu u φ).1 y)) → ∃ (S : D.what₂.Mu u ≃ₗ[ℂ] D.what₂.Mu u) (r : ℝ), 0 < r ∧ (∀ φ, ‖S φ‖ = r * ‖φ‖) ∧ ∀ φ y, (GlobalTheory.Core.Mi.chart0 F).rd θ (D.eMu u (S φ)).1 y = I.foldr (fun i f => sOp (β i) (Q i) q (resChar (χ i) (hχ i) q) (η i) f) ((GlobalTheory.Core.Mi.chart0 F).rd θ (D.eMu u φ).1 y) := by
  first | exact @GlobalTheory.RamStepZero.opsStepZero_norm | exact GlobalTheory.RamStepZero.opsStepZero_norm | (intros; apply GlobalTheory.RamStepZero.opsStepZero_norm <;> assumption)
