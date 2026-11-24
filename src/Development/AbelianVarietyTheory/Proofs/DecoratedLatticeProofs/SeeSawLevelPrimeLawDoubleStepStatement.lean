module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SmallPair
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.VacOfShape
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawLevelPrimeLawDoubleStep
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel IsLocalRing GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.FinPl

theorem _root_.GlobalTheory.T.seeSawLevelPrimeLaw_doubleStep : ∀ (D : D7) (c : Comm D) (v : VCom c) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (o : TDat c k ι), c.Is → v.Is → ShapeOff v o → ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m), ∃ (ε : ι → 𝓀[k]ˣ) (op : BiOp (c.X j) (c.X (j + 1)) (c.X (j + 1 + 1))) (r : ι → ℝ) (e : ι → ℤ), (∀ i, 0 < r i) ∧ OpAt (· ∈ v.tP) op ∧ ∀ t : Tup c, t.Is → WeilOK (t := t) v → t.UnrOn (· ∈ v.tP) → ∀ Ψ₁ Ψ₂, Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· ∈ v.tP) Ψ₁ → Vac c.ψ _ _ (v.N (j + 1)) (v.N (j + 1 + 1)) (· ∈ v.tP) Ψ₂ → BiVacAt c.ψ (c.x j).L (c.x (j + 1)).L (c.x (j + 1 + 1)).L (· ∈ v.tP) (op.app c.ψ (c.ctr j σ h (t.sBF j (σ + 1) h) (t.sFB j σ h) Ψ₁ Ψ₂)) ∧ ∀ d d', CombAt (· ∉ v.tP) d → CombAt (· ∉ v.tP) d' → ∀ φ ∈ o.Ram j, c.bl j (t.kom j) (t.kom (j + 1)) φ (biComb c.ψ _ _ _ d d' (c.ctr j σ h (t.sBF j (σ + 1) h) (t.sFB j σ h) Ψ₁ Ψ₂)) = o.mono r e (t.sBF j (σ + 1) h).χW • c.bl j (t.kom j) (t.kom (j + 1)) (o.S (fun _ => ε) j φ) (biComb c.ψ _ _ _ d d' (biComb c.ψ _ _ _ (v.dT j) (v.dT (j + 1)) (op.app c.ψ (c.ctr j σ h (t.sBF j (σ + 1) h) (t.sFB j σ h) Ψ₁ Ψ₂)))) := by
  first | exact @GlobalTheory.LevPrimeMid.lawLevelPrime_double | exact GlobalTheory.LevPrimeMid.lawLevelPrime_double | (intros; apply GlobalTheory.LevPrimeMid.lawLevelPrime_double <;> assumption)
