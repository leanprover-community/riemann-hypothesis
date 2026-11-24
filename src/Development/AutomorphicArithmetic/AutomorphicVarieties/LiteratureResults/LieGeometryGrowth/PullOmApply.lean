module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullStmt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullHkSmooth
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullPbD
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

open UpperTheory.V.Lit.Geo
open scoped ContDiff

theorem UpperTheory.V.Lit.Geo.omApply :
    OmApply := by
  intro Γ V S _ _ _ _ d G W hW q
  refine ⟨fun w s p hp => ?_, fun w s p hp => ?_⟩
  · refine toOm_apply G (z := fun s => pb (flow (W s) 1) (w.1 s)) (fun s x hx => ?_) s hp
    have hx' : flow (W s) 1 x ∈ G.Y := (hW.field s).2 x hx 1 ⟨zero_le_one, le_rfl⟩
    have h1 : ContDiffAt ℝ ∞ (W s) x := (hW.field s).1.contDiffAt (G.isOpen.mem_nhds hx)
    have h2 : ContDiffAt ℝ ∞ (flow (W s) 1) x := contDiffAt_id.add (h1.const_smul (1 : ℝ))
    have h3 : ContDiffAt ℝ ∞ (w.1 s) (flow (W s) 1 x) := (w.2 s).1.contDiffAt (G.isOpen.mem_nhds hx')
    exact (pbD V V (Fin d → ℂ) q _ _ x h2 h3).1.contDiffWithinAt
  · exact toOm_apply G (z := fun s => hom (W s) (w.1 s))
      (fun s => (hkSmooth V (Fin d → ℂ) G.Y G.isOpen (W s) (hW.field s) q (w.1 s) (w.2 s).1).2.2.2) s hp
