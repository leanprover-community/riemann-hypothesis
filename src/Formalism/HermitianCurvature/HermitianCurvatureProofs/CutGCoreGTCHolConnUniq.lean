module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTCHolCut
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTConnGaugeA
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTSSTr
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

theorem connection_uniqueness_holds : GTCConnUniq := by
  intro Wp Wq _ _ _ _ _ _ P Bs X d hyp e he A B A' B' hAB hAB' hC hC' ρ ζ hζ
  obtain ⟨Φ, hΦ, -⟩ := SSTr.exists_tr P Bs hyp.1 hyp.2.1 e he (fun _ => (1 : MA.SmQ P.r P.TT))
  have h1 := (hC Φ ρ).1
  have h2 := (hC' Φ ρ).1
  rw [hΦ] at h1 h2
  simp only [mul_one] at h1 h2
  have h3 : fnZ P (A ρ) = fnZ P (A' ρ) := by
    have := h1.symm.trans h2
    exact add_left_cancel this
  rw [fnZ_eq_mk P (hAB ρ).1, fnZ_eq_mk P (hAB' ρ).1] at h3
  have hq : ((fun _ => (1 : ℂ), ζ) : (Fin P.r → ℂ) × ℂ) ∈ MA.Qset P.r P.TT :=
    ⟨fun _ => one_ne_zero, hζ⟩
  have := congrFun (congrArg Subtype.val h3) ⟨_, hq⟩
  exact this

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
