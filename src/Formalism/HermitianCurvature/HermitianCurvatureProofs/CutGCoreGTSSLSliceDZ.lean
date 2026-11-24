module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTSSLocalCut
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

theorem second_shift_slice_derivative : GTSSLSliceDZ := by
  intro Wp Wq _ _ _ _ _ _ P Bs hpl T hT Φ Φ' c c' hc hc' hEq ζ hζ
  obtain ⟨n, A, -, hTA⟩ := hT
  have hTT : Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' = P.TT := by
    rw [hpl.2.2.2.1, hpl.2.2.2.2.1]; rfl
  have hU : IsOpen (Ann P) := isOpen_lt continuous_const Complex.continuous_normSq
  have hq : ((c, ζ) : (Fin P.r → ℂ) × ℂ) ∈ NF.QR P.k P.r Bs.z Bs.z' := ⟨hc, by rw [hTT]; exact hζ⟩
  have hq' : ((c', ζ) : (Fin P.r → ℂ) × ℂ) ∈ NF.QR P.k P.r Bs.z Bs.z' := ⟨hc', by rw [hTT]; exact hζ⟩
  have hev : (fun ζ' => NF.radR P.k P.r Bs.z Bs.z' Bs.μsec (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) (c, ζ')) =ᶠ[nhds ζ]
      (fun ζ' => NF.radR P.k P.r Bs.z Bs.z' Bs.μsec (Φ' : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) (c', ζ')) := by
    filter_upwards [hU.mem_nhds hζ] with ζ' hζ'
    have m : ((c, ζ') : (Fin P.r → ℂ) × ℂ) ∈ NF.QR P.k P.r Bs.z Bs.z' := ⟨hc, by rw [hTT]; exact hζ'⟩
    have m' : ((c', ζ') : (Fin P.r → ℂ) × ℂ) ∈ NF.QR P.k P.r Bs.z Bs.z' := ⟨hc', by rw [hTT]; exact hζ'⟩
    unfold NF.radR
    rw [Set.indicator_of_mem m, Set.indicator_of_mem m']
    exact hEq ζ' hζ'
  have e1 : NF.radR P.k P.r Bs.z Bs.z' Bs.μsec (T Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) (c, ζ) =
      (T Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (NF.muZ P.k P.r Bs.μsec ζ) := by
    unfold NF.radR; rw [Set.indicator_of_mem hq]
  have e2 : NF.radR P.k P.r Bs.z Bs.z' Bs.μsec (T Φ' : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) (c', ζ) =
      (T Φ' : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c' (NF.muZ P.k P.r Bs.μsec ζ) := by
    unfold NF.radR; rw [Set.indicator_of_mem hq']
  have h1 := hTA Φ (c, ζ) hq
  have h2 := hTA Φ' (c', ζ) hq'
  dsimp only at h1 h2
  rw [← e1, ← e2, h1, h2]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [(hev.iteratedFDeriv ℝ j).eq_of_nhds]

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
