module

public import Formalism.HermitianCurvature.MemParahoricTimesPrincipalCongruenceIff
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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

noncomputable section

namespace Formalism.L2.SG.Pf.NcCut

open Formalism.FourierDecayAlt.S3

variable {P : Type} [Fintype P] (B : MassData P)

theorem MM_eq (hP : B.Pos) (hO : B.InOrdinary) (hT : B.InTyped) :
    B.MM = B.unitLevelVolume * B.μK * B.μKnat / (B.μS * B.μS') := by
  obtain ⟨hp, -, -, -, -, hU0, -⟩ := hP
  have h0 : B.Mo = B.localVolumeArchimedean * (B.μKo * B.μKo) / (B.μSo * B.μSo') := by
    have h := hO
    unfold MassData.InOrdinary at h
    rw [div_eq_iff hU0.ne'] at h
    rw [h]
    ring
  have h1 : ∀ p, B.Mp p = B.localVolumeAtPlace p * (B.μKp p * B.μKnatp p) / (B.μSp p * B.μSp' p) := by
    intro p
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hU⟩ := hp p
    have h := (hT p).1
    rw [div_eq_iff hU.ne'] at h
    rw [h]
    ring
  unfold MassData.MM MassData.unitLevelVolume MassData.μK MassData.μKnat MassData.μS MassData.μS'
  simp only [h0, h1, Finset.prod_div_distrib, Finset.prod_mul_distrib]
  rw [div_mul_div_comm]
  congr 1 <;> ring

theorem normalizing_constant_eq (hP : B.Pos) (hM : B.InMass) (hMs : B.InMasses) (hL : B.InLevelS) (hO : B.InOrdinary)
    (hT : B.InTyped) (hV : B.volNa = 1 ∧ B.volNa' = 1) :
    B.n0c = B.volB / B.volHa * B.Coo * B.volH * B.volN * B.volN' * (B.unitLevelVolume / B.volZZ) * B.μKnat / B.μH' := by
  have hMM := MM_eq B hP hO hT
  obtain ⟨hp, hKo, -, -, -, -, hH, hH', -, -, hN, hN', hZZ, -, -, -, hHa, -, -, -, hB, hVH, -, -, -,
    hCoo, -, -, -, hr0, -⟩ := hP
  obtain ⟨hρ, hNa, -, hNa'⟩ := hMs
  obtain ⟨hS, -, hS', -⟩ := hL
  have hK : 0 < B.μK := by
    unfold MassData.μK
    exact mul_pos hKo (Finset.prod_pos fun p _ => (hp p).2.2.2.2.2.1)
  have hvN : B.volN = 1 / B.μN := by
    rw [eq_div_iff hN.ne', ← hNa, hV.1]
  have hvN' : B.volN' = 1 / B.μN' := by
    rw [eq_div_iff hN'.ne', ← hNa', hV.2]
  have hM' : B.n0c * B.ρ0 = B.AA := hM
  unfold MassData.AA at hM'
  rw [hMM, hS, hS'] at hM'
  have hn := eq_div_of_mul_eq hr0.ne' hM'
  rw [hn, hρ, hvN, hvN']
  have h1 := hK.ne'
  have h2 := hH.ne'
  have h3 := hH'.ne'
  have h4 := hN.ne'
  have h5 := hN'.ne'
  have h6 := hZZ.ne'
  have h7 := hHa.ne'
  have h8 := hVH.ne'
  field_simp

theorem nc_iff (hP : B.Pos) (hM : B.InMass) (hMs : B.InMasses) (hL : B.InLevelS) (hO : B.InOrdinary)
    (hT : B.InTyped) (hV : B.volNa = 1 ∧ B.volNa' = 1) (c ng kap : ℝ) (hkap : kap ≠ 0) :
    c = B.n0c * ng / (B.al * kap) ↔
      c * B.al * kap = B.volB / B.volHa * B.Coo * B.volH * B.volN * B.volN' * (B.unitLevelVolume / B.volZZ) *
        B.μKnat / B.μH' * ng := by
  rw [normalizing_constant_eq B hP hM hMs hL hO hT hV]
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hal, -⟩ := hP
  rw [eq_div_iff (mul_ne_zero hal.ne' hkap)]
  constructor <;> intro h <;> linear_combination h

end Formalism.L2.SG.Pf.NcCut
