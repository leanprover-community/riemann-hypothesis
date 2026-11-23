module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ChainParSucc
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HermitianAdjointExistsUniqueOfPosDef
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemRangeAdjointOfMemSpanEvaluationValues
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
import Mathlib.Tactic.Linter.HaveILetI
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

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.EvenOnto

theorem pet_val_sum {D : D7} {c : Com D} {s : PiLocalization₂ D} {ipD : SmT s.M →ₗ[ℂ] SmT s.M →ₗ⋆[ℂ] ℂ}
    {ip : s.CC c →ₗ[ℂ] s.CC c →ₗ⋆[ℂ] ℂ} (h : IsMet c s ipD ip) (y : s.CC c) (w : SmT s.M) (n : ℕ)
    (ys : Fin n → s.CC c) (ws : Fin n → SmT s.M) :
    s.pet (PiLocalization₂.val y w) (∑ i, PiLocalization₂.val (ys i) (ws i)) = ∑ i, ip y (ys i) * ipD w (ws i) := by
  have hs : ∀ i, s.pet (PiLocalization₂.val y w) (PiLocalization₂.val (ys i) (ws i)) = ip y (ys i) * ipD w (ws i) :=
    fun i => h.schur y (ys i) w (ws i)
  rw [← Finset.sum_congr rfl (fun i _ => hs i)]

  simp only [PiLocalization₂.pet, Lift.pet, Finset.sum_apply, map_sum, Finset.mul_sum]
  exact integral_finsetSum _ (fun i _ => h.integ y (ys i) w (ws i))

theorem stepUp : ∀ D : D7, FinDim D → ParOfVal D → UpSpan D → UpAdj D → UpPar D → UpNe D → StepUp D := by
  intro D hFin hPV hSpan hAdj hPar hNe
  intro c hc k hk s s' hs hs' p hp ipD ip ipD' ip' hM hM' u B hB hL
  have hk' : k + 1 ≤ c.m := hk
  haveI : FiniteDimensional ℂ (s'.CC c) := hFin c hc (k + 1) hk' s' hs'
  obtain ⟨x, hx, -⟩ := GlobalTheory.hermitian_adjoint_exists_unique (s.CC c) (s'.CC c) ip ip' hM'.herm hM'.pos p.io u
  obtain ⟨φ, v, hv, hF⟩ := hNe c hc k hk s s' hs hs' p hp u B hB hL
  have key := GlobalTheory.ChainOnto.value_of_adjoint_of_mem_span (GA D s'.V) (SmT s'.M) (s'.CC c) (s'.CC c).subtype s'.KF ipD' ip' s'.pet
    hM'.hermD hM'.posD hM'.herm hM'.pos (fun y w n ys ws => pet_val_sum hM' y w n ys ws) x
    (p.up φ (PiLocalization₂.val u v)) (fun w => ipD (p.It φ w) v) (hSpan c hc k hk s s' hs hs' p hp u φ v hv)
    (fun y w hw => by
      rw [hx y]
      exact (hAdj c hc k hk s s' hs hs' p hp u y φ v hv w hw).trans (hM.schur _ _ _ _)) hF
  obtain ⟨-, w₀, -, hFx⟩ := key
  have hPF := hPar c hc k hk s s' hs hs' p hp u B φ hB v hv hF
  have hFx' : p.up φ (PiLocalization₂.val u v) = PiLocalization₂.val x w₀ := hFx
  refine ⟨x, hx, hPV c hc (k + 1) hk' s' hs' x w₀ _ ?_ ?_⟩
  · rw [← hFx']; exact hF
  · rw [← hFx']; exact hPF

end GlobalTheory.EvenOnto
