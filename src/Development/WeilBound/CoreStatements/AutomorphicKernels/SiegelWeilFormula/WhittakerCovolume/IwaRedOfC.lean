module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.WhitAtCOneIff
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.ParabolicLowerBlockZero
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

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.KWhit

open PositivityTheory.SiegelWeilFormula

theorem kFinK : KFinK := fun _ _ _ _ _ _ _ _ d Φ hΦ k hk => kfin_om d hΦ hk

theorem iwaRedC : IwaRedC := by
  intro hT c F E _ _ _ _ _ σ d Q hQs hQK hL Φ hΦ x nb lam 𝓖 hcd ε w hw T hTnd
  obtain ⟨p, t, hp, k, hk, rfl⟩ := d.ok.hgt.iwa x
  obtain ⟨n0, m0, β₀, hn, hm, rfl⟩ := par_decomp d p t hp
  have key := hL (d.om k Φ) (hQK Φ hΦ k hk) m0 hm nb lam 𝓖 hcd ε w hw T hTnd
  have e1 : (fun z => ∫ β, flat d.a (d.sec0 Φ) (s0 d.m d.n) z (w * nb β * (n0 * m0 * k)) *
      d.B.ψ (-d.tt (T.1.1 * β.1)) ∂lam) = fun z => d.B.ψ (d.tt (T.1.1 * β₀)) *
      ∫ β, flat d.a (d.sec0 (d.om k Φ)) (s0 d.m d.n) z (w * nb β * m0) * d.B.ψ (-d.tt (T.1.1 * β.1)) ∂lam := by
    funext z
    rw [← int_n d nb lam 𝓖 hcd T w n0 m0 β₀ hn]
    congr 1
    funext β
    rw [show w * nb β * (n0 * m0 * k) = (w * nb β * (n0 * m0)) * k by simp only [mul_assoc]]
    simp only [flat, a_mul_K d _ k hk, section_mul_weil_action]
  have e2 : d.orb T (d.om (n0 * m0 * k) Φ) = d.B.ψ (d.tt (T.1.1 * β₀)) * d.orb T (d.om m0 (d.om k Φ)) := by
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply]
    exact orb_n hT d T (om_mem_sch d _ (om_mem_sch d _ (hQs Φ hΦ))) n0 β₀ hn
  show HolValueAt _ _ _
  rw [e1, e2, mul_left_comm]
  exact holValueAt_const_mul _ key

end PositivityTheory.SiegelWeilFormula.KWhit

end
