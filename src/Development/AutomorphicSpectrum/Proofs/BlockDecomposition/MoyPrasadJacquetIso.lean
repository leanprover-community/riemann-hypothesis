module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.MoyPrasadJacquetIsoTrivial
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentralTorusContractsLowerStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFixedMkEqOfCommute
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FixedInjSmooth
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCompactParahoricSubgroupStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsOpenGx
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParahoricLeviUnipotentLowerStatement
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
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace GlobalTheory.CompanionTheory.MoyPrasadTop

open PositivityTheory.LowerBoundConstant GlobalTheory GlobalTheory.Published GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead Topology

theorem moyPrasadJacquetIso : GlobalTheory.Published.MoyPrasadJacquetIso := by
  intro k _ _ _ _ n s d e V _ _ π hπ
  refine ⟨mapsTo_fixed_jacU e π _, ?_, ?_⟩
  · intro v hv w hw h
    have h0 : (Submodule.Quotient.mk (v - w) : Jacquet π (unipRad k e)) = 0 := by
      rw [Submodule.Quotient.mk_sub]
      exact sub_eq_zero.2 h
    exact sub_eq_zero.1 (GlobalTheory.CompanionTheory.DepthZeroJac.fixed_inj_smooth k n s d e V π hπ.1 (v - w) (sub_mem hv hw) h0)
  · intro y hy
    obtain ⟨v, hv, hvy⟩ := GlobalTheory.CompanionTheory.JacquetCentral.exists_fixed_mk_eq_of_commute π hπ (Gx k e) (unipRad k e) (GlobalTheory.CompanionTheory.MoyPrasad.isOpen_Gx k n s d e)
      (GlobalTheory.T.isCompact_parahoric_subgroup k n s d e) (leviEmb k e) (leviEmb_mem_normalizer k e) ((Gx k e).comap (leviEmb k e))
      (fun _ hm => hm) (lowC k e) (GlobalTheory.T.parahoric_levi_unipotent_lower k n s d e)
      (fun U hU => by
        refine (GlobalTheory.T.central_torus_contracts_lower k n s d e U hU).imp ?_
        intro t ht
        exact ⟨fun m _ => ht.1 m, ht.2⟩) y hy
    exact ⟨v, hv, hvy⟩

end GlobalTheory.CompanionTheory.MoyPrasadTop

end
