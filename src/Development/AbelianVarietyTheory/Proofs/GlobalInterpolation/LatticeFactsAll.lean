module

public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TranslateMomentsAll
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DeltaNeZero
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FieldIsoSelfDualAndPeriodLatticesAgree
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.InterTransport
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormalisedFamilyLatticeHypAndSmooth
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.QuadraticFormIntegralOfSelfDualPeriodLattices
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.IsAdmissibleFlagPairOfUnitriangularLeftAutomorph
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.StdOK
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LatIntZero

@[expose] public section

open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.MomN
open IsDedekindDomain Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Th1.H GlobalTheory.ThetaMove GlobalTheory.ThetaMove.SeamMoves Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

noncomputable section

namespace GlobalTheory.MomLat

theorem latticeFactsAll : GlobalTheory.MomT.LatticeFactsAll := by
  intro D X s cc δ B χ cD hX hs hcc hδ hχ a b ha hb
  have hL := GlobalTheory.ThetaMove.LatticeFacts.latAll B hcc hδ
  have hVm := B.vec_mem_ne hcc hδ (delta_ne_zero B) (B.stdOK hcc hδ) χ hχ
  obtain ⟨hsd, hlam⟩ := GlobalTheory.PeriodTransport.seam_lattices X D s cc δ B χ cD hs
  have hq := qIntAll_of_latAll D cc δ B hL
  have hadm : ∀ (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)), IsSdLat N → IsSdLat N' →
      TaylorLogMetric.admitted D a b (s.lat N) (s.lat N') := fun N N' h h' => ⟨ha, hb, hsd _ _ h, hsd _ _ h'⟩
  refine ⟨⟨delta_ne_zero B, Fintype.card_pos_iff.1 hX.f_pos, by simp, fun P hP => absurd hP (Finset.notMem_empty P),
    aa_fg s B χ cD, fun N N' h h' => ?_⟩, fun N N' h h' k => ?_⟩
  · obtain ⟨h1, h2, h3⟩ := (Transport.inter_transport _ _ (reidx s a b) (Formalism.L2.Ker.HV (ambOf s B χ cD).sc)
      (formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau a b) (alV (ambOf s B χ cD).d (ambOf s B χ cD).sc) (TaylorLogMetric.al D B.tor)
      (lam (ambOf s B χ cD) N N') (lam (ambOf s B χ cD) N N') (TaylorLogMetric.La D B.tor (s.lat N) (s.lat N'))
      (TaylorLogMetric.La D B.tor (s.lat N) (s.lat N')) 0 (form_reidx s _ a b) (hlam a b N N') (hlam a b N N')
      (fun x hx => by
        obtain ⟨m, hm⟩ := hq a b _ _ (hadm N N' h h') (reidx s a b x) ((hlam a b N N' x).1 hx)
        exact alV_eq s B x hm)
      (isHerm_formV _ _ _ _) (hL.1 a b _ _ (hadm N N' h h')).1 (hL.1 a b _ _ (hadm N N' h h')).2).1
    exact ⟨h3 (B.eNat χ a b (s.lat N) (s.lat N')) (hVm a b _ _ (hadm N N' h h')).1.2, h1, h2⟩
  · have hd : ContDiff ℂ (k : WithTop ℕ∞) (B.eNat χ a b (s.lat N) (s.lat N')) :=
      GlobalTheory.SCV.contDiff_of_differentiable (hVm a b _ _ (hadm N N' h h')).1.1 _
    exact hd.comp (reidx s a b).toLinearMap.toContinuousLinearMap.contDiff

end GlobalTheory.MomLat
