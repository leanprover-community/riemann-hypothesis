module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicIwasawaDoubledGroupSelfDualLatticeStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingHeightAtRealPlaceLeOneStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelHeightFinitePlaceDoublingEmbeddingLeOneStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsOpenIsCompactLevelOffFinEmpty
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NsmulProjectionXColumnsMemSelfDualLattice
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated

@[expose] public section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.Core.Rk.IP
variable {D : D7} (A : HSp D) (L : Lat A) (a : GL (Fin A.rank) (AE D))

theorem hgtL_eq_prod (hL : IsSelfDualC A L) (ha : IsMaj A a) (g : GA D A) : hgtL A L a g = (∏ w, hgtArch D.sp.cm.sig (dblSp A).gram w (Formalism.UG.bc (compInf _ _ w) a)
      (ioH _ D.sp.cm.sig (gram_hdbl A) (projArch D.sp.cm.sig A.gram w g, 1))) *
      ∏ᶠ v, hgtFin D.sp.cm.sig (dblSp A).gram L v (ioH _ D.sp.cm.sig (gram_hdbl A) (proj D.sp.cm.sig A.gram v g, 1)) := by
  haveI : Submodule.IsFullLattice D.host.E L := GlobalTheory.ProjXCols.selfDual_isFullLattice A L hL
  have hI := GlobalTheory.T.adelicIwasawa_doubledGroup_selfDualLattice D A L a hL ha
  simpa only [hgtL, io, proj_ioH, projArch_ioH, map_one] using
    hI.hgtAd_eq (isCMExt_host D) (io A (g, 1))

theorem isOpen_openOff (hL : IsSelfDualC A L) (Sf : Finset (FinPl D)) : IsOpen (openOff A L Sf) := by
  haveI : Submodule.IsFullLattice D.host.E L := GlobalTheory.ProjXCols.selfDual_isFullLattice A L hL
  let H : Subgroup (GA D A) := ⨅ (v) (_ : v ∉ Sf), (stabLoc D.sp.cm.sig A.gram L v).comap (proj D.sp.cm.sig A.gram v)
  have hH : (H : Set (GA D A)) = openOff A L Sf := by
    ext g
    simp [H, openOff, Subgroup.mem_iInf, Subgroup.mem_comap]
  rw [← hH]
  refine Subgroup.isOpen_mono (H₁ := levelOpen D.sp.cm.sig A.gram L) (fun g hg => ?_) (isOpen_levelOpen _ _ _)
  simp only [H, Subgroup.mem_iInf, Subgroup.mem_comap]
  exact fun v _ => (mem_levelOpen.1 hg) v

theorem continuous_hgtL (hL : IsSelfDualC A L) (ha : IsMaj A a) : Continuous (hgtL A L a) := by
  haveI : Submodule.IsFullLattice D.host.E L := GlobalTheory.ProjXCols.selfDual_isFullLattice A L hL
  haveI := t2Space_adeleRing' (F := D.host.F)
  have hI := GlobalTheory.T.adelicIwasawa_doubledGroup_selfDualLattice D A L a hL ha
  exact (hI.continuous_hgtH continuous_absE (isCompact_KAd (isCMExt_host D))).comp
    ((continuous_io A).comp (continuous_id.prodMk continuous_const))

theorem hgtL_le_one (hL : IsSelfDualC A L) (ha : IsMaj A a) (g : GA D A) : hgtL A L a g ≤ 1 := by
  rw [hgtL_eq_prod A L a hL ha g]
  refine mul_le_one' (Finset.prod_le_one' fun w _ => ?_) ?_
  · have := GlobalTheory.T.doublingHeightAtRealPlace_le_one D A a ha w (projArch D.sp.cm.sig A.gram w g)
    simpa [GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtW] using this
  · by_cases hf : (Function.mulSupport fun v => hgtFin D.sp.cm.sig (dblSp A).gram L v
        (ioH _ D.sp.cm.sig (gram_hdbl A) (proj D.sp.cm.sig A.gram v g, 1))).Finite
    · rw [finprod_eq_prod _ hf]
      exact Finset.prod_le_one' fun v _ => GlobalTheory.T.siegelHeightFinitePlace_doublingEmbedding_le_one D A L hL v _
    · rw [finprod_of_infinite_mulSupport hf]

theorem hgtL_eq_prod_off (hL : IsSelfDualC A L) (ha : IsMaj A a) (Sf : Finset (FinPl D)) (g : GA D A)
    (hg : g ∈ openOff A L Sf) : (hgtL A L a g : ℝ) = (∏ w, GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtW A a w (projArch D.sp.cm.sig A.gram w g)) *
      ∏ v ∈ Sf, GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtV A L v (proj D.sp.cm.sig A.gram v g) := by
  haveI : Submodule.IsFullLattice D.host.E L := GlobalTheory.ProjXCols.selfDual_isFullLattice A L hL
  rw [hgtL_eq_prod A L a hL ha g]
  have hsub : (Function.mulSupport fun v => hgtFin D.sp.cm.sig (dblSp A).gram L v
      (ioH _ D.sp.cm.sig (gram_hdbl A) (proj D.sp.cm.sig A.gram v g, 1))) ⊆ (Sf : Set (FinPl D)) := by
    intro v hv
    by_contra hvS
    exact hv (hgtH_of_mem (continuous_absEv v) (isCompact_KFin v)
      ((ioH_mem_KFin (gram_hdbl A)).2 ⟨hg v hvS, one_mem _⟩))
  rw [finprod_eq_prod_of_mulSupport_subset _ hsub]
  push_cast
  rfl

theorem hgtL_props : ∀ (D : D7) (A : HSp D) (L : Lat A) (a : GL (Fin A.rank) (AE D)), IsSelfDualC A L → IsMaj A a → Continuous (hgtL A L a) ∧ (∀ g, 0 < hgtL A L a g ∧ hgtL A L a g ≤ 1) ∧ ∀ (Sf : Finset (FinPl D)), IsOpen (openOff A L Sf) ∧ ∀ g ∈ openOff A L Sf, (hgtL A L a g : ℝ) = (∏ w, GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtW A a w (projArch D.sp.cm.sig A.gram w g)) * ∏ v ∈ Sf, GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtV A L v (proj D.sp.cm.sig A.gram v g) := by
  intro D A L a hL ha
  exact ⟨continuous_hgtL A L a hL ha, fun g => ⟨hgtH_pos _, hgtL_le_one A L a hL ha g⟩,
    fun Sf => ⟨isOpen_openOff A L hL Sf, fun g hg => hgtL_eq_prod_off A L a hL ha Sf g hg⟩⟩

end GlobalTheory.Core.Rk.IP
