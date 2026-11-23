module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFinExt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodRingsGaloisActionLawsFrobeniusComm
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLogOnePlusKerThetaDeRhamPlusStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GaloisLogTeichmullerRatioEqAddKummerStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KerPEqSpanBetaStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KummerNotCoboundary

@[expose] public section

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.MemLoc GlobalTheory.Pst.StLat GlobalTheory.Pst.NoLog
open scoped Formalism.Per

namespace GlobalTheory.PMon

theorem exists_log_tilt_BdR : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI),
    ∃ u : P.R.BdR, ∀ g : GQ l, P.actQdR g u = u + P.ιB ((kummer P g : ℚ_[l]) • P.tB) := by
  intro l _ P AI T
  obtain ⟨Co, hC⟩ := GlobalTheory.MemLoc.FitsEx.exists_fits l P AI T
  obtain ⟨ϖ, hr⟩ := exists_tilt (lRoot l) (lRoot_succ l) l (lRoot_zero l)
  have hϖ : ϖ.untilt = ((l : ℕ) : Per.OC l) := Subtype.ext (by
    have := hr 0
    rw [lRoot_zero, map_natCast] at this
    exact this.trans (SubringClass.coe_natCast _ _).symm)
  obtain ⟨u, hu⟩ := GlobalTheory.T.exists_logOnePlus_kerTheta_deRhamPlus l (beta ϖ) (by
    rw [GlobalTheory.T.kerP_eq_span_beta_of_untilt_eq l ϖ hϖ]; exact Ideal.mem_span_singleton_self _)
  have hg := GlobalTheory.T.galois_logTeichmullerRatio_eq_add_kummer l P Co hC.ζ ϖ hr hϖ u hu
  have hct : ∀ g : GQ l, T.eD (P.ιB ((kummer P g : ℚ_[l]) • P.tB)) =
      algebraMap (Per.BdRp l) (Per.BdR l)
        (Co.j (algebraMap (Per.Ainf l) (Per.Acris l) (Per.zA l (kummer P g)) * Co.t)) := by
    intro g
    rw [hC.ι, Algebra.smul_def, map_mul, T.zB, hC.t, ← Co.ι_j]
    simp only [Core.tB, GlobalTheory.RingIface.zB_alg, map_mul]
  refine ⟨T.eD.symm (algebraMap (Per.BdRp l) (Per.BdR l) u), fun g => ?_⟩
  apply T.eD.injective
  rw [T.actD, RingEquiv.apply_symm_apply, map_add (f := _), RingEquiv.apply_symm_apply, hct]
  rw [show Per.σD g (algebraMap (Per.BdRp l) (Per.BdR l) u) =
    algebraMap (Per.BdRp l) (Per.BdR l) (Per.σDp g u) from GlobalTheory.MemLoc.ActLaws.σD_alg _ _, hg, map_add]

end GlobalTheory.PMon
