module

public import Formalism.LocalToGlobal.GlobalTheory.EqGlobOfHat
public import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.IsOrthCo
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsLatDlOfIsOrthCo
import Formalism.LocalRingCardinality.DataHost
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LocSpBot
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.MemMoveLevUloc
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.WittFractionToCpAlgebraMap
import Formalism.LocalToGlobal.InertKernelTheory.SecondKernelEntrywiseLastLevel
import Formalism.LocalToGlobal.InertKernelTheory.StatementInt
import Formalism.LocalToGlobal.KernelLattices.TopLawQ
import Formalism.SharpRestriction.GrowthBounds.ChartComparison.NrmAMemAdForms
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.ToLEInvApply
import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.CoeffProdRename

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory

theorem smul_dualSet_latAd_mem {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E]
    [Algebra F E] (sp : Spaces R F E) {N : ℕ} (J : Matrix (Fin N) (Fin N) E)
    (hco : ∃ co, IsOrthCo (sp.cm.sig : E →+* E) J co) (T : ℕ) (Lb : Submodule (𝓞 E) (Fin N → E)) (hT : 0 < T)
    (hLb : Formalism.L2.GlobalTheoryTheory.Comp.IsLat Lb)
    (hdual : ∀ z ∈ dualSet (sp.cm.sig : E →+* E) J Lb, (T : E) • z ∈ Lb)
    (y : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (hy : y ∈ UPts sp.cm.sig J (FiniteAdeleRing (𝓞 F) F))
    (z : Fin N → E) (hz : z ∈ dualSet (sp.cm.sig : E →+* E) J (latAd y Lb)) :
    (T : E) • z ∈ latAd y Lb := by
  have hlat : latAd y Lb = Formalism.UG.CS.globLat y Lb := Submodule.span_eq (Formalism.UG.CS.globLat y Lb)
  set a : 𝓞 E := (T : 𝓞 E) with ha
  have ha0 : a ≠ 0 := by
    rw [ha]; exact_mod_cast hT.ne'
  have hsm : ∀ w : Fin N → E, a • w = (T : E) • w := by
    intro w
    rw [← algebraMap_smul E a w, ha, map_natCast]

  have hdl : ∀ w ∈ Formalism.L2.GlobalTheoryTheory.Comp.dl sp.cm.sig J Lb, a • w ∈ Lb := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem w hw => rw [hsm]; exact hdual w hw
    | zero => rw [smul_zero]; exact zero_mem _
    | add u v _ _ hu hv => rw [smul_add]; exact add_mem hu hv
    | smul c w _ hw => rw [smul_comm]; exact Lb.smul_mem c hw
  have hle : Ideal.span {a} • Formalism.L2.GlobalTheoryTheory.Comp.dl sp.cm.sig J Lb ≤ Lb := by
    refine Submodule.smul_le.2 fun r hr w hw => ?_
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hr
    rw [mul_smul]
    exact Lb.smul_mem c (hdl w hw)

  have hz' : z ∈ Formalism.UG.CS.globLat y (Formalism.L2.GlobalTheoryTheory.Comp.dl sp.cm.sig J Lb) := by
    rw [Formalism.L2.GlobalTheoryTheory.Comp.glob_dl sp.cm.sig J (GlobalTheory.isLat_dl_of_isOrthCo sp J hco) hLb y hy]
    rw [hlat] at hz
    exact Submodule.subset_span hz
  have h1 : a • z ∈ Ideal.span {a} • Formalism.UG.CS.globLat y (Formalism.L2.GlobalTheoryTheory.Comp.dl sp.cm.sig J Lb) :=
    Submodule.smul_mem_smul (Ideal.mem_span_singleton_self a) hz'
  have h2 := Formalism.L2.GlobalTheoryTheory.Comp.glob_mono y hle
    (Formalism.L2.GlobalTheoryTheory.Comp.smul_glob_le _ a y h1)
  rw [hlat, ← hsm]
  exact h2

end GlobalTheory
