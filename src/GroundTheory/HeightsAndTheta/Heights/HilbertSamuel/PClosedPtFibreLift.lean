module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsClosedPtFibreLift
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGradedSubmodules
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsClosedPtSkyscraper
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsLocIdealKer
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.AlgCechSt
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenSESStep
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.IsFieldIntersection

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

theorem ClosedPtFibreLift.proof (hG : GradedSubmodules.Statement) (hSES : KH.CechSESStatement)
    (hSky : ClosedPtSkyscraper.Statement) (hKer : LocIdealKer.Statement) : ClosedPtFibreLift.Statement := by
  intro S _ K _ _ ι _ _ M _ _ _ _ 𝓜 P d _ _ h𝓜 hP hH1 I hI x hx
  have hPh : IsMultiHomogIdeal P := hP.1.2.1
  obtain ⟨h𝓝', h𝓝''⟩ := (hG S K ι M 𝓜 h𝓜).2 P hPh

  have hyd : GenSESStep.locMap (KH.cellMon S I.1) (P • ⊤ : Submodule (MRingOver S ι) M).mkQ x ∈
      KH.locPart ι (quotGrading 𝓜 (P • ⊤ : Submodule (MRingOver S ι) M)) (KH.cellMon S I.1) d := by
    obtain ⟨m, t, a, ht, hm, rfl⟩ := GenSESStep.locPart_normal h𝓜 hx
    rw [GenSESStep.locMap_mk]
    exact GenSESStep.mk_mem_locPart _ t a ht ⟨m, hm, rfl⟩

  have hkill : ∀ p ∈ P, ∀ n : M ⧸ (P • ⊤ : Submodule (MRingOver S ι) M), p • n = 0 := by
    intro p hp n
    induction n using Submodule.Quotient.induction_on with
    | H m =>
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      exact Submodule.smul_mem_smul hp Submodule.mem_top

  obtain ⟨z'', hz'', hz''I⟩ := hSky S K ι _ _ P d h𝓝'' hP hkill I hI _ hyd

  have hg : KH.IsMGradedMap S ι (subGrading 𝓜 (P • ⊤ : Submodule (MRingOver S ι) M)) 𝓜
      (P • ⊤ : Submodule (MRingOver S ι) M).subtype := fun _ _ hm => hm
  have hh : KH.IsMGradedMap S ι 𝓜 (quotGrading 𝓜 (P • ⊤ : Submodule (MRingOver S ι) M))
      (P • ⊤ : Submodule (MRingOver S ι) M).mkQ := fun _ m hm => ⟨m, hm, rfl⟩
  obtain ⟨z, hz, hzmap⟩ := (hSES S K ι _ M _ _ 𝓜 _ _ _ h𝓝' h𝓜 h𝓝'' hg hh
    (Submodule.injective_subtype _) (Submodule.mkQ_surjective _)
    (by rw [Submodule.range_subtype, Submodule.ker_mkQ]) d 0).2.2.2.2.1 hH1 z'' hz''
  refine ⟨z, hz, ?_⟩
  have hzI : z I ∈ KH.locPart ι 𝓜 (KH.cellMon S I.1) d := Submodule.mem_pi.mp hz.1 I (Set.mem_univ _)

  refine (hKer S K ι M 𝓜 P (KH.cellMon S I.1) d h𝓜 hPh (fun _ ht => GenSESStep.cellMon_homog ht) _
    (sub_mem hx hzI)).2 ?_
  have e : GenSESStep.locMap (KH.cellMon S I.1) (P • ⊤ : Submodule (MRingOver S ι) M).mkQ (z I) = z'' I :=
    congrFun hzmap I
  rw [map_sub]
  change _ - GenSESStep.locMap (KH.cellMon S I.1) (P • ⊤ : Submodule (MRingOver S ι) M).mkQ (z I) = 0
  rw [e, hz''I, sub_self]

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
