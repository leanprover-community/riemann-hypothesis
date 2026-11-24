module

public import Formalism.SharpRestriction.LevelLetterCocycles.HerrClassFieldOfNorms
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineAndDecompletion
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemFixingSubgroupMaxUnramifiedOfMemLocalGalois
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.T2SpaceLocLatV
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitVectorOfUnitFor
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct

namespace GlobalTheory.HerrExtClass


set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 4000000 in
theorem herr_extension_class_formula : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), Formalism.MainNotions.HerrComplexNaturality.HerrExtensionClass D HW F := by
  intro D HW F
  unfold Formalism.MainNotions.HerrComplexNaturality.HerrExtensionClass Formalism.MainNotions.RamifiedCoefficientChains.adm16
  intro l _ K s LL h
  show Formalism.MainNotions.RamifiedCoefficientChains.HerrExt ((HW l).W K s LL h)
  have hA := GlobalTheory.Decompl.fontaine_and_decompletion D HW F
  have hU := GlobalTheory.WachUnit.unitVector D HW F l K s LL h
  obtain ⟨e, e₀, hspan, hT, hj, hN, hEE, hφ, hγ, htf⟩ := hU
  refine ⟨e, (e₀ : ((HW l).W K s LL h).one.V), ?_, ?_, ?_⟩
  · exact ⟨by rw [hN]; exact Submodule.subset_span rfl, hN, hEE, hφ, hγ, hT⟩
  · intro T Tp ι π κ hκ hcoc x c hx w h1 h2
    obtain ⟨hS, t, htT, hπt, hκt⟩ := hcoc
    let yt : ↥Tp.L.T := ⟨_, Tp.L.T.smul_mem c htT⟩
    let z : ↥((HW l).W K s LL h).one.L.T := ⟨_, ((HW l).W K s LL h).one.L.T.smul_mem c e₀.2⟩
    have hz : (z : ((HW l).W K s LL h).one.V) = π.f (yt : Tp.V) := by
      have := (π.f.restrictScalars ↥(OL LL)).map_smul c t
      simp only [LinearMap.restrictScalars_apply] at this
      rw [this, hπt]
    have he : (((F l).E K s LL h).tie).jD ((HW l).W K s LL h).one (((HW l).W K s LL h).map π x) = (1 : RW LL) ⊗ₜ[↥(OL LL)] z := by
      rw [hx, LinearMap.map_smul, hj, TensorProduct.smul_tmul', TensorProduct.smul_tmul]
      rfl
    have hcκ := (latticeCocycles T.L).smul_mem c hκ
    let cr : ↥(latticeCocycles (resLat T ((HW l).W K s LL h).GKs)) := ⟨_, Formalism.MainNotions.DeltaInvariantLattices.resFun_Z1T _ T _ hcκ⟩
    have hc : ∀ g : ↥((HW l).W K s LL h).GKs, ι.f ((cr : ↥((HW l).W K s LL h).GKs → T.V) g) = Tp.ρ (g : ↥(GK K)) (yt : Tp.V) - (yt : Tp.V) := by
      intro g
      have e1 := (ι.f.restrictScalars ↥(OL LL)).map_smul c (κ (g : ↥(GK K)))
      have e2 := ((Tp.ρ (g : ↥(GK K))).restrictScalars ↥(OL LL)).map_smul c t
      simp only [LinearMap.restrictScalars_apply] at e1 e2
      simp only [cr, yt, Formalism.MainNotions.DeltaInvariantLattices.resFun, LinearMap.funLeft_apply, Pi.smul_apply]
      rw [e1, hκt, e2]
      exact @smul_sub _ _ _ Tp.modO.toDistribMulAction.toDistribSMul c ((Tp.ρ (g : ↥(GK K))) t) t
    have key := GlobalTheory.Cyc.dict_ext_Ks D HW F hA l K s LL h T Tp ((HW l).W K s LL h).one ι π hS
      ((HW l).W K s LL h).one_triv yt z x hz he w h1 h2 cr hc
    refine Eq.trans key ?_
    unfold Formalism.MainNotions.RamifiedCoefficientChains.clsK Formalism.MainNotions.DeltaInvariantLattices.res
    rw [Submodule.mapQ_apply, ← Submodule.Quotient.mk_smul]
    congr 1
  · intro _ hp2 T Tp ι π κ hκ hcoc x c hx hδ w h1 h2
    obtain ⟨hS, t, htT, hπt, hκt⟩ := hcoc
    let yt : ↥Tp.L.T := ⟨_, Tp.L.T.smul_mem c htT⟩
    let z : ↥((HW l).W K s LL h).one.L.T := ⟨_, ((HW l).W K s LL h).one.L.T.smul_mem c e₀.2⟩
    have hz : (z : ((HW l).W K s LL h).one.V) = π.f (yt : Tp.V) := by
      have := (π.f.restrictScalars ↥(OL LL)).map_smul c t
      simp only [LinearMap.restrictScalars_apply] at this
      rw [this, hπt]
    have he : (((F l).E K s LL h).tie).jD ((HW l).W K s LL h).one (((HW l).W K s LL h).map π x) = (1 : RW LL) ⊗ₜ[↥(OL LL)] z := by
      rw [hx, LinearMap.map_smul, hj, TensorProduct.smul_tmul', TensorProduct.smul_tmul]
      rfl
    have hcκ := (latticeCocycles T.L).smul_mem c hκ
    let cr : ↥(latticeCocycles T.L) := ⟨_, hcκ⟩
    have hc : ∀ g : ↥(GK K), ι.f ((cr : ↥(GK K) → T.V) g) = Tp.ρ g (yt : Tp.V) - (yt : Tp.V) := by
      intro g
      have e1 := (ι.f.restrictScalars ↥(OL LL)).map_smul c (κ g)
      have e2 := ((Tp.ρ g).restrictScalars ↥(OL LL)).map_smul c t
      simp only [LinearMap.restrictScalars_apply] at e1 e2
      simp only [cr, yt, Pi.smul_apply]
      rw [e1, hκt, e2]
      exact @smul_sub _ _ _ Tp.modO.toDistribMulAction.toDistribSMul c ((Tp.ρ g) t) t
    have hi : Formalism.MainNotions.LocalSituation.ell (Formalism.MainNotions.LocalSituation.sit D.loc HW l (D.locA l) K s LL h) = 2 → ∃ i : ↥K.1, i ^ 2 = -1 :=
      fun h2' => absurd h2' hp2
    have key := GlobalTheory.ExtDict.dict_K D HW F hA l K s LL h hi T Tp ((HW l).W K s LL h).one ι π hS
      ((HW l).W K s LL h).one_triv yt z x hz he hδ w h1 h2 cr hc
    refine Eq.trans key ?_
    unfold Formalism.MainNotions.RamifiedCoefficientChains.clsK
    rw [← Submodule.Quotient.mk_smul]
    rfl

end GlobalTheory.HerrExtClass
