module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdeleJoinZero
public import Formalism.LocalToGlobal.NumberFieldFamilies.ThetaCB
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsArchEquivEq
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

noncomputable section

namespace GlobalTheory.WeilL2Words.StdTheta

def negSum (F : Type) [Field F] [NumberField F] : mixedEmbedding.mixedSpace F →ₗ[ℝ] ℝ :=
  -(∑ w : {w : InfinitePlace F // w.IsReal}, (LinearMap.proj w).comp (LinearMap.fst ℝ _ _))

theorem negSum_apply (F : Type) [Field F] [NumberField F] (z : mixedEmbedding.mixedSpace F) :
    negSum F z = -∑ w, z.1 w := by
  simp [negSum]

theorem negSum_nondeg (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (z : mixedEmbedding.mixedSpace F)
    (hz : z ≠ 0) : ∃ u, negSum F (z * u) ≠ 0 := by
  have h1 : z.1 ≠ 0 := by
    intro h0
    apply hz
    refine Prod.ext h0 (funext fun w => absurd (IsTotallyReal.isReal w.1) ?_)
    exact InfinitePlace.not_isReal_iff_isComplex.2 w.2
  obtain ⟨w, hw⟩ := Function.ne_iff.1 h1
  refine ⟨(Pi.single w 1, 0), ?_⟩
  rw [negSum_apply]
  simpa [Pi.single_apply] using hw

theorem cmTypeComponents_sum_eq_realCoordinates_sum (D : D7) (x : Ainf D.host.F) :
    ∑ ρ, Formalism.L2.Fam.ThC.th0 D ρ (x ⊗ₜ[D.host.F] (1 : D.host.E)) =
      ((∑ w, (InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F x).1 w : ℝ) : ℂ) := by
  haveI := D.sp.cm.totReal
  have e1 : ∀ ρ, Formalism.L2.Fam.ThC.th0 D ρ (x ⊗ₜ[D.host.F] (1 : D.host.E)) =
      InfinitePlace.Completion.extensionEmbedding (GlobalTheory.AdelicU.placeOf D ρ) (x (GlobalTheory.AdelicU.placeOf D ρ)) := by
    intro ρ
    show Formalism.L2.Fam.ThC.projAt (tauE D ρ) (x ⊗ₜ[D.host.F] (1 : D.host.E)) = _
    rw [Formalism.L2.Fam.ThC.projAt_tmul, map_one, mul_one]
    rfl
  rw [Finset.sum_congr rfl fun ρ _ => e1 ρ,
    (GlobalTheory.AdelicU.placeOf_bijective D).sum_comp (fun w => InfinitePlace.Completion.extensionEmbedding w (x w)),
    Complex.ofReal_sum]
  refine (Fintype.sum_equiv (Equiv.subtypeUnivEquiv fun w : InfinitePlace D.host.F => IsTotallyReal.isReal w) _ _
    fun w => ?_).symm
  rw [InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
  exact InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply w.2 (x w.1)

theorem isStdInf_of_isStdChar : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    GlobalTheory.WeilL2Words.IsStdInf D.host.F ψ := by
  intro D ψ hψ
  haveI := D.sp.cm.totReal
  have h := Formalism.L2.Fam.ThC.allSome_fam.1 hψ.2
  refine ⟨negSum D.host.F, negSum_nondeg D.host.F, fun z => ?_⟩
  have hx := h ((InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F).symm z)
  rw [cmTypeComponents_sum_eq_realCoordinates_sum, RingEquiv.apply_symm_apply] at hx
  show psiInf D.host.F ψ ((InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F).symm z) = _
  rw [hx, negSum_apply]
  congr 1
  push_cast
  ring

end GlobalTheory.WeilL2Words.StdTheta
