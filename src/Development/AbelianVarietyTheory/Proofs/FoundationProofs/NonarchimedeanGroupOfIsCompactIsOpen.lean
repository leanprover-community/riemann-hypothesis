module

import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNhdsFixOfContinuousCoefficients
public import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EventuallyAlgebraMapMemIntegers
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsOpenIsCompactLevelOffFinEmpty
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Algebra.ClopenNhdofOne
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Separation.Connected
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice

@[expose] public section

noncomputable section

namespace GlobalTheory.Doubling

open scoped TensorProduct NNReal Topology
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.AdelicU

theorem eq_one_of_forall_norm_pow_sub_one_le {A : Type} [NormedRing A] [NormedAlgebra ℂ A] {x : A}
    (h : ∀ m : ℕ, ‖x ^ m - 1‖ ≤ 1 / 2) : x = 1 := by
  apply GlobalTheory.SmoothFix.eq_one_of_pow_norm_sub_one_le_half <;> assumption

theorem nonarchimedeanGroup_of_isCompact_isOpen {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TotallyDisconnectedSpace H] {K : Subgroup H} (hc : IsCompact (K : Set H)) (ho : IsOpen (K : Set H)) :
    NonarchimedeanGroup H :=
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hc
  haveI : NonarchimedeanGroup K := ⟨fun U hU => by
    obtain ⟨N, hN⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one (isOpen_interior (s := U))
      (mem_interior_iff_mem_nhds.2 hU)
    exact ⟨N.toOpenSubgroup, hN.trans interior_subset⟩⟩
  NonarchimedeanGroup.nonarchimedean_of_emb K.subtype ho.isOpenEmbedding_subtypeVal

section General

variable {G : Type} [Group G] {K : Subgroup G} {Φ : G → ℂ}


variable [TopologicalSpace G] [ContinuousMul G]

end General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)

section Groups

variable {m : ℕ} (J : Matrix (Fin m) (Fin m) E)

theorem totallyDisconnectedSpace_GLoc (v : HeightOneSpectrum (𝓞 F)) : TotallyDisconnectedSpace (GLoc σ J v) := by
  haveI : TotallyDisconnectedSpace (Fv F v ⊗[F] E) := by
    obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (Fv F v)
    exact e.symm.totallyDisconnectedSpace
  haveI : TotallyDisconnectedSpace (Matrix (Fin m) (Fin m) (Fv F v ⊗[F] E)) :=
    inferInstanceAs (TotallyDisconnectedSpace (Fin m → Fin m → Fv F v ⊗[F] E))
  exact ⟨isTotallyDisconnected_of_image (f := fun g => (matHom _ σ J g).1)
    (Units.continuous_val.comp (isEmbedding_matHom _ σ J).continuous).continuousOn
    (Units.val_injective.comp (matHom_injective _ σ J)) (isTotallyDisconnected_of_totallyDisconnectedSpace _)⟩

theorem totallyDisconnectedSpace_GFin : TotallyDisconnectedSpace (GFin σ J) :=
  haveI := totallyDisconnectedSpace_GLoc σ J
  ⟨isTotallyDisconnected_of_image (f := fun g v => projFinLoc σ J v g)
    (continuous_pi fun v => continuous_projFinLoc σ J v).continuousOn
    (fun _ _ e => GFin_ext σ J (congrFun e)) (isTotallyDisconnected_of_totallyDisconnectedSpace _)⟩

theorem nonarchimedeanGroup_GLoc (v : HeightOneSpectrum (𝓞 F)) : NonarchimedeanGroup (GLoc σ J v) :=
  haveI := totallyDisconnectedSpace_GLoc σ J v
  haveI := isLattice_stdLattice (E := E) (n := m)
  nonarchimedeanGroup_of_isCompact_isOpen (isCompact_stabLoc σ J (stdLattice E m) v)
    (isOpen_stabLoc σ J (stdLattice E m) v)

theorem nonarchimedeanGroup_GFin : NonarchimedeanGroup (GFin σ J) :=
  haveI := totallyDisconnectedSpace_GFin σ J
  haveI := isLattice_stdLattice (E := E) (n := m)
  nonarchimedeanGroup_of_isCompact_isOpen (isCompact_levelOffFin σ J (stdLattice E m) ∅)
    (isOpen_levelOffFin_empty σ J (stdLattice E m))

variable {σ J}

end Groups

variable {σ} {n : ℕ} {Q : Matrix (Fin (n + n)) (Fin (n + n)) E} {L : Submodule (𝓞 E) (Fin n → E)}
  [Submodule.IsLattice E L]

section Record

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta

end Record

end GlobalTheory.Doubling

end
