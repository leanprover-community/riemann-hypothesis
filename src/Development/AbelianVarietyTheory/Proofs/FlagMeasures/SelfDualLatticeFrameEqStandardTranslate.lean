module

public import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsDualFamilyInSelfDualLatticeStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsInnerLatticeImageFrameQuotientStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsTotallyIsotropicDualFamilyInLatticeStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUnitaryFrameDualStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryImageStandardLatticeEqSelfDualLatticeStatement
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Formalism.SharpRestriction.CuspSpanNormBounds.Point

@[expose] public section

open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG GlobalTheory.LocOver
open scoped Classical

namespace GlobalTheory.StdLat

theorem eq_img_lamStd : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r : ℕ), ∀ (Fr : FrameD H r) (Λ : Submodule M.L.O V), H.IsSelfDual Λ → H.IsFrame Λ r Fr.f Fr.T → ∃ L : Submodule M.L.O (H.Wb Fr.f), Fr.IsInner L ∧ (L : Set (H.Wb Fr.f)) = H.Lset Λ Fr.f ∧ ∃ n ∈ Fr.N, (∀ b, n (Fr.f b) = Fr.f b) ∧ Λ = img n (Fr.LamStd L) := by
  intro F _ _ _ E _ _ _ _ M hM V _ _ H r Fr Λ hSD hFr
  obtain ⟨y, hyΛ, hyf⟩ := GlobalTheory.T.exists_dual_family_in_selfDual_lattice M hM H r Fr Λ hSD hFr
  have hy0 : ∀ (a : Fin r) (b : Fin (r + 1)), H.h (y a.castSucc) (Fr.f b) = if b = a.castSucc then 1 else 0 :=
    fun a b => hyf b a.castSucc
  obtain ⟨y', hy'Λ, hy'f, hy'y⟩ := GlobalTheory.T.exists_totallyIsotropic_dual_family_in_lattice M hM H r Fr Λ hSD hFr (fun a : Fin r => y a.castSucc) (fun a : Fin r => hyΛ _) hy0
  obtain ⟨n, hnU, hnf, hnes, hnX⟩ := GlobalTheory.T.exists_unitary_frame_dual' M H r Fr y' hy'f hy'y
  obtain ⟨L, hLset, hLin⟩ := GlobalTheory.T.exists_innerLattice_image_frame_quotient M hM H r Fr Λ hSD hFr y' hy'Λ hy'f
  have heΛ : ∀ a : Fin r, Fr.f a.castSucc ∈ Λ := fun a => hFr.1.1 _
  refine ⟨L, hLin, hLset, n, ?_, hnf, ?_⟩
  · apply Subgroup.subset_closure
    refine ⟨hnU, ?_, hnX⟩
    intro j _ v hv
    have hle : Fr.Fj j ≤ LinearMap.ker ((n : V →ₗ[E] V) - LinearMap.id) := by
      rw [FrameD.Fj, Submodule.span_le]
      rintro _ ⟨a, _, rfl⟩
      simp [FrameD.e, hnf]
    have h1 := hle hv
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply] at h1
    rw [show n v - v = 0 from h1]
    exact zero_mem _
  · exact GlobalTheory.T.unitary_image_standardLattice_eq_selfDual_lattice M H r Fr Λ hSD heΛ L hLset n hnU (fun a => hnf _) (fun a => by rw [hnes]; exact hy'Λ a) hnX

end GlobalTheory.StdLat
