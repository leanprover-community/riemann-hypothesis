module

public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory

set_option backward.isDefEq.respectTransparency false in
instance instWEqLBEtRings (R : Type) [CommRing R] : (Scheme.etaleTopology.{0}).WEqualsLocallyBijective (ModuleCat.{1} (ULift.{1} R)) := by
  have : EssentiallySmall.{1} Scheme.{0} := inferInstance
  exact GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _


set_option backward.isDefEq.respectTransparency false in
theorem etale_affine_of_mem {U : Scheme.{0}} {S : Sieve U} (hS : S ∈ Scheme.etaleTopology U) (u : U) :
    ∃ (V : Scheme.{0}) (j : V ⟶ U) (v : V), IsAffine V ∧ Etale j ∧ j v = u ∧ S j := by
  obtain ⟨𝒰, hle⟩ := Scheme.mem_grothendieckTopology_iff.1 hS
  have : Scheme.JointlySurjective (Scheme.precoverage.{0} @Etale) :=
    Scheme.instJointlySurjectivePrecoverage
  obtain ⟨i, y, hy⟩ := 𝒰.exists_eq u
  obtain ⟨k, w, hw⟩ := (𝒰.X i).affineCover.exists_eq y
  have hi : S (𝒰.f i) := hle _ _ (Presieve.ofArrows.mk i)
  have he : Etale (𝒰.f i) := 𝒰.map_prop i
  refine ⟨_, (𝒰.X i).affineCover.f k ≫ 𝒰.f i, w, inferInstance, inferInstance, ?_, S.downward_closed hi _⟩
  rw [Scheme.Hom.comp_apply, hw, hy]

set_option backward.isDefEq.respectTransparency false in
theorem ofRings_loc : ∀ (R : Type) [CommRing R]
    (M : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} R)) (U : Scheme.{0}),
    (∀ (x : Sec (ofRings R M) U) (u : U),
      ∃ (V : Scheme.{0}) (j : V ⟶ U) (v : V) (m : M.obj Γ(V, ⊤)),
        IsAffine V ∧ Etale j ∧ j v = u ∧ ofRings.sec M V m = Sec.res j x) ∧
    (∀ m : M.obj Γ(U, ⊤), ofRings.sec M U m = 0 → ∀ u : U,
      ∃ (V : Scheme.{0}) (j : V ⟶ U) (v : V),
        IsAffine V ∧ Etale j ∧ j v = u ∧ (M.map j.appTop).hom m = 0) ∧
    ∀ (V : Scheme.{0}) (j : V ⟶ U) (m : M.obj Γ(U, ⊤)),
      Sec.res j (ofRings.sec M U m) = ofRings.sec M V ((M.map j.appTop).hom m) := by
  intro R _ M U
  refine ⟨fun x u => ?_, fun m hm u => ?_, fun V j m => ?_⟩
  · have hS := Presheaf.imageSieve_mem Scheme.etaleTopology (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ M)) (U := op U) x
    obtain ⟨V, j, v, hV, hj, hv, ⟨m, hm⟩⟩ := etale_affine_of_mem hS u
    exact ⟨V, j, v, m, hV, hj, hv, hm⟩
  · have hS := Presheaf.equalizerSieve_mem Scheme.etaleTopology (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ M))
      (X := op U) m 0 (hm.trans (map_zero _).symm)
    obtain ⟨V, j, v, hV, hj, hv, h⟩ := etale_affine_of_mem hS u
    refine ⟨V, j, v, hV, hj, hv, ?_⟩
    have h' : ((Scheme.Γ ⋙ M).map j.op).hom m = ((Scheme.Γ ⋙ M).map j.op).hom 0 := h
    rw [map_zero] at h'
    exact h'
  · have := congrArg (fun f => f.hom m) ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ M)).naturality j.op)
    exact this.symm

end GlobalTheory
