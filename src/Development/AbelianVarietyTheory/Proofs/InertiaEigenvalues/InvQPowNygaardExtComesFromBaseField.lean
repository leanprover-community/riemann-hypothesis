module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RestrictJumps
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SepOfHausdorff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachInclusionXQFrobenius
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.NL.CrystallineBase

noncomputable section

namespace GlobalTheory.NL.TransitionThirdCase


set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem jD_Qpow (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime]
    (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (T : Lt K LL) (m : ℕ)
    (x : ((HW l).W K s LL h).DD T) :
    ((F l).E K s LL h).tie.jD T (((HW l).W K s LL h).Q ^ m • x) =
      (inclR LL ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] (D.locA l).ξ)) ^ m • ((F l).E K s LL h).tie.jD T x := by
  let W := (HW l).W K s LL h
  let E := ((F l).E K s LL h).tie
  let a : AA K LL := W.Q ^ m
  let ξ : RA LL := (1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] (D.locA l).ξ
  let aE := @algebraMap (AA K LL) W.EE _ W.eeRing.toSemiring W.eeAlgA a
  have hQ : E.io W.Q = ξ := (GlobalTheory.NL.IoXQ.main D HW F l K s LL h).2.1
  have hscalar : E.ioE aE = (inclR LL ξ) ^ m :=
    (E.ioE_ext a).trans
      ((map_pow ((inclR LL).comp E.io) W.Q m).trans
        (congrArg (fun b : RA LL => (inclR LL b) ^ m) hQ))
  have hx := (@algebraMap_smul (AA K LL) _ W.EE W.eeRing.toSemiring W.eeAlgA
    (W.DD T) (W.ddAcg T).toAddCommMonoid (W.ddModE T) (W.ddModA T) (W.ddTowA T) a x).symm
  let smulRW := (@TensorProduct.leftHasSMul ↥(OL LL) (RW LL) _ _ (RW LL) ↥T.L.T _ _
    (Semiring.toModule (R := RW LL)).toDistribMulAction _ _ _).smul
  exact (congrArg (E.jD T) hx).trans
    ((E.jD_smul T aE x).trans (congrArg (fun b => smulRW b (E.jD T x)) hscalar))

private theorem image_map_refl {O R M : Type} [CommRing O] [AddCommGroup R] [Module O R]
    [AddCommGroup M] [Module O M] (S : Set (R ⊗[O] M)) :
    TensorProduct.map (LinearMap.id : R →ₗ[O] R) (LinearEquiv.refl O M).toLinearMap '' S = S := by
  rw [show TensorProduct.map (LinearMap.id : R →ₗ[O] R)
    (LinearEquiv.refl O M).toLinearMap = LinearMap.id from TensorProduct.map_id]
  exact Set.image_id S

private theorem transfer_preimage {A B C : Type} (f : A → C) (g : B → C)
    (u : A → A) (v : B → B) (k : C → C) (S : Set A) (S' : Set B)
    (hf : Function.Injective f) (hu : ∀ y, f (u y) = k (f y))
    (hR : Set.range g = Set.range f) (hN : g '' S' = f '' S)
    (y' : B) (hy' : v y' ∈ S') (hv : g (v y') = k (g y')) :
    ∃ y, u y ∈ S ∧ f y = g y' := by
  obtain ⟨y, hy⟩ := hR.subset (Set.mem_range_self y')
  obtain ⟨z, hz, he⟩ := hN.subset (Set.mem_image_of_mem g hy')
  have hzy : z = u y := hf <| calc
    f z = g (v y') := he
    _ = k (g y') := hv
    _ = k (f y) := congrArg k hy.symm
    _ = f (u y) := (hu y).symm
  exact ⟨y, hzy ▸ hz, hy⟩

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem main : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (K' : FinExt l) (h' : Good K' s LL) (hle : K.1 ≤ K'.1), K0 K' = K0 K → ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ (m : ℕ) (y' : ((HW l).W K' s LL h').DD (resLt (K := K) (K' := K') (LL := LL) hle T)), y' ∈ invN ((HW l).W K' s LL h') (resLt (K := K) (K' := K') (LL := LL) hle T) (((HW l).W K' s LL h').Q ^ m) → ∃ y ∈ invN ((HW l).W K s LL h) T (((HW l).W K s LL h).Q ^ m), ((F l).E K s LL h).tie.jD T y = toTW hle T (((F l).E K' s LL h').tie.jD (resLt (K := K) (K' := K') (LL := LL) hle T) y') := by
  intro D HW F l _ K s LL h K' h' hle hK0 T hT m y' hy'
  let T' : Lt K' LL := resLt hle T
  let W := (HW l).W K s LL h
  let W' := (HW l).W K' s LL h'
  let E := ((F l).E K s LL h).tie
  let E' := ((F l).E K' s LL h').tie
  let j : W.DD T → RW LL ⊗[↥(OL LL)] ↥T.L.T := E.jD T
  let j' : W'.DD T' → RW LL ⊗[↥(OL LL)] ↥T.L.T := E'.jD T'
  let u := (W.ddModA T).toSMul.smul (W.Q ^ m)
  let v := (W'.ddModA T').toSMul.smul (W'.Q ^ m)
  let k := (@TensorProduct.leftHasSMul ↥(OL LL) (RW LL) _ _ (RW LL) ↥T.L.T _ _
    (Semiring.toModule (R := RW LL)).toDistribMulAction _ _ _).smul
      ((inclR LL ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] (D.locA l).ξ)) ^ m)
  have hB := (GlobalTheory.NL.BaseField.base_indep D HW F l K s LL h K' h' hle hK0).2.2
    T T' (LinearEquiv.refl (↥(OL LL)) ↥T.L.T) (fun _ _ => rfl)
  have hId := image_map_refl (O := ↥(OL LL)) (R := RW LL) (M := ↥T.L.T)
  have hR : Set.range j' = Set.range j :=
    (hId (Set.range j')).symm.trans hB.1
  have hN : j' '' (W'.N T' : Set (W'.DD T')) = j '' (W.N T : Set (W.DD T)) :=
    (hId (j' '' (W'.N T' : Set (W'.DD T')))).symm.trans
      (hB.2 hT (restrict_crys (K' := K') D hle T hT))
  exact transfer_preimage j j' u v k (W.N T) (W'.N T') (E.jD_inj T)
    (jD_Qpow D HW F l K s LL h T m) hR hN y' hy' (jD_Qpow D HW F l K' s LL h' T' m y')

end GlobalTheory.NL.TransitionThirdCase
