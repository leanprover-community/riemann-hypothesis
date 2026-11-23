module

public import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseLevel
public import GroundTheory.ProfiniteCohomology.PoincareDuality.TensorHomZmodDualIsoZmodMulPairing
public import GroundTheory.ProfiniteCohomology.PoitouTate.ZmodToQZCompactCohomologyResMapOfLocalInv
import GroundTheory.ProfiniteCohomology.PoincarePairs
public import GroundTheory.ProfiniteCohomology.PoitouTate.PoitouTateNineTermGs
public import GroundTheory.ProfiniteCohomology.PoitouTate.RealAbstract
import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseInv
import GroundTheory.ProfiniteCohomology.RestrictedRamification.BijectiveGsLocalInvRootsOfPlaces
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
import Mathlib.Tactic.TypeStar

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open IsDedekindDomain NumberField CategoryTheory MonoidalCategory GroundTheory.Global

noncomputable section

attribute [local instance 2000] Rep.hV2

local notation "ℚ̄" => AlgebraicClosure ℚ

section Algebra

theorem bijective_of_surjective_of_surjective_dual {A : Type*} [AddCommGroup A] {n : ℕ} [NeZero n]
    (hA : ∀ a : A, n • a = 0) (T : A →+ ZMod n) (hT : Function.Surjective T)
    (e : ZMod n → (A →+ ZMod n)) (he : Function.Surjective e) : Function.Bijective T := by
  have : Finite (A →+ ZMod n) := Finite.of_surjective e he
  have : Finite A := finite_of_finite_addMonoidHom_zmod hA
  let ev : A → ((A →+ ZMod n) →+ ZMod n) := fun a =>
    { toFun := fun χ => χ a
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hev : Function.Injective ev := by
    intro a b hab
    by_contra hne
    obtain ⟨χ, hχ⟩ := zmod_exists_apply_ne_zero hA (sub_ne_zero.2 hne)
    apply hχ
    rw [map_sub, sub_eq_zero]
    exact DFunLike.congr_fun hab χ
  have h1 : Nat.card A ≤ Nat.card ((A →+ ZMod n) →+ ZMod n) := Nat.card_le_card_of_injective ev hev
  have h2 : Nat.card ((A →+ ZMod n) →+ ZMod n) ≤ Nat.card (A →+ ZMod n) :=
    card_addMonoidHom_zmod_le (n := n) (A := A →+ ZMod n)
  have h3 : Nat.card (A →+ ZMod n) ≤ Nat.card (ZMod n) := Nat.card_le_card_of_surjective e he
  exact hT.bijective_of_nat_card_le (h1.trans (h2.trans h3))

end Algebra

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ι : Type} {Hv : ι → Type} [∀ v, Group (Hv v)] [∀ v, TopologicalSpace (Hv v)]
  [∀ v, IsTopologicalGroup (Hv v)] (φ : ∀ v, Hv v →ₜ* G)
  {n : ℕ} [NeZero n] {D : Rep (ULift.{0} ℤ) G} [IsDiscreteRep D] (hD : ∀ d : D, n • d = 0)
  [IsDiscreteRep (dualRep D (zmodRep.{0} G n))]


omit [TopologicalSpace G] [IsTopologicalGroup G] [NeZero n] [IsDiscreteRep D]
  [IsDiscreteRep (dualRep D (zmodRep.{0} G n))] in
theorem tensorHom_zmodDualIso_inv_dualEvalPairing :
    ((zmodDualIso n D hD).inv ⊗ₘ 𝟙 (zmodRep.{0} G n)) ≫ dualEvalPairing D (zmodRep.{0} G n) =
      (𝟙 D ⊗ₘ 𝟙 (zmodRep.{0} G n)) ≫ zmodMulPairingRight n D hD := by
  rw [← tensorHom_zmodDualIso_zmodMulPairingRight D hD, ← Category.assoc,
    MonoidalCategory.tensorHom_comp_tensorHom, Iso.inv_hom_id, Category.comp_id]


omit [NeZero n] in
theorem compactZmodDualityMap_eq_compactDualityMap {m r s : ℕ}
    (T : compactCohomologyRes φ D m →+ ZMod n) (h : r + s = m) (x : cohomology (zmodRep.{0} G n) r)
    (y : compactCohomologyRes φ D s) :
    compactZmodDualityMap φ D hD T h x y =
      compactDualityMap φ D h T (zmodRep.{0} G n) x
        ((compactCohomologyResMap φ (zmodDualIso n D hD).inv s).hom y) := by
  have e := compactCupRes_compactCohomologyResMap φ (dualEvalPairing D (zmodRep.{0} G n))
    (zmodMulPairingRight n D hD) (zmodDualIso n D hD).inv (𝟙 _)
    (tensorHom_zmodDualIso_inv_dualEvalPairing hD) ((Nat.add_comm s r).trans h) y x
  rw [cohomologyMap_id, ModuleCat.hom_id, LinearMap.id_apply] at e
  rw [compactZmodDualityMap_apply, compactDualityMap_apply, e]

theorem bijective_compactZmodDualityMap_of_compactDualityMap {m r s : ℕ}
    (T : compactCohomologyRes φ D m →+ ZMod n) (h : r + s = m)
    (hb : Function.Bijective (compactDualityMap φ D h T (zmodRep.{0} G n))) :
    Function.Bijective (compactZmodDualityMap φ D hD T h) :=
  bijective_of_bijective_comp hb Function.bijective_id
    (bijective_compactCohomologyResMap_of_comp_eq_id φ (zmodDualIso n D hD).inv (zmodDualIso n D hD).hom
      (Iso.inv_hom_id _) (Iso.hom_inv_id _) s)
    (γ := (compactCohomologyResMap φ (zmodDualIso n D hD).inv s).hom.toAddMonoidHom)
    fun x y => compactZmodDualityMap_eq_compactDualityMap φ hD T h x y

omit [IsDiscreteRep (dualRep D (zmodRep.{0} G n))] in
private theorem bijective_compactZmodDualityMap_of_transport
    {G' : Type} [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G']
    {ι' : Type} {Hv' : ι' → Type} [∀ v, Group (Hv' v)] [∀ v, TopologicalSpace (Hv' v)]
    [∀ v, IsTopologicalGroup (Hv' v)] (ψ : ∀ v, Hv' v →ₜ* G')
    {D' : Rep (ULift.{0} ℤ) G'} [IsDiscreteRep D'] (hD' : ∀ d : D', n • d = 0)
    {m r s : ℕ} (h : r + s = m)
    (T : compactCohomologyRes φ D m →+ ZMod n) (T' : compactCohomologyRes ψ D' m →+ ZMod n)
    (eX : cohomology (zmodRep.{0} G n) r ≅ cohomology (zmodRep.{0} G' n) r)
    (eY : compactCohomologyRes φ D s ≅ compactCohomologyRes ψ D' s)
    (eW : compactCohomologyRes φ D m ≅ compactCohomologyRes ψ D' m)
    (hcup : ∀ y x,
      eW.hom.hom (compactCupRes φ (zmodMulPairingRight n D hD) ((Nat.add_comm s r).trans h) y x) =
        compactCupRes ψ (zmodMulPairingRight n D' hD') ((Nat.add_comm s r).trans h)
          (eY.hom.hom y) (eX.hom.hom x))
    (hT' : Function.Surjective T') (hT : Function.Bijective T)
    (hb : Function.Bijective (compactZmodDualityMap φ D hD T h)) :
    Function.Bijective (compactZmodDualityMap ψ D' hD' T' h) := by
  let aX := eX.toLinearEquiv.toAddEquiv
  let aY := eY.toLinearEquiv.toAddEquiv
  let aW := eW.toLinearEquiv.toAddEquiv
  obtain ⟨c, hc, hmul⟩ := exists_isUnit_mul_of_surjective_of_bijective T'
    (T.comp aW.symm.toAddMonoidHom) hT' (hT.comp aW.symm.bijective)
  have hsr := (Nat.add_comm s r).trans h
  exact bijective_of_transport
    (bilinAddHom (compactCupRes φ (zmodMulPairingRight n D hD) hsr))
    (bilinAddHom (compactCupRes ψ (zmodMulPairingRight n D' hD') hsr))
    T T' aX aY aW (fun y x => (hcup y x).symm) c hc
    (fun w => (hmul (aW w)).trans (congrArg (fun z => c * T z) (aW.symm_apply_apply w))) hb

end Generic

section Level

variable {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1))) [Fintype S]
  (ιs : ∀ v : S, ℚ̄ →ₐ[K.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))
  {N : ℕ} [NeZero N] (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((N : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)
  (hK : Odd N ∨ IsTotallyComplex K.1)



include hS in
theorem bijective_gs_compactZmodDualityMap_of_duality {r s : ℕ} (h : r + s = 3) :
    Function.Bijective (compactZmodDualityMap (gsFinFamily S ιs) (gsRoots S N) (nsmul_gsRoots S N)
      (gsCompactInv S ιs N hK (subsingleton_cohomology_three_gsRoots S hS hK)) h) := by
  have : IsDiscreteRep (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) N) := isDiscreteRep_of_isTrivial _
  have : IsDiscreteRep (dualRep (gsRoots S N) (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) N)) :=
    isDiscreteRep_dualRep _ _
  exact bijective_compactZmodDualityMap_of_compactDualityMap (gsFinFamily S ιs) (nsmul_gsRoots S N) _ h
    (poitouTate_duality_gs S ιs hS hK (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) N)
      (nsmul_zmodRep_eq_zero _ N) h)


include hS in
theorem bijective_gsCompactInv_of_duality [Nonempty S] :
    Function.Bijective (gsCompactInv S ιs N hK (subsingleton_cohomology_three_gsRoots S hS hK)) :=
  bijective_of_surjective_of_surjective_dual
    (nsmul_compactCohomologyRes_eq_zero (gsFinFamily S ιs) (nsmul_gsRoots S N) 3) _
    (surjective_gsCompactInv S N ιs hK (subsingleton_cohomology_three_gsRoots S hS hK) fun v =>
      (bijective_gsLocalInvRoots_of_places S ιs N (fun v hv h => hv (hS v h)) v).2)
    (fun a => compactZmodDualityMap (gsFinFamily S ιs) (gsRoots S N) (nsmul_gsRoots S N)
      (gsCompactInv S ιs N hK (subsingleton_cohomology_three_gsRoots S hS hK)) (show 0 + 3 = 3 from rfl)
      (zmodH0Class a))
    ((bijective_gs_compactZmodDualityMap_of_duality S ιs hS hK (show 0 + 3 = 3 from rfl)).2.comp
      (zmodH0Class_surjective (H := galUnramifiedOutside K.1 ℚ̄ S) (n := N)))


include hS in
theorem gsLevelBijective_gsCompactInv [Nonempty S] :
    GsLevelBijective (gsCompactInv S ιs N hK (subsingleton_cohomology_three_gsRoots S hS hK)) := by
  have hInv := bijective_gsCompactInv_of_duality S ιs hS hK
  have hPairing {r s : ℕ} (h : r + s = 3) :=
    bijective_gs_compactZmodDualityMap_of_duality S ιs hS hK h
  have hBoth := And.intro hInv @hPairing
  unfold GsLevelBijective
  with_reducible exact hBoth

end Level

section OpenSubgroup

variable {K L : FiniteSubfield} [Fact (K ≤ L)] (S : Set (HeightOneSpectrum (𝓞 K.1)))
  (ιs : ∀ v : S, ℚ̄ →ₐ[K.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))
  (hL : ∀ x : L.1, algebraMap L.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S) (n : ℕ) [NeZero n]



theorem bijective_compactZmodDualityMap_gsOpenSubgroup_of_surjective
    (τ : compactCohomologyRes (mackeyFamily (gsOpenSubgroup S hL) (gsFinFamily S ιs))
      (Rep.res (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype (gsRoots S n)) 3 →+ ZMod n)
    (hτ : Function.Surjective τ)
    (TL : compactCohomologyRes (gsFinFamily (placesOver S) (gsMackeyEmbeddings hL ιs))
      (gsRoots (K := L) (placesOver S) n) 3 →+ ZMod n) (hLev : GsLevelBijective TL) {r s : ℕ} (h : r + s = 3) :
    Function.Bijective (compactZmodDualityMap (mackeyFamily (gsOpenSubgroup S hL) (gsFinFamily S ιs))
      (Rep.res (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype (gsRoots S n))
      (nsmul_gsRoots S n) τ h) := by
  let D := Rep.res (gsOpenSubgroup S hL : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype (gsRoots S n)
  let DL := gsRoots (K := L) (placesOver S) n
  have hD : ∀ d : D, n • d = 0 := nsmul_gsRoots S n
  have hDL : ∀ d : DL, n • d = 0 := nsmul_gsRoots (K := L) (placesOver S) n
  let f := (gsRootsOfUnityIso S hL n).symm
  let θ := gsBaseChange S hL
  let eX := cohomologyIsoOfContinuousMulEquiv θ (zmodRepResIso θ n) r
  let eC := gsMackeyCompactIso (A' := DL) (A := D) hL ιs f
  have hcup := gsMackeyCompactIso_compactCupRes_zmod (D' := DL) (D := D) hL ιs n
    hDL hD f ((Nat.add_comm s r).trans h)
  have hTransport := bijective_compactZmodDualityMap_of_transport
    (D := DL) (D' := D) (gsFinFamily (placesOver S) (gsMackeyEmbeddings hL ιs)) hDL
    (mackeyFamily (gsOpenSubgroup S hL) (gsFinFamily S ιs)) hD h TL τ eX (eC s) (eC 3)
  with_reducible refine hTransport ?_ hτ ?_ ?_
  · simp only [eC, eX, cohomologyIsoOfContinuousMulEquiv_hom]
    with_reducible exact hcup
  · have hInv := hLev.1
    with_reducible exact hInv
  · have hPairing := hLev.2 h
    with_reducible exact hPairing

end OpenSubgroup

end

end GroundTheory.ProfCoh
