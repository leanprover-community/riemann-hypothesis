import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsWeight
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Imports
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.AlgebraicCharacterWD
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.AttTwist
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.Untwist
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeLAdicCharacterAndPrincipalIdealSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlobalArtinReciprocityHolds
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsGoodConjSelfDualTwistSplitUnramifiedStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsPotentiallySemistableOfSemistableRestrict
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GaloisRepOfPolarizedCuspidal
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WdParameterMonodromyZeroIffPotentiallyCrystallin
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsFrobSSWdRep
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GaloisRepConjInvariant
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsPstOfIsSst
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PotSemistableOfPotCrystallineDecompositionGroup
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DmulMulDRight
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsPeriodProductEqOfInvertibleCharacter
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsInvertibleDPstPotSemistableCharacter

section
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.GalOfCusp
open TensorProduct Module

noncomputable section

namespace GlobalTheory.SstTwist

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K L : FinExt l}
  {V : Type} [AddCommGroup V] [Module ↥L.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥L.1 V]

theorem ineTriv_of_isSst [FiniteDimensional ↥L.1 V] (ρ : Representation ↥L.1 ↥(GK K) V) (hV : IsPst P ρ)
    (hs : IsSst P ρ) : GlobalTheory.PstLaws.IneTriv P ρ := by
  intro g hg
  have hcl := mem_closure_mulV_of_finrank_eq l P K L V ρ hV (Dst P ρ) le_rfl
    (fun c hc x hx => (mem_Dst P ρ).mpr fun h => by
      rw [← Module.End.mul_apply, stRep_mulV P ρ h c c (mem_GK.mp h.2 _ hc), Module.End.mul_apply,
        (mem_Dst P ρ).mp hx h]) hs
  refine LinearMap.ext fun x => Subtype.ext ?_
  refine AddSubgroup.closure_induction (p := fun y _ => stRep P ρ g y = y) ?_ (map_zero _) ?_ ?_ (hcl x x.2)
  · rintro _ ⟨c, s, hs', rfl⟩
    rw [← Module.End.mul_apply, stRep_mulV P ρ g c c ((IntermediateField.mem_fixingSubgroup_iff _ _).mp hg _ c.2),
      Module.End.mul_apply, (mem_Dst P ρ).mp hs' g]
  · intro y z _ _ hy hz; rw [map_add, hy, hz]
  · intro y _ hy; rw [map_neg, hy]

end GlobalTheory.SstTwist

namespace GlobalTheory.SstTwist

open GlobalTheory.Pst.TwistLetters GlobalTheory.Pst.TwistLetters.Invert

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) {K L : FinExt l}
  {V : Type} [AddCommGroup V] [Module ↥L.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥L.1 V]

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem isSst_twist (T : LocTied l P AI) [FiniteDimensional ↥L.1 V] (ρs ρt : Representation ↥L.1 ↥(GK K) V)
    (ρm : Representation ↥L.1 ↥(GK K) (Fin 1 → ↥L.1)) (χ : ↥(GK K) → ↥L.1)
    (hm : ∀ g v, ρm g v = χ g • v) (ht : ∀ g v, ρt g v = χ g • ρs g v)
    (hs : IsSst P ρs) (hc : Formalism.WeaklyAdmissibleFiltrations.IsCrys (P.PD K) ρm) : IsSst P ρt := by
  haveI := L.2
  haveI : FiniteDimensional ℚ_[l] V := Module.Finite.trans ↥L.1 V
  have hPs : IsPst P ρs := GlobalTheory.GalCut.IwaAll.isPst_of_isSst P AI T ρs hs
  have hPm : IsPst P ρm := GlobalTheory.PstOfCrys.isPst_of_isCrys T ρm hc
  have hIs := ineTriv_of_isSst P ρs hPs hs
  have hIm := GlobalTheory.PstLaws.ineTriv_of_isCrys P ρm hPm hc
  obtain ⟨y, hy, y', hyy'⟩ := GlobalTheory.Pst.UnitLetter.exists_unit_Dpst P AI ⟨T⟩ ρm χ hm hPm
  let y₀ : ↥(Dpst P ρm) := ⟨y, hy⟩
  have hsurj := GlobalTheory.Pst.TwistLetters.exists_dmul_eq_of_inv P ρs ρt ρm χ hm ht y₀ y' hyy'

  let Φ : DpstUr P ρs →ₗ[↥(MaximalUnramifiedExtension l)] DpstUr P ρt :=
    { toFun := fun x => toUr P ρt (dmul P ρs ρt ρm χ hm ht ((toUr P ρs).symm x) y₀)
      map_add' := fun x x' => by simp only [map_add, LinearMap.add_apply]
      map_smul' := fun c x => dmul_mulD_left P ρs ρt ρm χ hm ht c _ y₀ }
  have hinj : Function.Injective Φ := by
    intro x x' hxx
    have h1 : mulB P V y' (mulB P V y ((toUr P ρs).symm x : V ⊗[ℚ_[l]] Bst P)) =
        mulB P V y' (mulB P V y ((toUr P ρs).symm x' : V ⊗[ℚ_[l]] Bst P)) :=
      congrArg (fun z : ↥(Dpst P ρt) => mulB P V y' (z : V ⊗[ℚ_[l]] Bst P)) hxx
    rw [mulB_assoc, mulB_assoc, hyy', one_mulB, one_mulB] at h1
    exact (toUr P ρs).symm.injective (Subtype.ext h1)
  have hsur : Function.Surjective Φ := by
    intro z
    obtain ⟨x, hx⟩ := hsurj ((toUr P ρt).symm z)
    exact ⟨toUr P ρs x, by
      change toUr P ρt (dmul P ρs ρt ρm χ hm ht ((toUr P ρs).symm (toUr P ρs x)) y₀) = z
      rw [AddEquiv.symm_apply_apply, hx, AddEquiv.apply_symm_apply]⟩
  have hPt : IsPst P ρt := by
    rw [IsPst, ← (LinearEquiv.ofBijective Φ ⟨hinj, hsur⟩).rank_eq]
    exact hPs
  refine GlobalTheory.PstLaws.isSst_of_ineTriv P ρt hPt fun g hg => LinearMap.ext fun z => ?_
  obtain ⟨x, rfl⟩ := hsurj z
  rw [actD_dmul, LinearMap.congr_fun (hIs g hg) x, LinearMap.congr_fun (hIm g hg) y₀]
  rfl

end GlobalTheory.SstTwist

open GlobalTheory.Pst.TwistLetters

theorem GlobalTheory.SstTwist.isSstAt_twist : GlobalTheory.Published.DeRhamPotSemistable → ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (E Ω : Type) [Field E] [Field Ω] [Algebra E Ω] (Gw : Subgroup (Ω ≃ₐ[E] Ω)) (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω Gw O) (a : ℕ) (r : ↥Gw →* GL (Fin a) (Om l)) (c : ↥Gw →* GL (Fin 1) (Om l)), (Continuous fun g => ((r g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l))) → (Continuous fun g => ((c g : GL (Fin 1) (Om l)) : Matrix (Fin 1) (Fin 1) (Om l))) → IsSstAt P Bw r → IsCrysAt P Bw c → IsSstAt P Bw (Formalism.MainNotions.SumRepresentations.At.twGL r (Matrix.GeneralLinearGroup.det.comp c)) := by
  intro _ l _ P AI hT E Ω _ _ _ Gw O _ _ _ Bw a r c _ _ hr hc
  obtain ⟨T⟩ := hT
  obtain ⟨L₁, r₁, hm₁, hs₁⟩ := hr
  obtain ⟨L₂, c₂, hm₂, hc₂⟩ := hc
  have l₁ : L₁.1 ≤ (supExt L₁ L₂).1 := le_sup_left
  have l₂ : L₂.1 ≤ (supExt L₁ L₂).1 := le_sup_right
  set L := supExt L₁ L₂
  set s := Formalism.MainNotions.N.mapRep (IntermediateField.inclusion l₁).toRingHom r₁
  set m := Formalism.MainNotions.N.mapRep (IntermediateField.inclusion l₂).toRingHom c₂
  refine ⟨L, _, GlobalTheory.TwistParamAbove.isModel_twist (hm₁.enlarge l₁) (hm₂.enlarge l₂), ?_⟩
  have hsL : IsSst P (Bw.repE L s) := GlobalTheory.AboveL.RepConj.isSst_enlarge P Bw l₁ r₁ hs₁
  have hcL : Bw.IsCrysE P L m := (GlobalTheory.Pst.local_ext P Bw l₂ c₂).1.2 hc₂
  let χ : ↥(GK Bw.Kw) → ↥L.1 := fun g => ((GlobalTheory.TwistAbove.chr m (Bw.e.symm g) : (↥L.1)ˣ) : ↥L.1)
  have hχm : ∀ g v, Bw.repE L m g v = χ g • v := fun g v => GlobalTheory.TwistAbove.repE_rank_one Bw m g v
  have hχt : ∀ g v, Bw.repE L (Formalism.MainNotions.SumRepresentations.At.twGL s (Matrix.GeneralLinearGroup.det.comp m)) g v =
      χ g • Bw.repE L s g v := by
    intro g v
    rw [GlobalTheory.TwistBridgeDR.twGL_eq]
    exact GlobalTheory.TwistBridgeDR.repE_twGL' Bw _ s g v
  exact GlobalTheory.SstTwist.isSst_twist P AI T (Bw.repE L s) _ (Bw.repE L m) χ hχm hχt hsL hcL
end
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.GalOfCusp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSemistableAtPlace_twist_crystallineCharacter : GlobalTheory.Published.DeRhamPotSemistable → ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (E Ω : Type) [Field E] [Field Ω] [Algebra E Ω] (Gw : Subgroup (Ω ≃ₐ[E] Ω)) (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω Gw O) (a : ℕ) (r : ↥Gw →* GL (Fin a) (Om l)) (c : ↥Gw →* GL (Fin 1) (Om l)), (Continuous fun g => ((r g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l))) → (Continuous fun g => ((c g : GL (Fin 1) (Om l)) : Matrix (Fin 1) (Fin 1) (Om l))) → IsSstAt P Bw r → IsCrysAt P Bw c → IsSstAt P Bw (Formalism.MainNotions.SumRepresentations.At.twGL r (Matrix.GeneralLinearGroup.det.comp c)) := by
  atlas_forward_decl GlobalTheory.SstTwist.isSstAt_twist
end

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published
open UpperTheory.V UpperTheory.V.Af

noncomputable section

namespace GlobalTheory.GalCut.IwaTwist

open Formalism.WeaklyAdmissibleFiltrations GlobalTheory.PMon Module

theorem isSst_resQ {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K : FinExt l} {LL : Type} [Field LL] [Algebra ℚ_[l] LL]
    [FiniteDimensional ℚ_[l] LL] {V : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]
    (ρ : Representation LL ↥(GK K) V) (h : IsSst P ρ) : IsSst P (GlobalTheory.PstCoeff.resQ ρ) := by
  have hD : Dst P (GlobalTheory.PstCoeff.resQ ρ) = (Dst P ρ).restrictScalars ℚ_[l] := by
    ext x
    simp [mem_Dst, GlobalTheory.PstCoeff.stRep_resQ]
  have e : finrank ℚ_[l] ↥(Dst P (GlobalTheory.PstCoeff.resQ ρ)) = finrank ℚ_[l] LL * finrank LL ↥(Dst P ρ) := by
    rw [hD, finrank_mul_finrank]
    rfl
  rw [IsSst, e, h, ← finrank_mul_finrank ℚ_[l] LL V]
  ring

theorem isPst_of_isSst {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) {K : FinExt l}
    {LL : Type} [Field LL] [Algebra ℚ_[l] LL] [FiniteDimensional ℚ_[l] LL] {V : Type} [AddCommGroup V] [Module LL V]
    [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V] [FiniteDimensional ℚ_[l] V]
    (ρ : Representation LL ↥(GK K) V) (h : IsSst P ρ) : IsPst P ρ := by
  rw [← GlobalTheory.PstCoeff.isPst_resQ_iff]
  apply GlobalTheory.PMon.isPst_of_isSst_resTo l P AI T K K le_rfl V
  have hD : Dst P (resTo (GlobalTheory.PstCoeff.resQ ρ) (le_refl K.1)) = Dst P (GlobalTheory.PstCoeff.resQ ρ) := by
    ext x
    rw [mem_Dst_resTo, mem_Dst]
    exact ⟨fun H g => H g g.2, fun H g _ => H g⟩
  have := isSst_resQ P ρ h
  rw [IsSst] at this ⊢
  rw [hD]
  exact this

theorem isPstAt_of_isSstAt {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (hT : Nonempty (LocTied l P AI))
    {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type} [CommRing O]
    [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω Gw O) {a : ℕ} (r : ↥Gw →* GL (Fin a) (Om l)) :
    IsSstAt P Bw r → IsPstAt P Bw r := by
  rintro ⟨LL', r', hm, hs⟩
  obtain ⟨T⟩ := hT
  haveI := LL'.2
  exact ⟨LL', r', hm, isPst_of_isSst P AI T _ hs⟩

theorem isSstAt_twist (hD : GlobalTheory.Published.DeRhamPotSemistable) {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (hT : Nonempty (LocTied l P AI))
    {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type} [CommRing O]
    [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω Gw O) {a : ℕ}
    (r : ↥Gw →* GL (Fin a) (Om l)) (c : ↥Gw →* GL (Fin 1) (Om l))
    (hr : Continuous fun g => ((r g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)))
    (hc : Continuous fun g => ((c g : GL (Fin 1) (Om l)) : Matrix (Fin 1) (Fin 1) (Om l)))
    (h1 : IsSstAt P Bw r) (h2 : IsCrysAt P Bw c) :
    IsSstAt P Bw (Formalism.MainNotions.SumRepresentations.At.twGL r (Matrix.GeneralLinearGroup.det.comp c)) :=
  GlobalTheory.T.isSemistableAtPlace_twist_crystallineCharacter hD l P AI hT E Ω Gw O Bw a r c hr hc h1 h2

end GlobalTheory.GalCut.IwaTwist

namespace GlobalTheory.GalCut.IwaTwist

end GlobalTheory.GalCut.IwaTwist

namespace GlobalTheory.GalCut.IwaTwist

end GlobalTheory.GalCut.IwaTwist

end
end
