import Mathlib
import Development.WeilBound.CoreStatements.PeriodRingComparison.CrystallinePeriodRings.BcrisPlusHomAlgebraMap
import Development.WeilBound.CoreStatements.PeriodRingComparison.AinfInverseMaps.AinfInvMapGOC
import Development.WeilBound.CoreStatements.PeriodRingComparison.RationalRingEquivalences.IsLogCore
import Development.WeilBound.CoreStatements.PeriodRingComparison.AinfAlgebraMaps.CAAlgebraMapGOC

section
noncomputable section

open GroundTheory.PAdicHodge

namespace Cmp6

variable (l : ℕ) [Fact l.Prime]

theorem bcris_hom_ext_acris {B : Type} [CommRing B] {f g : Reformulated.AutPerF.Bcris l (OC l) →+* B}
    (h : ∀ x : Reformulated.AutPerF.Acris l (OC l),
      f (algebraMap (Reformulated.AutPerF.Acris l (OC l)) (Reformulated.AutPerF.Bcris l (OC l)) x) =
        g (algebraMap (Reformulated.AutPerF.Acris l (OC l)) (Reformulated.AutPerF.Bcris l (OC l)) x)) : f = g := by
  apply Reformulated.AutPerF.Bcris.hom_ext
  intro z
  have h2 : f.comp (algebraMap (Reformulated.AutPerF.BcrisPlus l (OC l)) (Reformulated.AutPerF.Bcris l (OC l))) =
      g.comp (algebraMap (Reformulated.AutPerF.BcrisPlus l (OC l)) (Reformulated.AutPerF.Bcris l (OC l))) := by
    apply Reformulated.AutPerF.BcrisPlus.hom_ext
    intro y
    exact h y
  exact RingHom.congr_fun h2 z

theorem cBc_frob_of
    (hφ : ∀ x, cA l (Reformulated.AutPerF.Acris.frob l (OC l) x) = ACris.phi ℂ_[l] l (cA l x))
    (b : Reformulated.AutPerF.Bcris l (OC l)) :
    cBc l (Reformulated.AutPerF.Bcris.frob l (OC l) b) = Formalism.Per6.φB l (cBc l b) := by
  have h : (cBc l).toRingHom.comp (Reformulated.AutPerF.Bcris.frob l (OC l)) =
      (Formalism.Per6.φB l).comp (cBc l).toRingHom :=
    bcris_hom_ext_acris l fun x => by
      change cBc l (Reformulated.AutPerF.Bcris.frob l (OC l) _) = Formalism.Per6.φB l (cBc l _)
      rw [Reformulated.AutPerF.Bcris.frob_algebraMap_acris, cBc_algebraMap, cBc_algebraMap, hφ,
        PositivityTheory.LocInh.φB_cB]
  exact RingHom.congr_fun h b

theorem cBc_aB (a : Reformulated.AutPerF.Ainf l (OC l)) :
    cBc l (algebraMap (Reformulated.AutPerF.Acris l (OC l)) (Reformulated.AutPerF.Bcris l (OC l))
      (algebraMap (Reformulated.AutPerF.Ainf l (OC l)) (Reformulated.AutPerF.Acris l (OC l)) a)) =
      Formalism.Per6.aB l a := by
  rw [cBc_algebraMap, cA_algebraMap]
  exact (PositivityTheory.LocInh.frob_aB_apply a).symm

theorem algebraMap_ainf_eq_zA (z : ℤ_[l]) :
    algebraMap ℤ_[l] (Reformulated.AutPerF.Ainf l (OC l)) z = Formalism.Per6.zA l z := rfl

theorem cBc_zB (z : ℤ_[l]) :
    cBc l (algebraMap ℚ_[l] (Reformulated.AutPerF.Bcris l (OC l)) (z : ℚ_[l])) = Formalism.Per6.zB l z := by
  have h : algebraMap ℤ_[l] (Reformulated.AutPerF.Acris l (OC l)) z =
      algebraMap (Reformulated.AutPerF.Ainf l (OC l)) (Reformulated.AutPerF.Acris l (OC l))
        (algebraMap ℤ_[l] (Reformulated.AutPerF.Ainf l (OC l)) z) := rfl
  rw [Reformulated.AutPerF.Bcris.algebraMap_padicInt, h, cBc_aB, algebraMap_ainf_eq_zA, Formalism.Per6.zB,
    RingHom.comp_apply]

end Cmp6
end
end

section
noncomputable section

open GroundTheory.PAdicHodge
open Formalism.BasicNotions.Loc (GQ)

namespace Cmp6

variable (l : ℕ) [Fact l.Prime]

theorem cBc_gal (g : GQ l) (b : Reformulated.AutPerF.Bcris l (OC l)) :
    cBc l (Reformulated.AutPerF.Bcris.map l (gOC l g) (Reformulated.AutPerF.toRingHom_injective g) b) =
      Formalism.Per6.σB g (cBc l b) := by
  have key : ((cBc l).toRingHom.comp
      (Reformulated.AutPerF.Bcris.map l (gOC l g) (Reformulated.AutPerF.toRingHom_injective g))).comp
        (cBc l).symm.toRingHom = Formalism.Per6.σB g :=
    PositivityTheory.LocInh.bcris_hom_ext fun y => by
      change cBc l (Reformulated.AutPerF.Bcris.map l (gOC l g) (Reformulated.AutPerF.toRingHom_injective g)
        ((cBc l).symm (Formalism.Per6.cB l y))) = _
      rw [cBc_symm_cB, Reformulated.AutPerF.Bcris.map_algebraMap_acris (gOC l g) (Reformulated.AutPerF.toRingHom_injective g),
        cBc_algebraMap, cA_map_gal,
        RingEquiv.apply_symm_apply, PositivityTheory.LocInh.σB_cB]
  have h := RingHom.congr_fun key (cBc l b)
  change cBc l (Reformulated.AutPerF.Bcris.map l (gOC l g) (Reformulated.AutPerF.toRingHom_injective g)
    ((cBc l).symm (cBc l b))) = _ at h
  rwa [RingEquiv.symm_apply_apply] at h

theorem cBc_smul (g : GQ l) (b : Reformulated.AutPerF.Bcris l (OC l)) :
    cBc l (g • b) = Formalism.Per6.σB g (cBc l b) :=
  cBc_gal l g b

end Cmp6
end
end

section
noncomputable section
open GroundTheory.PAdicHodge
namespace Cmp6
variable (l : ℕ) [Fact l.Prime]

theorem cA_frob_ainf (w : Reformulated.AutPerF.Ainf l (OC l)) :
    cA l (Reformulated.AutPerF.Acris.frob l (OC l) (algebraMap (Reformulated.AutPerF.Ainf l (OC l)) (Reformulated.AutPerF.Acris l (OC l)) w)) =
      ACris.phi ℂ_[l] l (cA l (algebraMap (Reformulated.AutPerF.Ainf l (OC l)) (Reformulated.AutPerF.Acris l (OC l)) w)) := by
  rw [Reformulated.AutPerF.Acris.frob_algebraMap, cA_algebraMap, cA_algebraMap]
  exact PositivityTheory.LocInh.frob_phi_ainfMap w

theorem cA_frob (x : Reformulated.AutPerF.Acris l (OC l)) :
    cA l (Reformulated.AutPerF.Acris.frob l (OC l) x) = ACris.phi ℂ_[l] l (cA l x) := by
  have h : (cA l).toRingHom.comp (Reformulated.AutPerF.Acris.frob l (OC l)) =
      (ACris.phi ℂ_[l] l).comp (cA l).toRingHom := by
    refine Reformulated.AutPerF.Acris.hom_ext fun a => ?_
    have := zero_ext l
      (F := ((cA l).toRingHom.comp (Reformulated.AutPerF.Acris.frob l (OC l))).comp
        (algebraMap (Reformulated.AutPerF.AcrisZero l (OC l)) (Reformulated.AutPerF.Acris l (OC l))))
      (G := ((ACris.phi ℂ_[l] l).comp (cA l).toRingHom).comp
        (algebraMap (Reformulated.AutPerF.AcrisZero l (OC l)) (Reformulated.AutPerF.Acris l (OC l))))
      (fun w => by
        simp only [RingHom.comp_apply]
        rw [← IsScalarTower.algebraMap_apply]
        exact cA_frob_ainf l w) a
    simpa only [RingHom.comp_apply] using this
  exact RingHom.congr_fun h x

end Cmp6
end
end

section
noncomputable section

open GroundTheory.PAdicHodge Formalism.BasicNotions.Loc

namespace Cmp6

variable (l : ℕ) [Fact l.Prime]

theorem cPd_eq_cP : cPd l = cP l := rfl

theorem cD_zD (z : ℤ_[l]) :
    cD l (algebraMap ℚ_[l] (Reformulated.AutPerF.BdR l (OC l)) (z : ℚ_[l])) = Formalism.Per6.zD l z := by
  have h0 : algebraMap ℚ_[l] (Reformulated.AutPerF.AinfInv l (OC l)) (z : ℚ_[l]) =
      algebraMap (Reformulated.AutPerF.Ainf l (OC l)) (Reformulated.AutPerF.AinfInv l (OC l))
        (algebraMap ℤ_[l] (Reformulated.AutPerF.Ainf l (OC l)) z) :=
    Reformulated.AutPerF.padicLift_algebraMap l (algebraMap ℤ_[l] (Reformulated.AutPerF.AinfInv l (OC l)))
      (Reformulated.AutPerF.AinfInv.isUnit_p l (R := OC l)) z
  have h1 : algebraMap ℚ_[l] (Reformulated.AutPerF.BdR l (OC l)) (z : ℚ_[l]) =
      algebraMap (Reformulated.AutPerF.BdRPlus l (OC l)) (Reformulated.AutPerF.BdR l (OC l))
        (algebraMap (Reformulated.AutPerF.Ainf l (OC l)) (Reformulated.AutPerF.BdRPlus l (OC l))
          (algebraMap ℤ_[l] (Reformulated.AutPerF.Ainf l (OC l)) z)) := by
    change algebraMap (Reformulated.AutPerF.BdRPlus l (OC l)) (Reformulated.AutPerF.BdR l (OC l))
      (algebraMap (Reformulated.AutPerF.AinfInv l (OC l)) (Reformulated.AutPerF.BdRPlus l (OC l))
        (algebraMap ℚ_[l] (Reformulated.AutPerF.AinfInv l (OC l)) (z : ℚ_[l]))) = _
    rw [h0]
    rfl
  rw [h1, cD_algebraMap, cPd_eq_cP, comparison_algebraMap_ainf]
  rfl

theorem isLogA_iff_cP (ε : PreTilt ↥(PadicComplexInt l) l) (y : Reformulated.AutPerF.BdRPlus l (OC l)) :
    IsLogA l ε y ↔ Formalism.Per6.IsLog l ε (cP l y) :=
  isLogA_iff_of_compat l (cP l) (comparison_algebraMap_ainf l) (θD_cP l) ε y

theorem compat_native :
    (∀ z : ℤ_[l], cBc l (algebraMap ℚ_[l] (Reformulated.AutPerF.Bcris l (OC l)) (z : ℚ_[l])) = Formalism.Per6.zB l z) ∧
    (∀ z : ℤ_[l], cD l (algebraMap ℚ_[l] (Reformulated.AutPerF.BdR l (OC l)) (z : ℚ_[l])) = Formalism.Per6.zD l z) ∧
    (∀ y : Reformulated.AutPerF.BdRPlus l (OC l), cD l (algebraMap _ (Reformulated.AutPerF.BdR l (OC l)) y) =
      algebraMap (Formalism.Per6.BdRp l) (Formalism.Per6.BdR l) (cP l y)) ∧
    (∀ y : Reformulated.AutPerF.BdRPlus l (OC l), Formalism.Per6.θD l (cP l y) =
      Reformulated.AutPerF.BdRPlus.thetaC l (PadicComplexInt l) y) ∧
    (∀ (g : GQ l) (b : Reformulated.AutPerF.Bcris l (OC l)), cBc l (g • b) = Formalism.Per6.σB g (cBc l b)) ∧
    (∀ (g : GQ l) (x : Reformulated.AutPerF.BdR l (OC l)), cD l (g • x) = Formalism.Per6.σD g (cD l x)) ∧
    (∀ b : Reformulated.AutPerF.Bcris l (OC l), cBc l (Reformulated.AutPerF.Bcris.frob l (OC l) b) = Formalism.Per6.φB l (cBc l b)) ∧
    (∀ (a : ℤ) (x : Reformulated.AutPerF.BdR l (OC l)), x ∈ Reformulated.AutPerF.BdR.fil l (OC l) a ↔ cD l x ∈ Formalism.Per6.FilD l a) ∧
    (∀ (ε : PreTilt ↥(PadicComplexInt l) l) (y : Reformulated.AutPerF.BdRPlus l (OC l)),
      IsLogA l ε y ↔ Formalism.Per6.IsLog l ε (cP l y)) ∧
    (∀ a : Reformulated.AutPerF.Ainf l (OC l), cBc l (algebraMap (Reformulated.AutPerF.Acris l (OC l)) (Reformulated.AutPerF.Bcris l (OC l))
      (algebraMap (Reformulated.AutPerF.Ainf l (OC l)) (Reformulated.AutPerF.Acris l (OC l)) a)) = Formalism.Per6.aB l a) :=
  ⟨cBc_zB l, cD_zD l, fun y => cD_algebraMap l y, θD_cP l, cBc_smul l, cD_gal l, cBc_frob_of l (cA_frob l), cD_fil l, isLogA_iff_cP l, cBc_aB l⟩

end Cmp6
end
end
