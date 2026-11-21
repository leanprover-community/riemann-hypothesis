import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.StabFiniteOf
import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.MeasurePrjFPreimage
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.ContinuousSplitA
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.NVolAllOf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TopoClose
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.UnfoldAbs
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.Unimod

section
noncomputable section

open MeasureTheory NumberField Set
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.HidaSetting Formalism.L2.SG.TypedSets

namespace MassDataMassesW

theorem massUnfold_holds : MassUnfold := by
  intro D X u hT _hc _hK hKo hfin 𝓕 h𝓕
  haveI : FiniteDimensional X.B.I.F X.B.I.E :=
    Module.finite_of_finrank_pos (by rw [X.B.I.cm.deg2]; norm_num)
  have hU : MeasurableSet ((KH X u : Subgroup ↥(Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u))) :
      Set ↥(Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u))) :=
    (hKo.preimage continuous_subtype_val).measurableSet
  exact massUnfold_gen X.B.I.cm.sig X.B.I.J (frameOf X u) (isCMExt_of_cmData X.B.I.cm)
    (isHermND_of_setting X) (X.measW u) hT (KH X u) hU hfin 𝓕 h𝓕

end MassDataMassesW
end
end

section
noncomputable section

open MeasureTheory NumberField
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
  Formalism.L2.SG.TypedSets

namespace MassDataMassesW

theorem countable_ratOf {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (K : Subgroup (HA (AF F) σ J)) :
    Countable (ratOf (K := K)) := by
  haveI := PI.VolStabSW.um_countable_HFinIn F E σ M J
  refine Function.Injective.countable (f := fun x : ratOf (K := K) =>
    (⟨((x : K) : HA (AF F) σ J), Subgroup.mem_comap.1 x.2⟩ : HFinIn (AF F) σ J)) ?_
  intro x y hxy
  have e := congrArg Subtype.val hxy
  exact Subtype.ext (Subtype.ext e)

theorem smulInv_ratOf {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G] (K : Subgroup G)
    (Γ : Subgroup K) (μ : Measure K) [μ.IsMulLeftInvariant] : SMulInvariantMeasure Γ K μ := by
  first
  | exact inferInstance
  | exact ⟨fun c s _ => by
      show μ ((fun x : K => (c : K) * x) ⁻¹' s) = μ s
      exact measure_preimage_mul μ (c : K) s⟩

theorem covol_eq_of_fd {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) [MeasurableMul (HA (AF F) σ J)]
    (K : Subgroup (HA (AF F) σ J)) (μ : Measure K) (hμ : μ.IsMulLeftInvariant) (𝓕 : Set K)
    (h𝓕 : IsFundamentalDomain (ratOf (K := K)) 𝓕 μ) : covol μ = (μ 𝓕).toReal := by
  haveI := hμ
  haveI := countable_ratOf σ J K
  haveI := smulInv_ratOf K (ratOf (K := K)) μ
  unfold covol
  split_ifs with h
  · congr 1
    exact h.choose_spec.measure_eq h𝓕
  · exact absurd ⟨𝓕, h𝓕⟩ h

theorem n4cov_holds : UnipotentCoveringCount := by
  intro D X u 𝓕 hN h𝓕
  exact covol_eq_of_fd _ _ _ _ hN.2.2.2.1.toIsMulLeftInvariant 𝓕 h𝓕

end MassDataMassesW
end
end

section
noncomputable section

open MeasureTheory NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
  Formalism.L2.SG.TypedSets
open scoped TensorProduct

namespace MassDataMassesW

theorem massH_nonneg {D : D7} (X : HidaSetting D) (u : D.what₂.Word) :
    0 ≤ massH X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) (frameOf X u) :=
  finsum_nonneg fun _ => inv_nonneg.2 (Nat.cast_nonneg _)

theorem massAll_of (hH : HinfCompact) (hK : KCompactOpen) (hC : ClassFinite) : MassAll := by
  intro D X hb u hT
  have : FiniteDimensional X.B.I.F X.B.I.E :=
    Module.finite_of_finrank_pos (by rw [X.B.I.cm.deg2]; norm_num)
  have hN := X.measW_norm u
  have hcs := hH X u
  have hfin : MassFinite (G := ↥(Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u))) (GamH X u) (KH X u) :=
    ⟨hC X u, stabFinite_of hH hK X u⟩
  obtain ⟨𝓕, h𝓕⟩ := fdExistsH_holds X u
  have hU := massUnfold_holds X u hN hcs (hK X).1 (hK X).2 hfin 𝓕 h𝓕
  have hcov : covol (X.measW u).μH = ((X.measW u).μH 𝓕).toReal :=
    covol_eq_of_fd X.B.I.cm.sig X.B.I.J _ (X.measW u).μH hN.1.toIsMulLeftInvariant 𝓕 h𝓕
  have hV := volHTie_holds X hb u hT

  have h1 := hN.2.1
  have h2 := hN.2.2.1
  have ha0 : (X.measW u).μHinf Set.univ ≠ 0 :=
    (isOpen_univ.measure_pos _ Set.univ_nonempty).ne'
  have haT : (X.measW u).μHinf Set.univ ≠ ⊤ :=
    (h1.toIsFiniteMeasureOnCompacts.lt_top_of_isCompact (@isCompact_univ _ _ (hH X u))).ne
  have hKo : IsOpen (Subtype.val ⁻¹' (KX X : Set (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J)) :
      Set ↥(Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u))) :=
    (hK X).2.preimage continuous_subtype_val
  have hb0 : (X.measW u).μHf (Subtype.val ⁻¹' (KX X : Set (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J))) ≠ 0 :=
    h2.toIsOpenPosMeasure.open_pos _ hKo ⟨1, (KX X).one_mem⟩
  have hcl : IsClosed ((Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u) :
      Subgroup (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J)) : Set (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J)) :=
    isClosed_stabT' X.B.I.cm.sig X.B.I.J (Af X.B.I.F) (tupH (frameOf X u))
  have hbT : (X.measW u).μHf (Subtype.val ⁻¹' (KX X : Set (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J))) ≠ ⊤ :=
    (h2.toIsFiniteMeasureOnCompacts.lt_top_of_isCompact
      (hcl.isClosedEmbedding_subtypeVal.isCompact_preimage (hK X).1)).ne
  have ha : 0 < ((X.measW u).μHinf Set.univ).toReal := ENNReal.toReal_pos ha0 haT
  have hb' : 0 < ((X.measW u).μHf (Subtype.val ⁻¹' (KX X : Set (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J)))).toReal :=
    ENNReal.toReal_pos hb0 hbT
  unfold MassAt
  rw [hcov, hU, hV, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (massH_nonneg X u)]
  field_simp

end MassDataMassesW
end
end
