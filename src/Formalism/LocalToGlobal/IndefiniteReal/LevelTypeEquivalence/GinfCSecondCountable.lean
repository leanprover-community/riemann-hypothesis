import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.NumFieldHosCountable
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.TnsIsTopologicalAddGroup
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.FdomExistsAll

section
open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

noncomputable section

namespace Formalism.IndefR.Eqv.G5

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem hfin_exists_mat (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (γ : HFinIn (AF F) σ J) :
    ∃ g : GL (Fin M) E, Formalism.UG.bc (inclR (AF F)) g = ((γ : HR (AF F) σ J) : GL (Fin M) (AF F ⊗[F] E)) := by
  have h : ((γ : HR (AF F) σ J) : GL (Fin M) (AF F ⊗[F] E)) ∈
      (Formalism.UG.UJ (σ : E →+* E) J).map (Formalism.UG.bc (inclR (AF F))) := γ.2
  obtain ⟨g, -, hg⟩ := Subgroup.mem_map.1 h
  exact ⟨g, hg⟩

theorem hfin_entry {M : ℕ} (g : GL (Fin M) E) (i j : Fin M) :
    ((Formalism.UG.bc (inclR (F := F) (AF F)) g : GL (Fin M) (AF F ⊗[F] E)) :
      Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) i j =
      inclR (AF F) ((g : Matrix (Fin M) (Fin M) E) i j) := by
  simp [Formalism.UG.bc]

theorem hfin_disc (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) :
    DiscreteTopology (HFinIn (AF F) σ J) := by
  have := tns_isTopologicalAddGroup (F := F) (E := E)
  obtain ⟨V, hVo, hV0, hV⟩ := tns_disc (F := F) (E := E)
  refine discreteTopology_iff_isOpen_singleton.2 fun γ => ?_
  let ent : HR (AF F) σ J → Matrix (Fin M) (Fin M) (AF F ⊗[F] E) :=
    fun h => ((h : GL (Fin M) (AF F ⊗[F] E)) : Matrix (Fin M) (Fin M) _)
  have hent : Continuous ent := Units.continuous_val.comp continuous_subtype_val
  refine isOpen_induced_iff.2 ⟨{h | ∀ i j, ent h i j - ent γ i j ∈ V}, ?_, ?_⟩
  · simp only [Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      hVo.preimage ((hent.matrix_elem i j).sub continuous_const)
  · ext γ'
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_singleton_iff]
    obtain ⟨g', hg'⟩ := hfin_exists_mat σ J γ'
    obtain ⟨g, hg⟩ := hfin_exists_mat σ J γ
    have e' : ∀ i j, ent γ' i j = inclR (AF F) ((g' : Matrix (Fin M) (Fin M) E) i j) := fun i j => by
      show ((γ' : HR (AF F) σ J) : GL (Fin M) (AF F ⊗[F] E)) i j = _
      rw [← hg', hfin_entry]
    have e : ∀ i j, ent γ i j = inclR (AF F) ((g : Matrix (Fin M) (Fin M) E) i j) := fun i j => by
      show ((γ : HR (AF F) σ J) : GL (Fin M) (AF F ⊗[F] E)) i j = _
      rw [← hg, hfin_entry]
    constructor
    · intro h
      have hmat : ent γ' = ent γ := by
        ext i j
        have := h i j
        rw [e' i j, e i j, ← map_sub] at this
        rw [e' i j, e i j, sub_eq_zero.1 (hV _ this)]
      exact Subtype.ext (Subtype.ext (Units.ext hmat))
    · rintro rfl i j
      rw [sub_self]; exact hV0

theorem hfin_countable (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) :
    Countable (HFinIn (AF F) σ J) := by
  have hE : Countable E :=
    Function.Injective.countable (Module.finBasis ℚ E).equivFun.injective
  have hGL : Countable (GL (Fin M) E) :=
    Function.Injective.countable (f := fun g : GL (Fin M) E => fun i j => (g : Matrix (Fin M) (Fin M) E) i j)
      (fun g g' h => Units.ext (Matrix.ext fun i j => congrFun (congrFun h i) j))
  choose g hg using hfin_exists_mat σ J
  exact Function.Injective.countable (f := g) fun γ γ' h =>
    Subtype.ext (Subtype.ext (by rw [← hg γ, ← hg γ', h]))


end Formalism.IndefR.Eqv.G5
end
end

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta MeasureTheory NumberField

namespace Formalism.IndefR.Eqv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : D7)

theorem ga_facts (V : HSp D) :
    IsTopologicalGroup (GA D V) ∧ T2Space (GA D V) ∧ LocallyCompactSpace (GA D V) ∧
      SecondCountableTopology (GA D V) ∧ BorelSpace (GA D V) := by
  obtain ⟨h1, h2, h3⟩ := G5.af_facts D.host.F
  exact G5.ha_facts (AF D.host.F) D.sp.cm.deg2 D.sp.cm.sig V.gram

theorem ae_facts : IsTopologicalRing (AE D) ∧ T2Space (AE D) ∧ LocallyCompactSpace (AE D) ∧
    SecondCountableTopology (AE D) ∧ BorelSpace (AE D) := by
  obtain ⟨h1, h2, h3⟩ := G5.af_facts D.host.F
  exact G5.tens_facts (AF D.host.F) D.sp.cm.deg2

theorem gQDiscrete_holds : GQDiscrete D := fun V => G5.hfin_disc D.sp.cm.sig V.gram

theorem gQ_countable (V : HSp D) : Countable (GQ V) := G5.hfin_countable D.sp.cm.sig V.gram

theorem measurableMul_GA (V : HSp D) : MeasurableMul (GA D V) := by
  obtain ⟨h1, -, -, -, h5⟩ := ga_facts D V
  infer_instance

theorem measurableMul₂_GA (V : HSp D) : MeasurableMul₂ (GA D V) := by
  obtain ⟨h1, -, -, h4, h5⟩ := ga_facts D V
  infer_instance

theorem gfC_secondCountable (V : HSp D) : SecondCountableTopology (GfC V) := by
  obtain ⟨-, -, -, h4, -⟩ := ga_facts D V
  exact Topology.IsInducing.subtypeVal.secondCountableTopology

theorem fundDomExists_holds : FundDomExists D := fun V => by
  obtain ⟨h1, -, -, h4, h5⟩ := ga_facts D V
  have := gQDiscrete_holds D V
  exact G5.fdom_exists_all (GQ V)

end Formalism.IndefR.Eqv

end
end
