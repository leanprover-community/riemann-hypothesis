import Formalism.AdmissibleDesigns.MemImageOfTensorSum
import Formalism.AdmissibleDesigns.ExistsWildInertiaCyclotomicGenerator
import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypes

section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Formalism.BasicNotions Classical

namespace Formalism.MainNotions.N.KUnr

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions Formalism.MainNotions.N

section Gen

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {p : ℕ} [Fact p.Prime]

theorem exists_unr_dec (A : ValuationSubring Ω) (hp : A.valuation (p : Ω) < 1) :
    ∃ χ : ↥(A.decompositionSubgroup F) → ℤ_[p], Continuous χ ∧ (∀ g h, χ (g * h) = χ g + χ h) ∧
      (∀ g : ↥(A.decompositionSubgroup F), (g : Ω ≃ₐ[F] Ω) ∈ Ine (F := F) A → χ g = 0) ∧ ∃ g, χ g = 1 := by
  exact hT2Core.out.unr A hp

end Gen

section Rec

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)

private lemma plOf_colIdx (l : K.Col i dc) : K.plOf i dc (K.colIdx i dc l) = l.1 := by
  have hmem : l.1 ∈ K.plSet i dc := by
    simp only [K.plSet, Finset.mem_union]
    exact Or.inl (Or.inr l.2)
  have hlt : ((K.plSet i dc).equivFin ⟨l.1, hmem⟩ : ℕ) < (K.plSet i dc).card := Fin.is_lt _
  unfold K.colIdx K.idx K.plOf
  rw [dif_pos hmem, dif_pos hlt]
  simp

theorem col_over (l : K.Col i dc) : K.plOf i dc (K.colIdx i dc l) ∈ placesOver D.host.E (D.nd.l i) := by
  rw [plOf_colIdx]
  first
  | exact (dc.cover l.1).mp (Or.inr l.2)
  | exact ((dc.cover l.1).mp (Or.inr l.2)).1
  | (have h := (dc.cover l.1).mp (Or.inr l.2); done)

theorem col_hp (l : K.Col i dc) :
    (K.Aw i dc (K.colIdx i dc l)).valuation ((D.nd.l i : ℕ) : D.nd.Om) < 1 := by
  have hov := col_over i dc l
  rw [plOf_colIdx] at hov
  unfold K.Aw
  rw [plOf_colIdx]
  have h2 := (D.nd.plOm.2 l.1 ((D.nd.l i : ℕ) : 𝓞 D.host.E)).mpr hov
  simpa using h2

theorem unrHom (l : K.Col i dc) : KFin.UnrHom i dc l := by
  obtain ⟨χ, hc, hm, hI, g1, h1⟩ :=
    exists_unr_dec (F := D.host.E) (K.Aw i dc (K.colIdx i dc l)) (col_hp i dc l)
  refine ⟨fun g => algebraMap ℤ_[D.nd.l i] (D.nd.O i) (χ g), ⟨fun g h => ?_, fun g hg => ?_, fun hn => ?_⟩, g1, ?_⟩
  · show algebraMap ℤ_[D.nd.l i] (D.nd.O i) (χ (g * h)) = _ + _
    rw [hm, map_add]
  · have hg' : ((g : D.nd.Om ≃ₐ[D.host.E] D.nd.Om)) ∈ Ine (F := D.host.E) (K.Aw i dc (K.colIdx i dc l)) :=
      Subgroup.mem_subgroupOf.1 hg
    show algebraMap ℤ_[D.nd.l i] (D.nd.O i) (χ g) = 0
    rw [hI g hg', map_zero]
  · have hf : Continuous fun g : ↥(KFin.Γc i dc l) => algebraMap ℤ_[D.nd.l i] (D.nd.O i) (χ g) :=
      (K.Topo.continuous_alg i).comp hc
    have e1 : ∀ c : D.nd.O i, KHf.eK (D.nbr i _ hn) (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)) c) =
        ((D.nbr i _ hn).eO c : Br.LLw (D.nbr i _ hn)) := fun c => by
      rw [KHf.eK_apply, Br.toLLK_alg]
      rfl
    simp only [e1]
    exact continuous_subtype_val.comp ((D.nbr i _ hn).eO_cont.comp (hf.comp (Br.iota_cont D.nbr i _ hn)))
  · show algebraMap ℤ_[D.nd.l i] (D.nd.O i) (χ g1) = 1
    rw [h1, map_one]

end Rec

end Formalism.MainNotions.N.KUnr
end
end

section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Formalism.BasicNotions Classical

namespace Formalism.MainNotions.N.KUnr

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations

section Loc

variable {O : Type} [CommRing O] [IsDomain O] {Γ : Type} [Group Γ] {M : Type} [AddCommGroup M] [Module O M]

theorem locRep_triv (g : Γ) (x : KHf.MK (O := O) M) :
    KHf.locRep (Representation.trivial O Γ M) g x = x := by
  induction x using LocalizedModule.induction_on with
  | h m s =>
    show LocalizedModule.map (nonZeroDivisors O) (Representation.trivial O Γ M g) (LocalizedModule.mk m s) =
      LocalizedModule.mk m s
    rw [LocalizedModule.map_mk]
    rfl

end Loc

section Rec

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i) (δO : D.nd.O i)

theorem col_mem (l : K.Col i dc) : K.plOf i dc (K.colIdx i dc l) ∈ dc.col := by
  have h : l.1 ∈ K.plSet i dc := by
    unfold K.plSet
    simp [l.2]
  rw [K.colIdx, K.plOf_idx i dc h]
  exact l.2



end Rec

end Formalism.MainNotions.N.KUnr
end
end
