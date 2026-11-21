import Mathlib
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts

set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.Reg.PChartModel

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

theorem mem_R_of_mem_B (P : PChart Xo c β) (e : P.Ω) {x : P.Ω} (hx : x ∈ P.B) : x ∈ P.R e := by
  have h : P.B ≤ (P.R e).toSubring := by
    refine Subring.closure_le.2 ?_
    rintro y (⟨a, rfl⟩ | hy)
    · exact (P.R e).algebraMap_mem _
    · exact Algebra.subset_adjoin (Set.mem_insert_of_mem _ hy)
  exact h hx


theorem isFractionRing_R (P : PChart Xo c β) (e : P.Ω) : IsFractionRing (P.R e) P.Ω := by
  refine IsFractionRing.of_field _ _ fun z => ?_
  have hz : z ∈ Subfield.closure (Set.range (algebraMap c.F P.Ω) ∪ (P.gens : Set P.Ω)) := by
    rw [P.frac]; trivial
  obtain ⟨a, ha, b, hb, rfl⟩ := Subfield.mem_closure_iff.1 hz
  have h : Subring.closure (Set.range (algebraMap c.F P.Ω) ∪ (P.gens : Set P.Ω)) ≤ (P.R e).toSubring := by
    refine Subring.closure_le.2 ?_
    rintro y (⟨a, rfl⟩ | hy)
    · exact (P.R e).algebraMap_mem _
    · exact Algebra.subset_adjoin (Set.mem_insert_of_mem _ hy)
  exact ⟨⟨a, h ha⟩, ⟨b, h hb⟩, rfl⟩





theorem nonempty_of_point (hbc : FrBC Xo c) (y₀ : FrPt Xo c c.F)
    (hy : ∀ (T : CDVR) (io : c.F →+* T.Fr), letI := io.toAlgebra
      (∀ a : O, io (β a) ∈ Set.range (algebraMap T.V T.Fr)) →
      ∀ z : FrPt Xo c T.Fr, FrMap (Algebra.ofId c.F T.Fr) y₀ z → Integral T io z) :
    Nonempty (PChart Xo c β) := by
  let R : Subalgebra c.F c.F := Algebra.adjoin c.F (insert (1 : c.F)⁻¹ (((∅ : Finset c.F)) : Set c.F))
  obtain ⟨y₁, h₁⟩ := hbc c.F R (Algebra.ofId c.F R) y₀
  obtain ⟨y₂, h₂⟩ := hbc R c.F R.val y₁
  have hbij : Function.Bijective (Algebra.ofId c.F R) :=
    ⟨(Algebra.ofId c.F R).toRingHom.injective, fun x => ⟨x.1, Subtype.ext rfl⟩⟩
  refine ⟨{
    Ω := c.F
    gens := ∅
    frac := top_le_iff.1 fun x _ => Subfield.subset_closure (Or.inl ⟨x, rfl⟩)
    es := {1}
    es_ne := Finset.singleton_nonempty _
    es_mem := fun e he => by
      rw [Finset.mem_singleton.1 he]; exact ⟨one_ne_zero, Subring.one_mem _⟩
    sm := fun e he => by
      obtain rfl := Finset.mem_singleton.1 he
      exact Algebra.Smooth.of_equiv (AlgEquiv.ofBijective _ hbij)
    yg := y₂
    y := fun e he => (Finset.mem_singleton.1 he).symm ▸ y₁
    gen := fun e he => by
      obtain rfl := Finset.mem_singleton.1 he
      exact h₂
    int := fun e he T io => by
      obtain rfl := Finset.mem_singleton.1 he
      letI := io.toAlgebra
      intro ψ hO _ z hz
      have : FrMap (ψ.comp (Algebra.ofId c.F R)) y₀ z := frMap_trans _ _ _ _ ψ _ _ _ h₁ hz
      rw [Subsingleton.elim (ψ.comp (Algebra.ofId c.F R)) (Algebra.ofId c.F T.Fr)] at this
      exact hy T io hO z this }⟩

theorem evR_map (h : EvLaws Xo c) {f : Rul Xo c}
    (hf : IsNatural (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) f)
    {S T : Type} [CommRing S] [IsReduced S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T)
    {y : FrPt Xo c S} {z : FrPt Xo c T} (hyz : FrMap φ y z) : evR Xo c f z = φ (evR Xo c f y) := by
  have hy := h.test S y
  have h1 := hy.choose_spec.choose_spec.choose_spec
  have h2 := frMap_trans _ _ _ _ φ _ _ _ h1 hyz
  have hz : FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) z := ⟨_, _, _, h2⟩
  unfold evR evalAt
  rw [dif_pos hy, dif_pos hz]
  exact h.wd f hf T _ _ _ (φ.comp _) _ _ z hz.choose_spec.choose_spec.choose_spec h2


end GlobalTheory.Reg.PChartModel
