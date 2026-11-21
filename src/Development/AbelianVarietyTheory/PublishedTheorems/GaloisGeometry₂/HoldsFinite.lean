import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.AlgebraicCharacterWD
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ConclusionFinite

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.LocLanglands GlobalTheory.WeilDeligne Polynomial TensorProduct Module
open GlobalTheory.Published.ParamAboveModel

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.Published.CharWDModel

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) (ι : Om l ≃+* ℂ)
  {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
  {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
  [IsAlgClosure E Ω] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}
  (Bw : LocBridge l E Ω (Dec (F := E) A) O) (h : IsPlaceOver A w) (hj : GlobalTheory.Pst.Induces Bw)

theorem holds_finite {art : Ideles E →* Gab E Ω} (ha : IsGlobalArtin art) {χ : HChar E} {k : ℕ} (hk : 0 < k)
    (hχ : χ.OrderDvd k) {μ : G E Ω →* (Qbar l)ˣ} (hμ : Continuous μ) (hL : IsLAdicOf art ι χ 0 μ)
    (hr : IsPstAt P Bw ((rk1 μ).comp (Dec (F := E) A).subtype))
    {ξ : (w.adicCompletion E)ˣ →* ℂˣ} (hξ : GlobalTheory.NPin.IsComp χ w ξ)
    {a : Weil h →* (w.adicCompletion E)ˣ} (ha' : IsLocalArtin h a) :
    wdAt P ι Bw h hj ((rk1 μ).comp (Dec (F := E) A).subtype) =
      WD.lpOfChar h (ξ.comp a) (ha'.smooth hξ.1) := by
  obtain rfl := eq_loc hξ
  have ho : IsOpen (μ.ker : Set (G E Ω)) :=
    isOpen_ker_of_pow μ hμ hk fun g => DFunLike.congr_fun (hL.pow_eq_one ha.quot.surjective hχ) g
  have ho2 : IsOpen {g : GK Bw.Kw | μ (Bw.e.symm g : Dec (F := E) A) = 1} :=
    ho.preimage (continuous_subtype_val.comp Bw.e_symm_cont)
  obtain ⟨U, hU, hU'⟩ := isOpen_induced_iff.1 ho2
  have h1 : (1 : GQ l) ∈ U := by
    have : (1 : GK Bw.Kw) ∈ Subtype.val ⁻¹' U := by rw [hU']; simp
    exact this
  obtain ⟨K', hK1, hK2⟩ := (krullTopology_mem_nhds_one_iff _ _ U).1 (hU.mem_nhds h1)
  have := nontrivial_B P
  refine eq_lpOfChar h _ (Test.lpDim_wdAt P ι Bw h hj _) _ _ fun σ => ?_
  have key := mem_eig_wdAt P ι Bw h hj μ hr 1 one_ne_zero 1 one_ne_zero (by simp) (fun _ => 1) (by simp) (by simp)
    ⟨K', hK1⟩ (fun g hg => by
      have : Bw.e g ∈ Subtype.val ⁻¹' U := hK2 hg
      rw [hU'] at this
      have h2 : μ g = 1 := by simpa using this
      simp [h2]) σ
  rw [hL.loc_away (Or.inr rfl) _ _ (ha'.glob art ha σ)] at key
  simpa using key


omit P Bw h hj in

theorem hypotheses_met (hA : GlobalArtinReciprocity) (hL : LocalLanglandsGL) (hw : w ∈ placesOver E l) :
    ∃ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) ∧ ∃ art : Ideles E →* Gab E Ω, IsGlobalArtin art ∧
      ∃ μ : G E Ω →* (Qbar l)ˣ, IsAlgPos (Model.absPow E (1 : ℕ)) (fun _ => ((1 : ℕ) : ℤ)) ∧ Continuous μ ∧
      IsLAdicOf art ι (Model.absPow E (1 : ℕ)) (fun _ => ((1 : ℕ) : ℤ)) μ ∧
      ∃ (A : ValuationSubring Ω) (h : IsPlaceOver A w) (LL : FinExt l)
        (Bw : LocBridge l E Ω (Dec (F := E) A) ↥(OL LL)), GlobalTheory.Pst.Induces Bw ∧
        (∃ ξ, GlobalTheory.NPin.IsComp (Model.absPow E (1 : ℕ)) w ξ) ∧ ∃ a, IsLocalArtin h a := by
  obtain ⟨P, AI, hT, art, ha, μ, h1, h2, h3, A, h, LL, Bw, hj, hξ, rc, a, ha', -⟩ :=
    ParamAboveModel.hypotheses_met (Ω := Ω) ι hA hL hw
  exact ⟨P, AI, hT, art, ha, μ, h1, h2, h3, A, h, LL, Bw, hj, hξ, a, ha'⟩

end GlobalTheory.Published.CharWDModel

end
