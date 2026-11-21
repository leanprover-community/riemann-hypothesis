import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConjSPV
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharLocalComponentExistsUniqueUnitary
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EqOrIsConjPlaceOfOverSplitPlace
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConjugateSplitPlaceEqConjugatePlaceAndEmbeddingStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSplitPlaceParahoricSubgroupCharacter
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLocalComponentEigenvectorAtSplitPlaceIsoty
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsParahoricTypeVectorAtConjugatePlace
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLevelCharacterAtConjugateSplitPlace

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem GlobalTheory.VTypeTame.ramified_of_isComp : ∀ (E : Type) [Field E] [NumberField E] (χ : HChar E) (w : HeightOneSpectrum (𝓞 E)) (ξ : (w.adicCompletion E)ˣ →* ℂˣ), IsComp χ w ξ → ¬ GlobalTheory.SplitWeil.IsUnram ξ → ¬ χ.UnrAt w := by
  intro E _ _ χ w ξ hξ hn hu
  have hc : IsComp χ w (χ.loc w) := ⟨GlobalTheory.HeckeComp.smooth_loc χ w, fun _ => rfl⟩
  have he : ξ = χ.loc w := GlobalTheory.HeckeComp.eq_of_isComp hc hξ
  apply hn
  intro x hx
  rw [he]
  apply hu x
  have : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have h1 := ValuativeRel.isEquiv (ValuativeRel.valuation (w.adicCompletion E))
    (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ)))
  show Valued.v (x : w.adicCompletion E) = 1
  exact h1.eq_one_iff_eq_one.1 hx
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeChar_ramified_of_ramified_localComponent : ∀ (E : Type) [Field E] [NumberField E] (χ : HChar E) (w : HeightOneSpectrum (𝓞 E)) (ξ : (w.adicCompletion E)ˣ →* ℂˣ), IsComp χ w ξ → ¬ GlobalTheory.SplitWeil.IsUnram ξ → ¬ χ.UnrAt w := by
  atlas_forward_decl GlobalTheory.VTypeTame.ramified_of_isComp
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.GeoUnder

theorem exists_under_in_qPl : ∀ (D : D7) (χ : HChar D.host.E) (w : PlE D.host), (∀ k, w ∉ placesOver D.host.E (D.host.g k)) → ¬ χ.UnrAt w → ∃ v, NG.OverPl w v ∧ v ∈ qPl D χ := by
  intro D χ w hg hχ
  have hne : w.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) ≠ ⊥ := by
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot w.ne_bot
    have hint : IsIntegral ℤ x := Algebra.IsIntegral.isIntegral x
    exact Ideal.comap_ne_bot_of_integral_mem hx0 hx (hint.tower_top)
  let v : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) :=
    { asIdeal := w.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E))
      isPrime := Ideal.comap_isPrime _ _
      ne_bot := hne }
  refine ⟨v, rfl, ?_, w, rfl, hχ⟩
  rintro ⟨w', hw', k, hk⟩
  apply hg k
  have h1 : ((D.host.g k : ℕ) : 𝓞 (maximalRealSubfield D.host.E)) ∈ v.asIdeal := by
    rw [← hw']
    show algebraMap _ _ _ ∈ w'.asIdeal
    rw [map_natCast]; exact hk
  show ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal
  have h2 := h1
  change algebraMap _ _ _ ∈ w.asIdeal at h2
  rwa [map_natCast] at h2

end GlobalTheory.GeoUnder
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_realSubfield_place_in_ramified_set : ∀ (D : D7) (χ : HChar D.host.E) (w : PlE D.host), (∀ k, w ∉ placesOver D.host.E (D.host.g k)) → ¬ χ.UnrAt w → ∃ v, NG.OverPl w v ∧ v ∈ qPl D χ := by
  atlas_forward_decl GlobalTheory.GeoUnder.exists_under_in_qPl
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_or_isConjPlace_of_over_splitPlace : ∀ (D : D7) (s : SplitPlace D.host.E) (w : PlE D.host), NG.OverPl w s.v → s.w = w ∨ IsConjPl D.host w s.w := by
  first | exact @GlobalTheory.SplitPlaceOver.eq_or_isConjPl | exact GlobalTheory.SplitPlaceOver.eq_or_isConjPl | (intros; apply GlobalTheory.SplitPlaceOver.eq_or_isConjPl <;> assumption)
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_splitPlaceParahoric_subgroup_character : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (s : SplitPlace L) (r : ℕ) (J : Subgroup (GAf L n)) (χ : J →* ℂˣ) (ξ : (s.v.adicCompletion (maximalRealSubfield L))ˣ →* ℂˣ), NG.LevelPara J χ s r ξ → (∃ N : ℕ, ∀ u : (s.v.adicCompletion (maximalRealSubfield L))ˣ, Valued.v ((u : s.v.adicCompletion (maximalRealSubfield L)) - 1) ≤ WithZero.exp (-(N : ℤ)) → ξ u = 1) → ∃ (K : Subgroup (GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L)))) (θ : K →* ℂˣ), (∀ g, g ∈ K ↔ NG.ParaRT s r g) ∧ (∀ g (h : g ∈ K) (d : (s.v.adicCompletion (maximalRealSubfield L))ˣ), (d : s.v.adicCompletion (maximalRealSubfield L)) = NG.detDD s r g → θ ⟨g, h⟩ = ξ d) ∧ (∀ g ∈ K, g ∈ Formalism.UG.GLint (Fin n) (s.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring) ∧ IsOpen (θ.ker : Set K) ∧ ∀ κ, TrivOutside {s.v} κ → ∀ (hJ : κ ∈ J) (h : s.loc n κ ∈ K), χ ⟨κ, hJ⟩ = θ ⟨s.loc n κ, h⟩ := by
  first | exact @GlobalTheory.ParaLevel.exists_parahoric_char | exact GlobalTheory.ParaLevel.exists_parahoric_char | (intros; apply GlobalTheory.ParaLevel.exists_parahoric_char <;> assumption)
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_localComponent_eigenvector_at_splitPlace_isotypic : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n) (S : Submodule ℂ (GAf L n → a.W)), NG.IsIrrRep a.ρ S → ∀ (s : SplitPlace L) (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L))), IsLocS S s σ → ∀ c : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L, Continuous c → (∀ x : L, c (s.i x) = algebraMap L (s.w.adicCompletion L) x) → ∀ (K : Subgroup (GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L)))) (θ : K →* ℂˣ), (∀ g ∈ K, g ∈ Formalism.UG.GLint (Fin n) (s.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring) → IsOpen (θ.ker : Set K) → ∀ f ∈ NG.isoTyp a.ρ S, f ≠ 0 → (∀ κ, TrivOutside {s.v} κ → ∀ h : s.loc n κ ∈ K, NG.rt L n κ f = ((θ ⟨s.loc n κ, h⟩ : ℂˣ) : ℂ) • f) → ∃ u : σ.V, u ≠ 0 ∧ ∀ g (h : g ∈ K), σ.ρ (Matrix.GeneralLinearGroup.map c.toRingHom g) u = ((θ ⟨g, h⟩ : ℂˣ) : ℂ) • u := by
  first | exact @GlobalTheory.LocVec.main | exact GlobalTheory.LocVec.main | (intros; apply GlobalTheory.LocVec.main <;> assumption)
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SameParahoric

open Filter Topology

theorem denseRange_i {L : Type} [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L) :
    DenseRange (s.i : L → s.v.adicCompletion (maximalRealSubfield L)) := by
  refine (s.v.denseRange_algebraMap (maximalRealSubfield L)).mono ?_
  rintro _ ⟨y, rfl⟩
  exact ⟨algebraMap (maximalRealSubfield L) L y, s.i.commutes y⟩

theorem eq_comp {L : Type} [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L)
    (ξ : (s.v.adicCompletion (maximalRealSubfield L))ˣ →* ℂˣ) (μ : (s.w.adicCompletion L)ˣ →* ℂˣ)
    (c : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L) (hc : Continuous c)
    (hci : ∀ x : L, c (s.i x) = algebraMap L (s.w.adicCompletion L) x) (hμ : GlobalTheory.SmGL.IsSmoothChar μ) (N : ℕ)
    (hN : ∀ u : (s.v.adicCompletion (maximalRealSubfield L))ˣ,
      Valued.v ((u : s.v.adicCompletion (maximalRealSubfield L)) - 1) ≤ WithZero.exp (-(N : ℤ)) → ξ u = 1)
    (hglob : ∀ k : Lˣ, ξ (Units.map (s.i : L →* s.v.adicCompletion (maximalRealSubfield L)) k) =
      μ (Units.map (algebraMap L (s.w.adicCompletion L)).toMonoidHom k))
    (d : (s.v.adicCompletion (maximalRealSubfield L))ˣ) :
    ξ d = μ (Units.map c.toRingHom.toMonoidHom d) := by
  obtain ⟨z, hz⟩ := s.v.valuedAdicCompletion_surjective (maximalRealSubfield L) (WithZero.exp (-(N : ℤ)))
  have hξo : GlobalTheory.SmGL.IsSmoothChar ξ := by
    have hU : IsOpen {x : (s.v.adicCompletion (maximalRealSubfield L))ˣ |
        Valued.v ((x : s.v.adicCompletion (maximalRealSubfield L)) - 1) < Valued.v z} := by
      have h1 := (Valued.isOpen_ball (s.v.adicCompletion (maximalRealSubfield L)) (Valued.v.restrict z)).preimage
        (Units.continuous_val.sub (continuous_const (y := (1 : s.v.adicCompletion (maximalRealSubfield L)))))
      simpa only [Set.preimage_setOf_eq, Valuation.restrict_lt_iff, Pi.sub_apply] using h1
    refine Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset (hU.mem_nhds ?_) fun x hx => ?_)
    · simp only [Set.mem_setOf_eq, Units.val_one, sub_self, map_zero, hz]
      exact WithZero.exp_pos
    · have hx' : Valued.v ((x : s.v.adicCompletion (maximalRealSubfield L)) - 1) < Valued.v z := hx
      exact hN x (by rw [← hz]; exact hx'.le)
  have hcu : Continuous (Units.map c.toRingHom.toMonoidHom :
      (s.v.adicCompletion (maximalRealSubfield L))ˣ → (s.w.adicCompletion L)ˣ) := by
    rw [Units.continuous_iff]
    exact ⟨hc.comp Units.continuous_val, hc.comp Units.continuous_coe_inv⟩
  have hs := hξo.mul (hμ.comp _ hcu).inv
  have hcl := Subgroup.isClosed_of_isOpen _ hs
  refine mul_inv_eq_one.1 ?_
  by_contra hy
  obtain ⟨U, hU, hU'⟩ := Units.isEmbedding_val₀.isInducing.isOpen_iff.1 hcl.isOpen_compl
  have hyU : (d : s.v.adicCompletion (maximalRealSubfield L)) ∈ U := by
    have : d ∈ Units.val ⁻¹' U := by rw [hU']; exact hy
    exact this
  obtain ⟨k, hk1, hk2⟩ := (denseRange_i s).exists_mem_open
    (hU.inter isOpen_ne (t := {z | z ≠ 0})) ⟨d, hyU, d.ne_zero⟩
  have hk0 : k ≠ 0 := fun e => hk2 (by rw [e, map_zero])
  have h3 : Units.map (s.i : L →* s.v.adicCompletion (maximalRealSubfield L)) (Units.mk0 k hk0) ∈ Units.val ⁻¹' U := hk1
  rw [hU'] at h3
  refine h3 ?_
  have hm : Units.map c.toRingHom.toMonoidHom
      (Units.map (s.i : L →* s.v.adicCompletion (maximalRealSubfield L)) (Units.mk0 k hk0)) =
      Units.map (algebraMap L (s.w.adicCompletion L)).toMonoidHom (Units.mk0 k hk0) := Units.ext (hci k)
  show ξ _ * (μ (Units.map c.toRingHom.toMonoidHom _))⁻¹ = 1
  rw [hm, ← hglob]
  exact mul_inv_cancel _

theorem isParahoricVec_of_eigen : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L) (r t : ℕ) {W : Type} [AddCommGroup W] [Module ℂ W] (π : Representation ℂ (GL (Fin (r + t)) (s.w.adicCompletion L)) W) (ξ : (s.v.adicCompletion (maximalRealSubfield L))ˣ →* ℂˣ) (μ : (s.w.adicCompletion L)ˣ →* ℂˣ) (c : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L), Continuous c → (∀ x : L, c (s.i x) = algebraMap L (s.w.adicCompletion L) x) → GlobalTheory.SmGL.IsSmoothChar μ → (∃ N : ℕ, ∀ u : (s.v.adicCompletion (maximalRealSubfield L))ˣ, Valued.v ((u : s.v.adicCompletion (maximalRealSubfield L)) - 1) ≤ WithZero.exp (-(N : ℤ)) → ξ u = 1) → (∀ k : Lˣ, ξ (Units.map (s.i : L →* s.v.adicCompletion (maximalRealSubfield L)) k) = μ (Units.map (algebraMap L (s.w.adicCompletion L)).toMonoidHom k)) → ∀ u : W, (∀ g : GL (Fin (r + t)) (s.v.adicCompletion (maximalRealSubfield L)), NG.ParaRT s r g → ∀ d : (s.v.adicCompletion (maximalRealSubfield L))ˣ, (d : s.v.adicCompletion (maximalRealSubfield L)) = NG.detDD s r g → π (Matrix.GeneralLinearGroup.map c.toRingHom g) u = ((ξ d : ℂˣ) : ℂ) • u) → GlobalTheory.ThetaGL.IsParahoricVec μ π u := by
  intro L _ _ _ s r t W _ _ π ξ μ c hc hci hμ ⟨N, hN⟩ hglob u hvec
  have hE := GlobalTheory.ConjParahoric.isEquiv_of_continuous c hc
  have hlt : ∀ x, ValuativeRel.valuation _ x < 1 → Valued.v (c.symm x) < 1 := fun x hx =>
    (Valuation.isEquiv_iff_val_lt_one.1 hE).2 hx
  have hle : ∀ x, ValuativeRel.valuation _ x ≤ 1 →
      c.symm x ∈ (s.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring := fun x hx =>
    (Valuation.isEquiv_iff_val_le_one.1 hE).2 hx
  intro h hK hlow x hx
  obtain ⟨hi1, hi2⟩ := (GlobalTheory.SplitFlip.mem_KO_iff h).1 hK
  let g := Matrix.GeneralLinearGroup.map c.symm.toRingHom h
  have hg : ∀ a b, g.val a b = c.symm (h.val a b) := fun a b => rfl
  have hg' : ∀ a b, (g⁻¹).val a b = c.symm ((h⁻¹).val a b) := fun a b => rfl
  have hpara : NG.ParaRT s r g := by
    refine ⟨GlobalTheory.ConjParahoric.mem_GLint_of_entries _ g (fun a b => hg a b ▸ hle _ (hi1 a b))
      (fun a b => hg' a b ▸ hle _ (hi2 a b)), fun a b ha hb => ?_⟩
    rw [hg]
    have ea : Fin.natAdd r (⟨a.val - r, by omega⟩ : Fin t) = a := by ext; simp; omega
    have eb : Fin.castAdd t (⟨b.val, hb⟩ : Fin r) = b := by ext; simp
    have := hlow ⟨a.val - r, by omega⟩ ⟨b.val, hb⟩
    rw [ea, eb] at this
    exact hlt _ this
  have hDD : c.symm (x : s.w.adicCompletion L) = NG.detDD s r g := by
    rw [NG.detDD, ← Matrix.det_submatrix_equiv_self (GlobalTheory.ConjParahoric.lowerEquiv r t), hx]
    refine (RingHom.map_det c.symm.toRingHom _).trans ?_
    congr 1
  have key := hvec g hpara (Units.map c.symm.toRingHom.toMonoidHom x) hDD
  have hpp : Matrix.GeneralLinearGroup.map c.toRingHom g = h :=
    Units.ext (Matrix.ext fun a b => c.apply_symm_apply _)
  have hcc : Units.map c.toRingHom.toMonoidHom (Units.map c.symm.toRingHom.toMonoidHom x) = x :=
    Units.ext (c.apply_symm_apply _)
  rw [hpp, GlobalTheory.SameParahoric.eq_comp s ξ μ c hc hci hμ N hN hglob, hcc] at key
  exact key

end GlobalTheory.SameParahoric
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isParahoricTypeVector_of_upperParahoric_eigen : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L) (r t : ℕ) {W : Type} [AddCommGroup W] [Module ℂ W] (π : Representation ℂ (GL (Fin (r + t)) (s.w.adicCompletion L)) W) (ξ : (s.v.adicCompletion (maximalRealSubfield L))ˣ →* ℂˣ) (μ : (s.w.adicCompletion L)ˣ →* ℂˣ) (c : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L), Continuous c → (∀ x : L, c (s.i x) = algebraMap L (s.w.adicCompletion L) x) → GlobalTheory.SmGL.IsSmoothChar μ → (∃ N : ℕ, ∀ u : (s.v.adicCompletion (maximalRealSubfield L))ˣ, Valued.v ((u : s.v.adicCompletion (maximalRealSubfield L)) - 1) ≤ WithZero.exp (-(N : ℤ)) → ξ u = 1) → (∀ k : Lˣ, ξ (Units.map (s.i : L →* s.v.adicCompletion (maximalRealSubfield L)) k) = μ (Units.map (algebraMap L (s.w.adicCompletion L)).toMonoidHom k)) → ∀ u : W, (∀ g : GL (Fin (r + t)) (s.v.adicCompletion (maximalRealSubfield L)), NG.ParaRT s r g → ∀ d : (s.v.adicCompletion (maximalRealSubfield L))ˣ, (d : s.v.adicCompletion (maximalRealSubfield L)) = NG.detDD s r g → π (Matrix.GeneralLinearGroup.map c.toRingHom g) u = ((ξ d : ℂˣ) : ℂ) • u) → GlobalTheory.ThetaGL.IsParahoricVec μ π u := by
  atlas_forward_decl GlobalTheory.SameParahoric.isParahoricVec_of_eigen
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_level_character_at_conjugateSplitPlace : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (s : SplitPlace L) (K : Subgroup (GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L)))) (θ : K →* ℂˣ), (∀ g ∈ K, g ∈ Formalism.UG.GLint (Fin n) (s.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring) → IsOpen (θ.ker : Set K) → ∃ (K' : Subgroup (GL (Fin n) ((GlobalTheory.TypeTame.conjSP s).v.adicCompletion (maximalRealSubfield L)))) (θ' : K' →* ℂˣ), (∀ g ∈ K', g ∈ Formalism.UG.GLint (Fin n) ((GlobalTheory.TypeTame.conjSP s).v.adicCompletionIntegers (maximalRealSubfield L)).toSubring) ∧ IsOpen (θ'.ker : Set K') ∧ (∀ κ : GAf L n, (GlobalTheory.TypeTame.conjSP s).loc n κ ∈ K' ↔ s.loc n κ ∈ K) ∧ (∀ (κ : GAf L n) (h : s.loc n κ ∈ K) (h' : (GlobalTheory.TypeTame.conjSP s).loc n κ ∈ K'), θ' ⟨(GlobalTheory.TypeTame.conjSP s).loc n κ, h'⟩ = θ ⟨s.loc n κ, h⟩) ∧ ∀ g (hg : g ∈ K) (g' : GL (Fin n) ((GlobalTheory.TypeTame.conjSP s).v.adicCompletion (maximalRealSubfield L))), g'.val = (g⁻¹).val.transpose → ∃ h' : g' ∈ K', θ' ⟨g', h'⟩ = θ ⟨g, hg⟩ := by
  first | exact @GlobalTheory.TypeTame.exists_conj_level | exact GlobalTheory.TypeTame.exists_conj_level | (intros; apply GlobalTheory.TypeTame.exists_conj_level <;> assumption)
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_parahoricType_vector_at_conjugate_place : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L) (r t : ℕ) {W : Type} [AddCommGroup W] [Module ℂ W] (π : Representation ℂ (GL (Fin (r + t)) (s.w.adicCompletion L)) W) (ξ : (s.v.adicCompletion (maximalRealSubfield L))ˣ →* ℂˣ) (μ : (s.w.adicCompletion L)ˣ →* ℂˣ) (c : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L), Continuous c → (∀ x : L, c (s.i x) = algebraMap L (s.w.adicCompletion L) x) → GlobalTheory.SmGL.IsSmoothChar μ → GlobalTheory.SplitWeil.IsTame μ → (∃ N : ℕ, ∀ u : (s.v.adicCompletion (maximalRealSubfield L))ˣ, Valued.v ((u : s.v.adicCompletion (maximalRealSubfield L)) - 1) ≤ WithZero.exp (-(N : ℤ)) → ξ u = 1) → (∀ k : Lˣ, ξ (Units.map (s.i : L →* s.v.adicCompletion (maximalRealSubfield L)) k) = (μ (Units.map (algebraMap L (s.w.adicCompletion L)).toMonoidHom k))⁻¹) → ∀ u : W, u ≠ 0 → (∀ g h : GL (Fin (r + t)) (s.v.adicCompletion (maximalRealSubfield L)), NG.ParaRT s r g → h.val = (g⁻¹).val.transpose → ∀ d : (s.v.adicCompletion (maximalRealSubfield L))ˣ, (d : s.v.adicCompletion (maximalRealSubfield L)) = NG.detDD s r g → π (Matrix.GeneralLinearGroup.map c.toRingHom h) u = ((ξ d : ℂˣ) : ℂ) • u) → ∃ u' : W, u' ≠ 0 ∧ GlobalTheory.ThetaGL.IsParahoricVec μ π u' := by
  first | exact @GlobalTheory.ConjParahoric.exists_parahoricVec | exact GlobalTheory.ConjParahoric.exists_parahoricVec | (intros; apply GlobalTheory.ConjParahoric.exists_parahoricVec <;> assumption)
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField
  IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.TypeTame

theorem typeTame_of_ramified : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D), ∀ S : Reading P.T, IsTrue P S → ∀ i w hw, (∀ k, w ∉ placesOver D.host.E (D.host.g k)) → GlobalTheory.SplitWeil.IsTame (S i w hw).mu → ¬ GlobalTheory.SplitWeil.IsUnram (S i w hw).mu → TypeTame S i w hw := by
  intro hL D P S hT i w hw hg htame hram
  refine ⟨htame, hram, fun Q => ?_⟩
  obtain ⟨h1, h2⟩ := D.nd.j_range i
  let j : Fin D.R.m := ⟨D.nd.j i - 1, by omega⟩
  have hj : j.1 + 1 = D.nd.j i := by simp only [j]; omega
  have hcomp := hT.mu i w hw j hj
  obtain ⟨v, hov, hvq⟩ := GlobalTheory.T.exists_realSubfield_place_in_ramified_set D _ w hg (GlobalTheory.T.heckeChar_ramified_of_ramified_localComponent _ _ w _ hcomp hram)
  obtain ⟨s, ξ, hsv, hcs, hlp⟩ := P.H.level.para i j hj v hvq

  obtain ⟨f, hfI, hfT, hf0⟩ : ∃ f, f ∈ NG.isoTyp (P.M.loc i).wt.ρ (P.H.av.S i Q) ∧
      f ∈ NG.TypeSp (P.M.loc i).wt.ρ (P.M.loc i).J (P.M.loc i).χ ∧ f ≠ 0 := by
    obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (D.naut.typeV_ne i Q)
    rw [P.H.av.typeV] at hy
    refine ⟨(P.M.loc i).real y, hy, ?_, ?_⟩
    · rw [← (P.M.loc i).real_range]; exact ⟨y, rfl⟩
    · intro h; exact hy0 ((P.M.loc i).real_inj (h.trans (map_zero _).symm))
  obtain ⟨K, θ, hKm, hθ, hKi, hθo, hχθ⟩ := GlobalTheory.T.exists_splitPlaceParahoric_subgroup_character _ _ s D.R.r _ _ ξ hlp hcs.1
  have hfK : ∀ κ, TrivOutside {s.v} κ → ∀ h : s.loc D.R.nV κ ∈ K,
      NG.rt D.host.E D.R.nV κ f = ((θ ⟨s.loc D.R.nV κ, h⟩ : ℂˣ) : ℂ) • f := by
    intro κ hκ h
    have hJ : κ ∈ (P.M.loc i).J := (hlp.mem κ hκ).2 ((hKm _).1 h)
    rw [← hχθ κ hκ hJ h]
    exact hfT.2 ⟨κ, hJ⟩
  have hmu_eq : ∀ g (hg : NG.ParaRT s D.R.r g) (d : (s.v.adicCompletion (maximalRealSubfield D.host.E))ˣ),
      (d : s.v.adicCompletion (maximalRealSubfield D.host.E)) = NG.detDD s D.R.r g →
      θ ⟨g, (hKm g).2 hg⟩ = ξ d := fun g hg d hd => hθ g _ d hd
  rcases GlobalTheory.T.eq_or_isConjPlace_of_over_splitPlace D s w (hsv ▸ hov) with hsw | hconj
  · subst hsw
    obtain ⟨c, T, hc, hci, -⟩ := hT.rep i s hw Q
    obtain ⟨u, hu0, hu⟩ := GlobalTheory.T.exists_localComponent_eigenvector_at_splitPlace_isotypic _ _ (P.M.loc i).wt (P.H.av.S i Q) (P.H.av.irr i Q) s _ (hT.rep i s hw Q) c hc hci
      K θ hKi hθo f hfI hf0 hfK
    refine ⟨u, hu0, GlobalTheory.T.isParahoricTypeVector_of_upperParahoric_eigen _ s D.R.r D.R.t _ ξ _ c hc hci hcomp.1 hcs.1 (fun k => (hcs.2 k).trans (hcomp.2 k).symm) u ?_⟩
    intro g hg d hd
    rw [← hmu_eq g hg d hd]
    exact hu g _
  · obtain ⟨hw', hci'⟩ := GlobalTheory.T.conjugateSplitPlace_eq_conjugatePlace_and_embedding D s w hconj
    subst hw'
    obtain ⟨c, T, hc, hci, -⟩ := hT.rep i (GlobalTheory.TypeTame.conjSP s) hw Q
    obtain ⟨K', θ', hK'i, hθ'o, hK'iff, hθ'eq, hK'of⟩ := GlobalTheory.T.exists_level_character_at_conjugateSplitPlace _ _ s K θ hKi hθo
    have hfK' : ∀ κ, TrivOutside {(GlobalTheory.TypeTame.conjSP s).v} κ → ∀ h' : (GlobalTheory.TypeTame.conjSP s).loc D.R.nV κ ∈ K',
        NG.rt D.host.E D.R.nV κ f = ((θ' ⟨(GlobalTheory.TypeTame.conjSP s).loc D.R.nV κ, h'⟩ : ℂˣ) : ℂ) • f := by
      intro κ hκ h'
      have h := (hK'iff κ).1 h'
      rw [hθ'eq κ h h']
      exact hfK κ hκ h
    obtain ⟨u, hu0, hu⟩ := GlobalTheory.T.exists_localComponent_eigenvector_at_splitPlace_isotypic _ _ (P.M.loc i).wt (P.H.av.S i Q) (P.H.av.irr i Q) (GlobalTheory.TypeTame.conjSP s) _
      (hT.rep i (GlobalTheory.TypeTame.conjSP s) hw Q) c hc hci K' θ' hK'i hθ'o f hfI hf0 hfK'
    have hcsd : IsCSD D.host (P.tp.tup (D.nd.mu i) j) := by
      rw [← P.chr.muC i j hj]; exact (P.chr.csd _).1 (D.naut.muC_csd i)
    refine GlobalTheory.T.exists_parahoricType_vector_at_conjugate_place _ (GlobalTheory.TypeTame.conjSP s) D.R.r D.R.t _ ξ _ c hc hci hcomp.1 htame hcs.1 ?_ u hu0 ?_
    · intro k
      have e : Units.map ((GlobalTheory.TypeTame.conjSP s).i : D.host.E →* s.v.adicCompletion (maximalRealSubfield D.host.E)) k =
          Units.map (s.i : D.host.E →* s.v.adicCompletion (maximalRealSubfield D.host.E))
            (Units.map (MonoidHomClass.toMonoidHom D.host.conj) k) := by
        ext; simp [hci']
      have e2 := hcs.2 (Units.map (MonoidHomClass.toMonoidHom D.host.conj) k)
      have e3 := hcsd.1 _ _ hconj k
      have e4 := hcomp.2 k
      rw [e, e2, e3, e4]
    · intro g h hg hh d hd
      obtain ⟨h', e⟩ := hK'of g ((hKm g).2 hg) h hh
      rw [← hmu_eq g hg d hd, ← e]
      exact hu h h'

end GlobalTheory.TypeTame
end
