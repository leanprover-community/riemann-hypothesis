import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GermSys
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GenericPartDenseProOpen
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AmplePointsLocalizedModel
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeLatticeDvrDegree
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FormalIsomorphismTransport
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FormalHermitianActionPairing
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.GermHodgeLatticeExists
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.EqMulInversePow
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HermitianSignatureCharacter
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.CharacteristicPolynomialFreeGenerators
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.RepresentationBasisLinearIndependent
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HeightCharFreeGeometric
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FormalGermBaseChange
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.HodgeFreeEveryStalk
import BuildAid.ForwardExisting
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ModelFibresPowerFree
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PowFnsOfAbelianGeneric
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelExistsUniqueEquivStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProperNormalCompactification

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_lattice_dvr_degree : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X : Scheme.{0}) (t : SAB H X) (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Sp Ω ⟶ X) (d r : ℕ) (M : LieModel t.G ξ (Fin d → Ω)) (S : GermSys t ξ M) (ρ : 𝓞 E →+* Module.End Ω (Fin d → Ω)) (𝓗 : HodgeLat M.lat ρ H.bar r) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O Ω] (s : X ⟶ Sp O) [IsSeparated s] [LocallyOfFiniteType s] (ϖ : O) (p : ℕ) (σ : E →+* Ω), Irreducible ϖ → p.Prime → ϖ ∣ (p : O) → ξ ≫ s = spMap (algebraMap O Ω) → IsCptGen ξ → PowFns t → S.Gives 𝓗 → (∀ q : Cpt ξ, (p : X.residueField q.1) = 0 → FibPF t q.1) → Nat.card (E →+* Ω) = Module.finrank ℚ E → (∀ (s' : E →+* Ω) (a : 𝓞 E), s' (a : E) ∈ (algebraMap O Ω).range) → 𝓗.DegZero σ (algebraMap O Ω ϖ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.germ_degZero | exact GlobalTheory.CompanionTheory.Ar.Flat.germ_degZero | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.germ_degZero <;> assumption)
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem germ_gives_hodgeLat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X : Scheme.{0}) (t : SAB H X) (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Sp Ω ⟶ X) (d r : ℕ) (M : LieModel t.G ξ (Fin d → Ω)) (S : GermSys t ξ M) (ρ : 𝓞 E →+* Module.End Ω (Fin d → Ω)), IsCptGen ξ → M.IsActOf t.act.act ρ → (∀ q : Cpt ξ, HFree (S.g q).B r) → ∃ 𝓗 : HodgeLat M.lat ρ H.bar r, S.Gives 𝓗 := by
  intro E _ _ _ H _ hstar X t Ω _ _ ξ d r M S ρ _hcg hact hfree
  classical
  have hρeq : ∀ (a : 𝓞 E) (v : Fin d → Ω),
      (GlobalTheory.CompanionTheory.Ar.Conj.rho S.g₀.B a).mulVec v = ρ a v := fun a v =>
    M.inj ((S.act₀ a v).trans (hact a v).symm)
  obtain ⟨⟨ρ0, hρ0⟩, -, -⟩ := GlobalTheory.T.formal_hermitian_action_pairing Ω d (𝓞 E) S.g₀.B
  let dd : ((Fin d → Ω) × (Fin d → Ω)) ≃ₗ[Ω] (Fin d → Ω) × Module.Dual Ω (Fin d → Ω) :=
    PositivityTheory.Xgn.GermHodgeLattice.dd Ω d
  have hdd : ∀ y, dd y = (y.1, dotProductBilin Ω Ω y.2) := fun y =>
    PositivityTheory.Xgn.GermHodgeLattice.dd_apply y
  have hsymm : ∀ y, ((dd.symm y).1, dotProductBilin Ω Ω (dd.symm y).2) = y := fun y => by
    rw [← hdd]; exact dd.apply_symm_apply y
  have hr1 : ∀ (a : 𝓞 E) (z : (Fin d → Ω) × (Fin d → Ω)),
      (GlobalTheory.CompanionTheory.Ar.Conj.rhoH S.g₀.B a z).1 = (GlobalTheory.CompanionTheory.Ar.Conj.rho S.g₀.B a).mulVec z.1 := by
    intro a z; simp [GlobalTheory.CompanionTheory.Ar.Conj.rhoH, Matrix.toLin'_apply]
  have hr2 : ∀ (a : 𝓞 E) (z : (Fin d → Ω) × (Fin d → Ω)),
      (GlobalTheory.CompanionTheory.Ar.Conj.rhoH S.g₀.B a z).2 =
        (GlobalTheory.CompanionTheory.Ar.Conj.rho S.g₀.B (star a)).transpose.mulVec z.2 -
          (GlobalTheory.CompanionTheory.Ar.Conj.bil (S.g₀.B.ad a) 1 1).transpose.mulVec z.1 := by
    intro a z; simp [GlobalTheory.CompanionTheory.Ar.Conj.rhoH, Matrix.toLin'_apply]
  let ρH : 𝓞 E →+* Module.End Ω ((Fin d → Ω) × Module.Dual Ω (Fin d → Ω)) :=
    { toFun := fun a => dd.toLinearMap ∘ₗ ρ0 a ∘ₗ dd.symm.toLinearMap
      map_one' := LinearMap.ext fun y => by simp
      map_mul' := fun a b => LinearMap.ext fun y => by simp [Module.End.mul_apply]
      map_zero' := LinearMap.ext fun y => by simp
      map_add' := fun a b => LinearMap.ext fun y => by simp }
  have hρH : ∀ a y, ρH a y = dd (GlobalTheory.CompanionTheory.Ar.Conj.rhoH S.g₀.B a (dd.symm y)) := by
    intro a y; show dd (ρ0 a (dd.symm y)) = _; rw [hρ0]
  let HL : GlobalTheory.CompanionTheory.Ar.Lat ξ ((Fin d → Ω) × Module.Dual Ω (Fin d → Ω)) := fun p =>
    Submodule.map (dd.toLinearMap.restrictScalars (GlobalTheory.CompanionTheory.Ar.regAt ξ p))
      (GlobalTheory.CompanionTheory.Ar.Flat.stdLat (GlobalTheory.CompanionTheory.Ar.regAt ξ p)
        (GlobalTheory.CompanionTheory.Ar.Conj.transH (S.φ p) (S.ψ p) (S.lam p)))
  have hmem : ∀ p y, dd y ∈ HL p ↔
      y ∈ GlobalTheory.CompanionTheory.Ar.Flat.stdLat (GlobalTheory.CompanionTheory.Ar.regAt ξ p)
        (GlobalTheory.CompanionTheory.Ar.Conj.transH (S.φ p) (S.ψ p) (S.lam p)) := by
    intro p y
    constructor
    · intro h
      obtain ⟨z, hz, hzy⟩ := Submodule.mem_map.mp h
      have : z = y := dd.injective hzy
      exact this ▸ hz
    · intro h
      exact Submodule.mem_map.mpr ⟨y, h, rfl⟩
  have hiso := fun p => GlobalTheory.T.formal_isomorphism_transport Ω d (𝓞 E) S.g₀.B (S.BK p) (S.φ p) (S.ψ p) (S.lam p) (S.iso p)
  have h_fst : ∀ (a : 𝓞 E) (y : (Fin d → Ω) × Module.Dual Ω (Fin d → Ω)),
      ((ρH a) y).1 = (ρ a) y.1 := by
    intro a y
    rw [hρH, hdd]
    dsimp only
    rw [hr1, ← hρeq]
    congr 1
  have h_inr : ∀ (a : 𝓞 E) (f : Module.Dual Ω (Fin d → Ω)),
      (ρH a) (0, f) = (0, f ∘ₗ ρ (H.bar a)) := by
    intro a f
    rw [hρH, hdd]
    have hz := hsymm (0, f)
    generalize dd.symm (0, f) = z at hz ⊢
    obtain ⟨hz1, hz2⟩ : z.1 = 0 ∧ dotProductBilin Ω Ω z.2 = f := Prod.ext_iff.mp hz
    subst hz2
    refine Prod.ext ?_ ?_
    · dsimp only
      rw [hr1, hz1, Matrix.mulVec_zero]
    · dsimp only
      rw [hr2, hz1, Matrix.mulVec_zero, sub_zero]
      refine LinearMap.ext fun u => ?_
      simp only [dotProductBilin_apply_apply, LinearMap.comp_apply, ← hρeq,
        Matrix.mulVec_transpose, hstar]
      exact (Matrix.dotProduct_mulVec _ _ _).symm
  have h_map : GlobalTheory.CompanionTheory.Ar.Lat.map HL
      (LinearMap.fst Ω (Fin d → Ω) (Module.Dual Ω (Fin d → Ω))) = M.lat := by
    funext p
    ext e
    rw [PositivityTheory.Xgn.GermHodgeLattice.lat_eq S p,
      ← PositivityTheory.Xgn.GermHodgeLattice.fst_stdLat (GlobalTheory.CompanionTheory.Ar.regAt ξ p) (S.φ p) (S.ψ p)
        (S.lam p) e]
    show e ∈ Submodule.map _ (HL p) ↔ _
    constructor
    · intro h
      obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp h
      obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.mp hy
      exact ⟨z, hz, by simp [hdd]⟩
    · rintro ⟨z, hz, rfl⟩
      exact Submodule.mem_map.mpr ⟨dd z, (hmem p z).mpr hz, by simp [hdd]⟩
  have h_comap : GlobalTheory.CompanionTheory.Ar.Lat.comap HL
      (LinearMap.inr Ω (Fin d → Ω) (Module.Dual Ω (Fin d → Ω))) = M.lat.dual := by
    funext p
    ext f
    obtain ⟨hl1, hl2, -⟩ := hiso p
    have hz := hsymm (0, f)
    generalize dd.symm (0, f) = z at hz
    obtain ⟨-, hz2⟩ : z.1 = 0 ∧ dotProductBilin Ω Ω z.2 = f := Prod.ext_iff.mp hz
    subst hz2
    show ((0 : Fin d → Ω), dotProductBilin Ω Ω z.2) ∈ HL p ↔
      ∀ e ∈ M.lat p, dotProductBilin Ω Ω z.2 e ∈ GlobalTheory.CompanionTheory.Ar.regAt ξ p
    rw [show ((0 : Fin d → Ω), dotProductBilin Ω Ω z.2) = dd (0, z.2) from (hdd (0, z.2)).symm,
      hmem, PositivityTheory.Xgn.GermHodgeLattice.inr_stdLat _ _ _ _ hl1 hl2,
      PositivityTheory.Xgn.GermHodgeLattice.lat_eq S p]
    simp only [dotProductBilin_apply_apply]
  refine ⟨GlobalTheory.CompanionTheory.Ar.Flat.HodgeLat.mk ρH HL h_fst h_inr h_map h_comap ?_ ?_, ?_⟩
  · intro p
    obtain ⟨x₀, hli, hsp⟩ := hfree p
    obtain ⟨hl1, hl2, hbij, -, hint, -⟩ := hiso p
    obtain ⟨s, hs, hst⟩ :=
      PositivityTheory.Xgn.GermHodgeLattice.exists_finite (GlobalTheory.CompanionTheory.Ar.genMap ξ p) _ hsp
    obtain ⟨U, hpU, hU⟩ := PositivityTheory.Xgn.GermHodgeLattice.exists_open p s hs
    obtain ⟨U', hpU', hU'⟩ := S.loc p
    have hspanT := PositivityTheory.Xgn.GermHodgeLattice.span_stdLat (GlobalTheory.CompanionTheory.Ar.regAt ξ p)
      (GlobalTheory.CompanionTheory.Ar.Conj.transH (S.φ p) (S.ψ p) (S.lam p)) hbij.2
    rw [hst (GlobalTheory.CompanionTheory.Ar.regAt ξ p) (fun r' _ => (GlobalTheory.CompanionTheory.Ar.genMap ξ p).mem_range_self r')
      (GlobalTheory.CompanionTheory.Ar.Conj.transH (S.φ p) (S.ψ p) (S.lam p)), Submodule.span_span_of_tower] at hspanT
    have hcard := PositivityTheory.Xgn.GermHodgeLattice.card_eq _ hli hsp
    have hfin : Module.finrank Ω ((Fin d → Ω) × (Fin d → Ω)) = d + d := by simp
    have hG_li := linearIndependent_of_top_le_span_of_card_eq_finrank hspanT.ge
      (hcard.trans hfin.symm)
    have hF_li := hG_li.map' dd.toLinearMap dd.ker
    have hF_span := congrArg (Submodule.map dd.toLinearMap) hspanT
    rw [Submodule.map_span, ← Set.range_comp, Submodule.map_top, LinearEquiv.range] at hF_span
    simp only [Function.comp_def, LinearEquiv.coe_coe] at hF_span hF_li
    have hfam : ∀ (b : 𝓞 E) (j : Fin r),
        ρH b (dd (GlobalTheory.CompanionTheory.Ar.Conj.transH (S.φ p) (S.ψ p) (S.lam p)
          (PositivityTheory.Xgn.GermHodgeLattice.mp (GlobalTheory.CompanionTheory.Ar.genMap ξ p) (x₀ j)))) =
        dd (GlobalTheory.CompanionTheory.Ar.Conj.transH (S.φ p) (S.ψ p) (S.lam p)
          (PositivityTheory.Xgn.GermHodgeLattice.mp (GlobalTheory.CompanionTheory.Ar.genMap ξ p)
            (GlobalTheory.CompanionTheory.Ar.Conj.rhoH (S.g p).B b (x₀ j)))) := by
      intro b j
      rw [hρH, LinearEquiv.symm_apply_apply]
      exact congrArg dd ((LinearMap.congr_fun (hint b) _).trans
        (congrArg (GlobalTheory.CompanionTheory.Ar.Conj.transH (S.φ p) (S.ψ p) (S.lam p))
          (PositivityTheory.Xgn.GermHodgeLattice.rhoH_mp _ (S.mapK p) b (x₀ j))))
    refine ⟨U ⊓ U', ⟨hpU, hpU'⟩, fun i => dd (GlobalTheory.CompanionTheory.Ar.Conj.transH (S.φ p) (S.ψ p) (S.lam p)
      (PositivityTheory.Xgn.GermHodgeLattice.mp (GlobalTheory.CompanionTheory.Ar.genMap ξ p) (x₀ i))), fun q hq => ?_⟩
    have hHL : HL q = Submodule.map (dd.toLinearMap.restrictScalars (GlobalTheory.CompanionTheory.Ar.regAt ξ q))
        (GlobalTheory.CompanionTheory.Ar.Flat.stdLat (GlobalTheory.CompanionTheory.Ar.regAt ξ q)
          (GlobalTheory.CompanionTheory.Ar.Conj.transH (S.φ p) (S.ψ p) (S.lam p))) := by
      show Submodule.map _ _ = _
      rw [hU' q hq.2]
    rw [hst (GlobalTheory.CompanionTheory.Ar.regAt ξ q) (hU q hq.1), Submodule.map_span, ← Set.range_comp] at hHL
    simp only [Function.comp_def, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe] at hHL
    unfold GlobalTheory.CompanionTheory.Ar.HT.IsFreeOn
    simp only [hfam]
    refine ⟨hF_li, ?_, hHL⟩
    rw [hHL, Submodule.span_span_of_tower]
    exact hF_span
  · intro p _
    obtain ⟨U', hpU', hU'⟩ := S.loc p
    obtain ⟨hl1, hl2, -⟩ := hiso p
    have hfr : Module.finrank Ω (Fin d → Ω) = d := Module.finrank_fin_fun Ω
    have hinjP : Function.Injective (Matrix.toLin' (GlobalTheory.CompanionTheory.Ar.Conj.lin (S.φ p) 1)) := by
      intro u v huv
      have h := congrArg (Matrix.toLin' (GlobalTheory.CompanionTheory.Ar.Conj.lin (S.ψ p) 1)) huv
      simpa [Matrix.toLin'_apply, Matrix.mulVec_mulVec, hl2] using h
    have hsurjP : Function.Surjective (Matrix.toLin' (GlobalTheory.CompanionTheory.Ar.Conj.lin (S.φ p) 1)) := by
      intro v
      refine ⟨(GlobalTheory.CompanionTheory.Ar.Conj.lin (S.ψ p) 1).mulVec v, ?_⟩
      simp [Matrix.toLin'_apply, Matrix.mulVec_mulVec, hl1]
    have hcg : (fun l : Fin d => (GlobalTheory.CompanionTheory.Ar.Conj.lin (S.φ p) 1).mulVec (Pi.single l 1)) =
        (Matrix.toLin' (GlobalTheory.CompanionTheory.Ar.Conj.lin (S.φ p) 1)) ∘ (Pi.basisFun Ω (Fin d)) := by
      funext l; simp [Matrix.toLin'_apply]
    have hc_li : LinearIndependent Ω
        (fun l : Fin d => (GlobalTheory.CompanionTheory.Ar.Conj.lin (S.φ p) 1).mulVec (Pi.single l 1)) := by
      rw [hcg]
      exact (Pi.basisFun Ω (Fin d)).linearIndependent.map' _ (LinearMap.ker_eq_bot.mpr hinjP)
    have hc_span : Submodule.span Ω (Set.range
        (fun l : Fin d => (GlobalTheory.CompanionTheory.Ar.Conj.lin (S.φ p) 1).mulVec (Pi.single l 1))) = ⊤ := by
      rw [hcg, Set.range_comp, ← Submodule.map_span, (Pi.basisFun Ω (Fin d)).span_eq,
        Submodule.map_top, LinearMap.range_eq_top.mpr hsurjP]
    refine ⟨U', hpU',
      (fun l : Fin d => (GlobalTheory.CompanionTheory.Ar.Conj.lin (S.φ p) 1).mulVec (Pi.single l 1)) ∘ (finCongr hfr),
      ?_, ?_⟩
    · rw [(finCongr hfr).surjective.range_comp]; exact hc_span
    · intro q _ hq
      unfold GlobalTheory.CompanionTheory.Ar.Lat.IsFrameAt
      refine ⟨hc_li.comp _ (finCongr hfr).injective, ?_⟩
      rw [(finCongr hfr).surjective.range_comp]
      ext e
      rw [PositivityTheory.Xgn.GermHodgeLattice.lat_eq S q,
        ← PositivityTheory.Xgn.GermHodgeLattice.fst_stdLat (GlobalTheory.CompanionTheory.Ar.regAt ξ q) (S.φ q) (S.ψ q)
          (S.lam q) e,
        ← hU' q hq, PositivityTheory.Xgn.GermHodgeLattice.fst_stdLat]
  · unfold GlobalTheory.CompanionTheory.Ar.Flat.GermSys.Gives
    refine ⟨fun a y => ?_, fun p y => ?_⟩
    · show ρH a (y.1, dotProductBilin Ω Ω y.2) = _
      rw [show (y.1, dotProductBilin Ω Ω y.2) = dd y from (hdd y).symm, hρH,
        LinearEquiv.symm_apply_apply, hdd]
    · show (y.1, dotProductBilin Ω Ω y.2) ∈ HL p ↔ _
      rw [← hdd]
      exact hmem p y

end GlobalTheory.CompanionTheory.Ar.Flat
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_hodge_lattice_germ_system : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X : Scheme.{0}) (t : SAB H X) (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Sp Ω ⟶ X) (d r : ℕ) (M : LieModel t.G ξ (Fin d → Ω)) (S : GermSys t ξ M) (ρ : 𝓞 E →+* Module.End Ω (Fin d → Ω)), IsCptGen ξ → M.IsActOf t.act.act ρ → (∀ q : Cpt ξ, HFree (S.g q).B r) → ∃ 𝓗 : HodgeLat M.lat ρ H.bar r, S.Gives 𝓗 := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Flat.germ_gives_hodgeLat
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem germSys_exists : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X : Scheme.{0}) (t : SAB H X) (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Sp Ω ⟶ X) [IsLocallyNoetherian X], PowFns t → IsCptGen ξ → ∃ (d : ℕ) (M : LieModel t.G ξ (Fin d → Ω)), Nonempty (GermSys t ξ M) :=
  @PositivityTheory.Xgn.germ_system_exists

end GlobalTheory.CompanionTheory.Ar.Flat
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_germ_system : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X : Scheme.{0}) (t : SAB H X) (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Sp Ω ⟶ X) [IsLocallyNoetherian X], PowFns t → IsCptGen ξ → ∃ (d : ℕ) (M : LieModel t.G ξ (Fin d → Ω)), Nonempty (GermSys t ξ M) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Flat.germSys_exists
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem hfree_at_component_stalks : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X : Scheme.{0}) (t : SAB H X) (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Sp Ω ⟶ X) (d r : ℕ) (M : LieModel t.G ξ (Fin d → Ω)) (S : GermSys t ξ M), PowFns t → IsCptGen ξ → HChar S.g₀.B r → (∀ (q : Cpt ξ) (p : ℕ), p.Prime → (p : X.residueField q.1) = 0 → FibPF t q.1) → ∀ q : Cpt ξ, HFree (S.g q).B r :=
  PositivityTheory.Xgn.hodge_free_every_stalk

end GlobalTheory.CompanionTheory.Ar.Flat
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.germ_system_height_free : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X : Scheme.{0}) (t : SAB H X) (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Sp Ω ⟶ X) (d r : ℕ) (M : LieModel t.G ξ (Fin d → Ω)) (S : GermSys t ξ M), PowFns t → IsCptGen ξ → HChar S.g₀.B r → (∀ (q : Cpt ξ) (p : ℕ), p.Prime → (p : X.residueField q.1) = 0 → FibPF t q.1) → ∀ q : Cpt ξ, HFree (S.g q).B r := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Flat.hfree_at_component_stalks
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Flat

namespace HodgeTransport

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {V V' : Type} [AddCommGroup V] [Module Ω V]
  [AddCommGroup V'] [Module Ω V'] {F F' : Type} [AddCommGroup F] [Module Ω F] [AddCommGroup F'] [Module Ω F']
  {E : Type} [Field E] [NumberField E]

def conjE (e : V ≃ₗ[Ω] V') : (V × Module.Dual Ω V) ≃ₗ[Ω] (V' × Module.Dual Ω V') :=
  e.prodCongr e.symm.dualMap

theorem conjE_apply (e : V ≃ₗ[Ω] V') (y : V × Module.Dual Ω V) :
    conjE e y = (e y.1, y.2 ∘ₗ e.symm.toLinearMap) := rfl

theorem conjE_symm_apply (e : V ≃ₗ[Ω] V') (y : V' × Module.Dual Ω V') :
    (conjE e).symm y = (e.symm y.1, y.2 ∘ₗ e.toLinearMap) := rfl

def cj (g : F ≃ₗ[Ω] F') (ρ : 𝓞 E →+* Module.End Ω F) : 𝓞 E →+* Module.End Ω F' :=
  (g.conjRingEquiv : Module.End Ω F →+* Module.End Ω F').comp ρ

theorem cj_apply (g : F ≃ₗ[Ω] F') (ρ : 𝓞 E →+* Module.End Ω F) (a : 𝓞 E) (y : F') :
    cj g ρ a y = g (ρ a (g.symm y)) := rfl

theorem mem_map_equiv (M : Lat ξ F) (g : F ≃ₗ[Ω] F') (p : Cpt ξ) (y : F') :
    y ∈ M.map g.toLinearMap p ↔ g.symm y ∈ M p := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa using hx
  · intro h
    exact ⟨_, h, by simp⟩

theorem map_symm_map (M : Lat ξ F) (g : F ≃ₗ[Ω] F') :
    (M.map g.toLinearMap).map g.symm.toLinearMap = M := by
  funext p
  ext y
  rw [mem_map_equiv, mem_map_equiv]
  simp

theorem isFrameAt_map {M : Lat ξ F} (g : F ≃ₗ[Ω] F') {r : ℕ} {b : Fin r → F} {p : Cpt ξ}
    (h : M.IsFrameAt b p) : (M.map g.toLinearMap).IsFrameAt (g ∘ b) p := by
  refine ⟨(LinearMap.linearIndependent_iff g.toLinearMap (LinearEquiv.ker g)).2 h.1, ?_⟩
  change Submodule.map _ (M p) = _
  rw [h.2, Submodule.map_span, Set.range_comp]
  rfl

theorem isFrameAt_map_iff {M : Lat ξ F} (g : F ≃ₗ[Ω] F') {r : ℕ} {b : Fin r → F'} {p : Cpt ξ} :
    (M.map g.toLinearMap).IsFrameAt b p ↔ M.IsFrameAt (g.symm ∘ b) p := by
  constructor
  · intro h
    have := isFrameAt_map g.symm h
    rwa [map_symm_map] at this
  · intro h
    have := isFrameAt_map g h
    have e : g ∘ g.symm ∘ b = b := by funext i; simp
    rwa [e] at this

theorem detLat_map (M : Lat ξ F) (g : F ≃ₗ[Ω] F') {r : ℕ} (u : Fin r → F') :
    detLat (M.map g.toLinearMap) u = detLat M (g.symm ∘ u) := by
  funext p
  simp only [detLat]
  congr 1
  ext t
  refine exists_congr fun A => and_congr_left fun _ => ?_
  rw [isFrameAt_map_iff]
  have e : (g.symm ∘ fun i => ∑ j, A i j • u j) = fun i => ∑ j, A i j • (g.symm ∘ u) j := by
    funext i
    simp
  rw [e]

theorem isFreeOn_map {M : Lat ξ F} (g : F ≃ₗ[Ω] F') {ρ : 𝓞 E →+* Module.End Ω F} {p : Cpt ξ} {N : ℕ}
    {t : Fin N → F} (h : HT.IsFreeOn ρ (M p) t) :
    HT.IsFreeOn (cj g ρ) (M.map g.toLinearMap p) (g ∘ t) := by
  have e : (fun q : Fin N × Module.Free.ChooseBasisIndex ℤ (𝓞 E) =>
      cj g ρ (RingOfIntegers.basis E q.2) ((g ∘ t) q.1)) =
      g ∘ fun q : Fin N × Module.Free.ChooseBasisIndex ℤ (𝓞 E) =>
        ρ (RingOfIntegers.basis E q.2) (t q.1) := by
    funext q
    simp [cj_apply]
  refine ⟨?_, ?_, ?_⟩
  · rw [e]
    exact (LinearMap.linearIndependent_iff g.toLinearMap (LinearEquiv.ker g)).2 h.1
  · have e2 : ((M.map g.toLinearMap p : Submodule _ F') : Set F') = g '' (M p : Set F) := rfl
    rw [e2]
    have := Submodule.map_span g.toLinearMap (M p : Set F)
    rw [h.2.1, Submodule.map_top, LinearEquiv.range] at this
    exact this.symm
  · rw [e]
    change Submodule.map _ (M p) = _
    rw [h.2.2, Submodule.map_span, Set.range_comp]
    rfl

theorem eigProj_cj (g : F ≃ₗ[Ω] F') (ρ : 𝓞 E →+* Module.End Ω F) (σ : E →+* Ω) (y : F') :
    HT.eigProj (cj g ρ) σ y = g (HT.eigProj ρ σ (g.symm y)) := by
  simp [HT.eigProj, LinearMap.sum_apply, cj_apply, map_sum]

theorem mem_eigSp_cj (g : F ≃ₗ[Ω] F') (ρ : 𝓞 E →+* Module.End Ω F) (σ : E →+* Ω) (y : F') :
    y ∈ HT.eigSp (cj g ρ) σ ↔ g.symm y ∈ HT.eigSp ρ σ := by
  rw [HT.LatBasic.mem_eigSp, HT.LatBasic.mem_eigSp]
  refine forall_congr' fun a => ?_
  rw [cj_apply, ← map_smul, LinearEquiv.eq_symm_apply]

theorem eigQuot_map (M : Lat ξ F) (g : F ≃ₗ[Ω] F') (ρ : 𝓞 E →+* Module.End Ω F) (σ : E →+* Ω) :
    (M.map g.toLinearMap).map (HT.eigProj (cj g ρ) σ) = (M.map (HT.eigProj ρ σ)).map g.toLinearMap := by
  funext p
  ext y
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨_, ⟨x, hx, rfl⟩, by simp [eigProj_cj]⟩
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨_, ⟨x, hx, rfl⟩, by simp [eigProj_cj]⟩

variable {L : Lat ξ V} {ρ : 𝓞 E →+* Module.End Ω V} {ρ' : 𝓞 E →+* Module.End Ω V'} {bar : 𝓞 E ≃+* 𝓞 E} {r : ℕ}

def transport (e : V ≃ₗ[Ω] V') (𝓗 : HodgeLat L ρ bar r) (h : ∀ a v, e (ρ a v) = ρ' a (e v)) :
    HodgeLat (L.map e.toLinearMap) ρ' bar r where
  ρH := cj (conjE e) 𝓗.ρH
  HL := 𝓗.HL.map (conjE e).toLinearMap
  act_fst a y := by
    rw [cj_apply, conjE_apply, 𝓗.act_fst, h, conjE_symm_apply]
    simp
  act_inr a φ := by
    rw [cj_apply, conjE_symm_apply]
    simp only [map_zero]
    rw [𝓗.act_inr, conjE_apply]
    refine Prod.ext (by simp) (LinearMap.ext fun x => ?_)
    simp [h]
  map_fst := by
    funext p
    conv_rhs => rw [← 𝓗.map_fst]
    ext y
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨_, ⟨x, hx, rfl⟩, rfl⟩
  comap_inr := by
    funext p
    ext φ
    have h1 : (φ ∈ (𝓗.HL.map (conjE e).toLinearMap).comap (LinearMap.inr Ω V' (Module.Dual Ω V')) p) ↔
        ((0, φ ∘ₗ e.toLinearMap) : V × Module.Dual Ω V) ∈ 𝓗.HL p := by
      change ((0, φ) : V' × Module.Dual Ω V') ∈ 𝓗.HL.map (conjE e).toLinearMap p ↔ _
      rw [mem_map_equiv, conjE_symm_apply]
      simp
    have h2 : ((0, φ ∘ₗ e.toLinearMap) : V × Module.Dual Ω V) ∈ 𝓗.HL p ↔
        φ ∘ₗ e.toLinearMap ∈ L.dual p := by
      rw [← 𝓗.comap_inr]
      rfl
    rw [h1, h2]
    change (∀ x ∈ L p, φ (e x) ∈ regAt ξ p) ↔ ∀ x ∈ L.map e.toLinearMap p, φ x ∈ regAt ξ p
    constructor
    · rintro hφ _ ⟨z, hz, rfl⟩
      exact hφ z hz
    · intro hφ z hz
      exact hφ _ ⟨z, hz, rfl⟩
  free p := by
    obtain ⟨U, hU, x, hx⟩ := 𝓗.free p
    exact ⟨U, hU, conjE e ∘ x, fun q hq => isFreeOn_map (conjE e) (hx q hq)⟩
  vb := by
    rw [← e.finrank_eq]
    intro p hp
    obtain ⟨U, hU, b, hb, hf⟩ := 𝓗.vb p hp
    refine ⟨U, hU, e ∘ b, ?_, fun q hq hqU => isFrameAt_map e (hf q hq hqU)⟩
    rw [Set.range_comp]
    have := Submodule.map_span e.toLinearMap (Set.range b)
    rw [hb, Submodule.map_top, LinearEquiv.range] at this
    exact this.symm

theorem transport_degZero (e : V ≃ₗ[Ω] V') (𝓗 : HodgeLat L ρ bar r) (h : ∀ a v, e (ρ a v) = ρ' a (e v))
    (σ : E →+* Ω) (ϖ : Ω) (hd : 𝓗.DegZero σ ϖ) : (transport e 𝓗 h).DegZero σ ϖ := by
  intro u hu hsp
  have hq : (transport e 𝓗 h).quot σ = (𝓗.quot σ).map (conjE e).toLinearMap :=
    eigQuot_map 𝓗.HL (conjE e) 𝓗.ρH σ
  rw [hq, detLat_map]
  refine hd _ ((LinearMap.linearIndependent_iff (conjE e).symm.toLinearMap (LinearEquiv.ker _)).2 hu) ?_
  ext y
  have h1 : Set.range ((conjE e).symm ∘ u) = (conjE e).symm.toLinearMap '' Set.range u := Set.range_comp _ _
  rw [h1, ← Submodule.map_span, hsp]
  change _ ↔ y ∈ HT.eigSp 𝓗.ρH σ
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact (mem_eigSp_cj (conjE e) 𝓗.ρH σ z).1 hz
  · intro hy
    refine ⟨conjE e y, (mem_eigSp_cj (conjE e) 𝓗.ρH σ _).2 (by simpa using hy), by simp⟩

end HodgeTransport

theorem hodgeLat_transport : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (E : Type) [Field E] [NumberField E] (V V' : Type) [AddCommGroup V] [Module Ω V] [AddCommGroup V'] [Module Ω V'] (e : V ≃ₗ[Ω] V') (L : Lat ξ V) (ρ : 𝓞 E →+* Module.End Ω V) (ρ' : 𝓞 E →+* Module.End Ω V') (bar : 𝓞 E ≃+* 𝓞 E) (r : ℕ) (𝓗 : HodgeLat L ρ bar r), (∀ a v, e (ρ a v) = ρ' a (e v)) → ∃ 𝓗' : HodgeLat (L.map e.toLinearMap) ρ' bar r, ∀ σ ϖ, 𝓗.DegZero σ ϖ → 𝓗'.DegZero σ ϖ := by
  intro X Ω _ ξ E _ _ V V' _ _ _ _ e L ρ ρ' bar r 𝓗 h
  exact ⟨HodgeTransport.transport e 𝓗 h, fun σ ϖ hd => HodgeTransport.transport_degZero e 𝓗 h σ ϖ hd⟩

end GlobalTheory.CompanionTheory.Ar.Flat
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_lattice_transport_equiv : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (E : Type) [Field E] [NumberField E] (V V' : Type) [AddCommGroup V] [Module Ω V] [AddCommGroup V'] [Module Ω V'] (e : V ≃ₗ[Ω] V') (L : Lat ξ V) (ρ : 𝓞 E →+* Module.End Ω V) (ρ' : 𝓞 E →+* Module.End Ω V') (bar : 𝓞 E ≃+* 𝓞 E) (r : ℕ) (𝓗 : HodgeLat L ρ bar r), (∀ a v, e (ρ a v) = ρ' a (e v)) → ∃ 𝓗' : HodgeLat (L.map e.toLinearMap) ρ' bar r, ∀ σ ϖ, 𝓗.DegZero σ ϖ → 𝓗'.DegZero σ ϖ := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Flat.hodgeLat_transport
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.CptHodge

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem emb_factor {l : Level H} (c : Coeff l) {Ω : Type} [Field Ω] (inc : c.F →+* Ω) :
    Nat.card (E →+* Ω) = Module.finrank ℚ E ∧
      ∀ s : E →+* Ω, ∃ τ : E →+* ℂ, ∀ a : 𝓞 E, s (a : E) = inc (tauIn c τ a) := by
  haveI : CharZero Ω := charZero_of_injective_ringHom inc.injective
  let g : (E →+* ℂ) → (E →+* c.F) := fun τ => τ.codRestrict c.F.toSubfield (c.conj τ)
  let f₁ : (E →+* ℂ) → (E →+* Ω) := fun τ => inc.comp (g τ)
  let f₂ : (E →+* Ω) → (E →+* AlgebraicClosure Ω) := fun s => (algebraMap Ω (AlgebraicClosure Ω)).comp s
  have h₁ : Function.Injective f₁ := fun τ τ' h => by
    ext x
    have := DFunLike.congr_fun h x
    exact congrArg (fun y : c.F => (y : ℂ)) (inc.injective this)
  have h₂ : Function.Injective f₂ := fun s s' h => by
    ext x
    exact (algebraMap Ω (AlgebraicClosure Ω)).injective (DFunLike.congr_fun h x)
  have hb : Function.Bijective (f₂ ∘ f₁) := (Fintype.bijective_iff_injective_and_card _).2
    ⟨h₂.comp h₁, by rw [NumberField.Embeddings.card, NumberField.Embeddings.card]⟩
  have hs : Function.Surjective f₁ := Function.Surjective.of_comp_left hb.2 h₂
  refine ⟨?_, fun s => ?_⟩
  · rw [Nat.card_eq_fintype_card, ← Fintype.card_of_bijective ⟨h₁, hs⟩, NumberField.Embeddings.card]
  · obtain ⟨τ, rfl⟩ := hs s
    exact ⟨τ, fun a => rfl⟩

theorem tauIn_conj {l : Level H} (c : Coeff l) (τ : E →+* ℂ) (a : 𝓞 E) :
    tauIn c (ComplexEmbedding.conjugate τ) a = tauIn c τ (H.bar a) := by
  apply Subtype.ext
  change (ComplexEmbedding.conjugate τ) (a : E) = τ ((H.bar a : 𝓞 E) : E)
  rw [H.bar_eq, ComplexEmbedding.conjugate_coe_eq, IsCMField.complexEmbedding_complexConj]

theorem rt_cases (τ : E →+* ℂ) : τ (H.rt : E) = H.rt0 ∨ (ComplexEmbedding.conjugate τ) (H.rt : E) = H.rt0 := by
  have h1 : (τ (H.rt : E)) ^ 2 = H.rt0 ^ 2 := by
    rw [H.sqrt_neg_disc_sq, ← map_pow]
    have : ((H.rt : E)) ^ 2 = -(H.d : E) := by
      have := congrArg (algebraMap (𝓞 E) E) H.rt_sq
      simpa using this
    rw [this]
    simp
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have hc : (starRingEnd ℂ) H.rt0 = -H.rt0 := by
    have h2 := H.sqrt_neg_disc_sq
    apply Complex.ext
    · have hre : H.rt0.re = 0 := by
        by_contra hx
        have e1 := congrArg Complex.re h2
        have e2 := congrArg Complex.im h2
        simp [pow_two] at e1 e2
        have hi : H.rt0.im = 0 := by
          have : 2 * H.rt0.re * H.rt0.im = 0 := by linarith
          rcases mul_eq_zero.1 this with h | h
          · exact absurd (by linarith) hx
          · exact h
        rw [hi] at e1
        nlinarith [mul_self_nonneg H.rt0.re]
      simp [hre]
    · simp
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h | h
  · exact Or.inl h
  · right
    rw [ComplexEmbedding.conjugate_coe_eq, h, map_neg, hc, neg_neg]

section Transport

variable {Ω : Type} [Field Ω] {W V : Type} [AddCommGroup W] [Module Ω W] [AddCommGroup V] [Module Ω V]

theorem finrank_eig (e : W ≃ₗ[Ω] V) (ρ' : 𝓞 E →+* Module.End Ω W) (ρ : 𝓞 E →+* Module.End Ω V)
    (h : ∀ a v, e (ρ' a v) = ρ a (e v)) (s : E →+* Ω) (χ : 𝓞 E →+* Ω) (hχ : ∀ a : 𝓞 E, χ a = s (a : E)) :
    Module.finrank Ω (HT.eigSp ρ' s) = Module.finrank Ω (eigSp ρ χ) := by
  have hm : eigSp ρ χ = (HT.eigSp ρ' s).map (e : W →ₗ[Ω] V) := by
    ext y
    simp only [eigSp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.id_apply, sub_eq_zero, Submodule.mem_map, HT.LatBasic.mem_eigSp]
    constructor
    · intro hy
      refine ⟨e.symm y, fun a => e.injective ?_, by simp⟩
      rw [h, map_smul, e.apply_symm_apply, hy, hχ]
    · rintro ⟨x, hx, rfl⟩ a
      change ρ a (e x) = χ a • e x
      rw [← h, hx, map_smul, hχ]
  rw [hm]
  exact (LinearEquiv.finrank_eq (e.submoduleMap _))

end Transport

section LatMap

variable {X : Scheme.{0}} {G : Over X} [GrpObj G] {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {W V : Type} [AddCommGroup W] [Module Ω W] [AddCommGroup V] [Module Ω V]

theorem lat_map (M : LieModel G ξ W) (M' : LieModel G ξ V) (e : W ≃ₗ[Ω] V) (h : ∀ w, M'.pt (e w) = M.pt w) :
    M.lat.map e.toLinearMap = M'.lat := by
  funext p
  change Submodule.map _ (Submodule.span _ _) = Submodule.span _ _
  rw [Submodule.map_span]
  congr 1
  ext y
  constructor
  · rintro ⟨x, ⟨v, hv⟩, rfl⟩
    refine ⟨v, hv.1, ?_⟩
    change (M'.pt (e x)).left = _
    rw [h]
    exact hv.2
  · rintro ⟨v, hv⟩
    refine ⟨e.symm y, ⟨v, hv.1, ?_⟩, by simp⟩
    rw [← h, e.apply_symm_apply]
    exact hv.2

end LatMap

section Model

variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O]
  [IsDedekindDomain O] [Algebra O c.F] [IsFractionRing O c.F]

theorem generic_mem_abLocus (Y : Model Xo c (algebraMap O c.F)) (z : Y.X) (hz : ∀ z' : Y.X, z' ⤳ z → z' = z) :
    z ∈ abLocus Y.t.G := by
  have h0 : IsDomain (Y.X.presheaf.stalk z) := (Y.normal z).1
  have hfl : (Scheme.stalkClosedPointTo (Y.X.fromSpecStalk z)).hom.Flat := by
    rw [Scheme.stalkClosedPointTo_fromSpecStalk]
    exact RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso _)
  obtain ⟨y, hy⟩ := @GlobalTheory.TorRef.DomFine.exists_generic_point O c.F _ _ _ _ _ Y.X (Xo.XF c) Y.s Y.jQ Y.flat Y.proj
    Y.jQ_open Y.jQ_dense (Y.X.presheaf.stalk z) _ h0 _ (Y.X.fromSpecStalk z) hfl
  obtain ⟨pt⟩ : Nonempty (Sp (FractionRing (Y.X.presheaf.stalk z))) := inferInstance
  have h1 : (y ≫ Y.jQ ≫ pullback.fst _ _) pt ⤳ z := by
    have : (y ≫ Y.jQ ≫ pullback.fst _ _) pt ∈ Set.range (Y.X.fromSpecStalk z) := by
      rw [hy]
      exact ⟨_, by rw [Scheme.Hom.comp_apply]⟩
    rw [Scheme.range_fromSpecStalk] at this
    exact this
  have h2 := hz _ h1
  have h3 : Y.jQ (y pt) ∈ pullback.fst Y.s (spMap (algebraMap O c.F)) ⁻¹' abLocus Y.t.G := by
    rw [Y.ab_gen]
    exact ⟨_, rfl⟩
  rw [← h2]
  simpa [Scheme.Hom.comp_apply] using h3

end Model

end GlobalTheory.CompanionTheory.Ar.Flat.CptHodge

namespace GlobalTheory.CompanionTheory.Ar.Flat

open CptHodge in

theorem hodgeLat_model : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (τ : E →+* ℂ) (ϖ : O) (p : ℕ), Irreducible ϖ → p.Prime → ϖ ∣ (p : O) → Function.Injective β → (∀ x : c.F, x ∈ β.range ∨ x⁻¹ ∈ β.range) → Y.SplitFibres → Y.N3 → ∃ 𝓗 : HodgeLat Z.M.lat Z.ρ H.bar (D.p + D.q), ∀ σ : E →+* Z.Ω, 𝓗.DegZero σ (Z.inc (β ϖ)) := by
  intro E _ _ _ H D l Xo c O _ _ _ β Y U Z τ ϖ p hϖ hp hdvd hβ hval hsplit hN3
  letI : StarRing (𝓞 E) := H.starRing
  have hstar : ∀ a : 𝓞 E, star a = H.bar a := fun _ => rfl
  have hfrac : ∀ x : c.F, ∃ a b : O, b ≠ 0 ∧ x * β b = β a := by
    intro x
    rcases hval x with ⟨a, rfl⟩ | ⟨b, hb⟩
    · exact ⟨a, 1, one_ne_zero, by simp⟩
    · by_cases hx : x = 0
      · exact ⟨0, 1, one_ne_zero, by simp [hx]⟩
      · refine ⟨1, b, ?_, ?_⟩
        · rintro rfl
          rw [map_zero] at hb
          exact inv_ne_zero hx hb.symm
        · rw [hb, mul_inv_cancel₀ hx, map_one]
  letI algF : Algebra O c.F := β.toAlgebra
  haveI : FaithfulSMul O c.F := (faithfulSMul_iff_algebraMap_injective O c.F).2 hβ
  haveI : IsFractionRing O c.F := IsFractionRing.of_field O c.F fun z => by
    obtain ⟨a, b, hb, h⟩ := hfrac z
    refine ⟨a, b, ?_⟩
    have hb' : β b ≠ 0 := fun h0 => hb (hβ (by rw [h0, map_zero]))
    change z = β a / β b
    rw [← h, mul_div_cancel_right₀ _ hb']
  obtain ⟨hLN, -, -, -, -, hdom, -⟩ := GlobalTheory.genericPart_dense_proOpen O c.F Y.X (Xo.XF c) Y.s Y.jQ Y.flat Y.proj
    Y.jQ_open Y.jQ_dense
  have hdense : Dense (Set.range Y.j) := hdom.denseRange
  have hFib := GlobalTheory.T.model_fibres_power_free E H D l Xo c O β Y hdense hsplit hN3
  haveI : ∀ x : Y.X, _root_.IsReduced (Y.X.presheaf.stalk x) := fun x => by
    have := (Y.normal x).1
    infer_instance
  have hred : AlgebraicGeometry.IsReduced Y.X := isReduced_of_isReduced_stalk Y.X
  have hPow : PowFns Y.t := GlobalTheory.T.powFns_of_abelian_generic E H Y.X Y.t hred hLN (fun z hz => generic_mem_abLocus (O := O) Y z hz)
  haveI : CharZero Z.Ω := charZero_of_injective_ringHom Z.inc.injective
  obtain ⟨hcard, hfac⟩ := emb_factor (E := E) c Z.inc
  have facts := fun τ' h => GlobalTheory.T.proper_normal_compactification E H D l Xo c O β Y U Z τ' hβ hfrac h
  have hτ₀ : ∃ τ₀ : E →+* ℂ, τ₀ (H.rt : E) = H.rt0 := (rt_cases τ).elim (fun h => ⟨τ, h⟩) fun h => ⟨_, h⟩
  obtain ⟨τ₀, hτ₀⟩ := hτ₀
  obtain ⟨hprop, -, hover, -, hfd, -, -⟩ := facts τ₀ hτ₀
  haveI : IsProper Y.s := hprop
  obtain ⟨d, M, ⟨S⟩⟩ := GlobalTheory.T.exists_germ_system E H hstar Y.X Y.t Z.Ω (Z.ξ₀ ≫ Y.j) hPow Z.gen
  obtain ⟨e, he, -⟩ := GlobalTheory.T.lie_model_existsUnique_equiv Y.X Y.t.G Z.Ω (Z.ξ₀ ≫ Y.j) (Fin d → Z.Ω) Z.V M Z.M
  let ρ' : 𝓞 E →+* Module.End Z.Ω (Fin d → Z.Ω) := (e.symm.conjRingEquiv : _ ≃+* _).toRingHom.comp Z.ρ
  have hρ' : ∀ a v, e (ρ' a v) = Z.ρ a (e v) := fun a v => by
    simp [ρ', LinearEquiv.conjRingEquiv, LinearEquiv.conj_apply]
  have hact : M.IsActOf Y.t.act.act ρ' := fun a v => by
    rw [← he, hρ', Z.act a (e v), he]
  have hrho : ∀ a v, ρ' a v = (rho S.g₀.B a).mulVec v := fun a v => M.inj (by rw [S.act₀, hact a v])
  have hsum : ∀ s s' : E →+* Z.Ω, (∀ a : 𝓞 E, s' (a : E) = s ((star a : 𝓞 E) : E)) →
      Module.finrank Z.Ω (HT.eigSp ρ' s) + Module.finrank Z.Ω (HT.eigSp ρ' s') = D.p + D.q := by
    intro s s' hss
    obtain ⟨τ', hτ'⟩ := hfac s
    have h1 := finrank_eig e ρ' Z.ρ hρ' s (Z.inc.comp (tauIn c τ')) fun a => (hτ' a).symm
    have h2 := finrank_eig e ρ' Z.ρ hρ' s' (Z.inc.comp (tauIn c (ComplexEmbedding.conjugate τ'))) fun a => by
      rw [hss, hτ', hstar, RingHom.comp_apply, tauIn_conj]
    rw [h1, h2]
    rcases rt_cases (H := H) τ' with h | h
    · obtain ⟨-, -, -, -, -, e1, e2⟩ := facts τ' h
      rw [e1, e2]
    · obtain ⟨-, -, -, -, -, e1, e2⟩ := facts _ h
      have hcc : ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ') = τ' := by
        ext x
        simp [ComplexEmbedding.conjugate_coe_eq]
      rw [hcc] at e2
      rw [e1, e2, add_comm]
  have hC : HChar S.g₀.B (D.p + D.q) := GlobalTheory.T.hermitian_signature_character E Z.Ω d (D.p + D.q) S.g₀.B ρ' hrho hcard hsum
  have hfree := GlobalTheory.T.germ_system_height_free E H hstar Y.X Y.t Z.Ω (Z.ξ₀ ≫ Y.j) d (D.p + D.q) M S hPow Z.gen hC
    (fun q p' hp' h => hFib p' hp' q.1 h)
  obtain ⟨𝓗, hG⟩ := GlobalTheory.T.exists_hodge_lattice_germ_system E H hstar Y.X Y.t Z.Ω (Z.ξ₀ ≫ Y.j) d (D.p + D.q) M S ρ' Z.gen hact hfree
  letI algΩ : Algebra O Z.Ω := (Z.inc.comp β).toAlgebra
  have hint : ∀ (s' : E →+* Z.Ω) (a : 𝓞 E), s' (a : E) ∈ (algebraMap O Z.Ω).range := by
    intro s' a
    obtain ⟨τ', hτ'⟩ := hfac s'
    have h1 : IsIntegral ℤ (tauIn c τ' a) :=
      (RingOfIntegers.isIntegral a).map (tauIn c τ').toIntAlgHom
    have h2 : IsIntegral O (tauIn c τ' a) := h1.tower_top
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h2
    refine ⟨y, ?_⟩
    rw [hτ', ← hy]
    rfl
  have hdeg : ∀ σ : E →+* Z.Ω, 𝓗.DegZero σ (Z.inc (β ϖ)) := fun σ =>
    GlobalTheory.T.hodge_lattice_dvr_degree E H hstar Y.X Y.t Z.Ω (Z.ξ₀ ≫ Y.j) d (D.p + D.q) M S ρ' 𝓗 O Y.s ϖ p σ hϖ hp hdvd hover Z.gen
      hPow hG (fun q h => hFib p hp q.1 h) hcard hint
  have htr := GlobalTheory.T.hodge_lattice_transport_equiv Y.X Z.Ω (Z.ξ₀ ≫ Y.j) E (Fin d → Z.Ω) Z.V e M.lat ρ' Z.ρ H.bar (D.p + D.q) 𝓗 hρ'
  rw [lat_map M Z.M e he] at htr
  obtain ⟨𝓗', h'⟩ := htr
  exact ⟨𝓗', fun σ => h' σ _ (hdeg σ)⟩

end GlobalTheory.CompanionTheory.Ar.Flat
end
end
