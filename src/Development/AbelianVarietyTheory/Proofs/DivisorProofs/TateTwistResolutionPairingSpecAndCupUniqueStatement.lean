import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupProductNaturalInSheafComplexPairingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsTensorEtaleSheafComplexPairingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTateTwistResolutionTensorFlatStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendChainMapAlongQuasiIsoKInjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatSectionsOfInjectiveZmodEtaleSheafStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChosenInjectiveResolutionEtaleSheafProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistSectionsLocallyGeneratedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HypercohomologyPullbackPushforwardFunctorialStatement

section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.TwResExt

theorem sec_map_comp {R : Type} [CommRing R] {F G K : Shv R} (f : F ⟶ G) (g : G ⟶ K) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (f ≫ g) x = Sec.map g (Sec.map f x) := rfl

theorem twRes_ext : ∀ (q : ℕ) [NeZero q] (i : ℤ), IsTwRes q i (res _ (tw q i)) (fun _ ζ => resGen i ζ) ∧
    (∀ t, FlatS ((res _ (tw q i)).X t)) ∧ ∀ {T : Cx (ZMod q)} (e : ∀ U : Scheme.{0}, Prim q Γ(U, ⊤) → Sec (T.X 0) U),
    IsTwRes q i T e → (∃ u : T ⟶ res _ (tw q i), ∀ U ζ, Sec.map (u.f 0) (e U ζ) = resGen i ζ) ∧
    ∀ u u' : T ⟶ res _ (tw q i), (∀ U ζ, Sec.map (u.f 0) (e U ζ) = Sec.map (u'.f 0) (e U ζ)) → Nonempty (Homotopy u u') := by
  intro q _ i
  obtain ⟨hKI, hInj, hGE, hQI, -⟩ := GlobalTheory.T.chosenInjectiveResolution_etaleSheaf_properties (ZMod q) (tw q i)
  refine ⟨⟨hGE, resAug _, hQI, fun _ _ => rfl⟩, fun t => ?_, ?_⟩
  · haveI := hInj t
    exact (GlobalTheory.T.flat_sections_of_injective_zmodEtaleSheaf q ((res _ (tw q i)).X t)).2
  intro T e ⟨_, ε, hε, he⟩
  have hext := GlobalTheory.T.extend_chainMap_along_quasiIso_kInjective (ZMod q) (tw q i) T (res _ (tw q i)) ε
  refine ⟨?_, fun u u' huu => ?_⟩
  · obtain ⟨m, hm⟩ := hext.1 (resAug _)
    refine ⟨m, fun U ζ => ?_⟩
    rw [← he U ζ, ← sec_map_comp, ← HomologicalComplex.comp_f, hm]
    rfl
  · refine hext.2 u u' ?_
    have htw := (GlobalTheory.T.tateTwist_sections_locally_generated q i).2.2.2
    obtain ⟨hres, hrel, huniq⟩ := htw
    let ψ : (T ⟶ res _ (tw q i)) → (tw q i ⟶ (res _ (tw q i)).X 0) := fun v => sglι (tw q i) ≫ (ε ≫ v).f 0
    have key : ∀ v : T ⟶ res _ (tw q i), ∀ U ζ, Sec.map (ψ v) (twGen i ζ) = Sec.map (v.f 0) (e U ζ) := by
      intro v U ζ
      rw [← he U ζ]
      rfl
    have hnat : ∀ v : T ⟶ res _ (tw q i), ∀ (V U : Scheme.{0}) (g : V ⟶ U) (ζ : Prim q Γ(U, ⊤)),
        Sec.res g (Sec.map (ψ v) (twGen i ζ)) = Sec.map (ψ v) (twGen i (ζ.map g.appTop.hom)) := by
      intro v V U g ζ
      rw [← hres V U g ζ]
      exact (congrArg (fun f => f.hom (twGen i ζ)) ((ψ v).hom.naturality g.op)).symm
    have hrl : ∀ v : T ⟶ res _ (tw q i), ∀ (U : Scheme.{0}) (ζ ξ : Prim q Γ(U, ⊤)) (a : (ZMod q)ˣ),
        ξ.1 = ζ.1 ^ (a : ZMod q).val →
        Sec.map (ψ v) (twGen i ξ) = ((a ^ i : (ZMod q)ˣ) : ZMod q).val • Sec.map (ψ v) (twGen i ζ) := by
      intro v U ζ ξ a h
      rw [hrel U ζ ξ a h]
      exact map_nsmul _ _ _
    obtain ⟨φ, -, hφ⟩ := huniq ((res _ (tw q i)).X 0) (fun U ζ => Sec.map (ψ u) (twGen i ζ)) (hnat u) (hrl u)
    have h1 := hφ (ψ u) fun U ζ => rfl
    have h2 := hφ (ψ u') fun U ζ => by rw [key, key, huu]
    have h12 : ψ u = ψ u' := h2.symm ▸ h1 ▸ rfl
    apply HomologicalComplex.from_single_hom_ext
    exact (Iso.cancel_iso_inv_left (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (tw q i)) _ _).1 h12

end GlobalTheory.EtC.TwResExt
end
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tateTwistResolution_map_exists_unique_homotopy : ∀ (q : ℕ) [NeZero q] (i : ℤ), IsTwRes q i (res _ (tw q i)) (fun _ ζ => resGen i ζ) ∧ (∀ t, FlatS ((res _ (tw q i)).X t)) ∧ ∀ {T : Cx (ZMod q)} (e : ∀ U : Scheme.{0}, Prim q Γ(U, ⊤) → Sec (T.X 0) U), IsTwRes q i T e → (∃ u : T ⟶ res _ (tw q i), ∀ U ζ, Sec.map (u.f 0) (e U ζ) = resGen i ζ) ∧ ∀ u u' : T ⟶ res _ (tw q i), (∀ U ζ, Sec.map (u.f 0) (e U ζ) = Sec.map (u'.f 0) (e U ζ)) → Nonempty (Homotopy u u') := by
  first | (exact @GlobalTheory.EtC.TwResExt.twRes_ext) | (exact GlobalTheory.EtC.TwResExt.twRes_ext) | (intros; apply GlobalTheory.EtC.TwResExt.twRes_ext  <;> assumption)
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.TwPairUniq

theorem main : ∀ (q : ℕ) [NeZero q] (i j : ℤ), IsTwPair (twPair q i j) ∧ ∀ (k : ℤ), i + j = k →
    ∀ μ ν : Pair (res _ (tw q i)) (res _ (tw q j)) (res _ (tw q k)), IsTwPair μ → IsTwPair ν →
    ∀ (E : Spc) {n m w : ℤ} (h : n + m = w), μ.cup E h = ν.cup E h := by
  intro q _ i j
  obtain ⟨T, τ, hτ⟩ := GlobalTheory.T.exists_isTensor_etaleSheafComplexPairing (ZMod q) (res _ (tw q i)) (res _ (tw q j))
  obtain ⟨hI, -, -⟩ := GlobalTheory.T.tateTwistResolution_map_exists_unique_homotopy q i
  obtain ⟨hJ, hJflat, -⟩ := GlobalTheory.T.tateTwistResolution_map_exists_unique_homotopy q j
  have hT : IsTwRes q (i + j) T (fun U ζ => τ.mul U 0 0 0 (add_zero 0) (resGen i ζ) (resGen j ζ)) :=
    GlobalTheory.T.isTateTwistResolution_tensor_flat q i j (i + j) rfl _ _ hI hJ hJflat τ hτ
  obtain ⟨huniv, -, hext⟩ := GlobalTheory.T.isTensor_universal_property (ZMod q) τ hτ
  obtain ⟨-, -, hK⟩ := GlobalTheory.T.tateTwistResolution_map_exists_unique_homotopy q (i + j)
  obtain ⟨⟨u, hu⟩, huniq⟩ := hK _ hT
  refine ⟨?_, ?_⟩
  · obtain ⟨ν, hν⟩ := hext u
    show IsTwPair (pick IsTwPair)
    refine pick_spec ⟨ν, fun U ζ => ?_⟩
    exact (hν U 0 0 0 (add_zero 0) (resGen i ζ) (resGen j ζ)).symm.trans (hu U ζ)
  · intro k hk μ ν hμ hν E n m w h
    subst hk
    obtain ⟨uμ, huμ, -⟩ := huniv μ (𝟙 _) (𝟙 _)
    obtain ⟨uν, huν, -⟩ := huniv ν (𝟙 _) (𝟙 _)
    have hom := huniq uμ uν (fun U ζ =>
      (huμ U 0 0 0 (add_zero 0) (resGen i ζ) (resGen j ζ)).trans ((hμ U ζ).trans ((hν U ζ).symm.trans
        (huν U 0 0 0 (add_zero 0) (resGen i ζ) (resGen j ζ)).symm)))
    obtain ⟨hid, -, -, -, hhtp⟩ := GlobalTheory.T.hypercohomologyPullbackPushforward_functorial (ZMod q)
    have key : ∀ (π : Pair (res _ (tw q i)) (res _ (tw q j)) (res _ (tw q (i + j)))) (v : T ⟶ res _ (tw q (i + j))),
        τ.Compat π (𝟙 _) (𝟙 _) v → ∀ a b, π.cup E h a b = cpush _ v w (τ.cup E h a b) := by
      intro π v hc a b
      rw [GlobalTheory.T.cupProduct_natural_in_sheafComplexPairing (ZMod q) τ π (𝟙 _) (𝟙 _) v hc E h a b, (hid _ _ n a).2, (hid _ _ m b).2]
    refine AddMonoidHom.ext fun a => AddMonoidHom.ext fun b => ?_
    rw [key μ uμ huμ, key ν uν huν, (hhtp uμ uν hom _ w).2]

end GlobalTheory.EtC.TwPairUniq
end

section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tateTwistResolutionPairing_spec_and_cup_unique : ∀ (q : ℕ) [NeZero q] (i j : ℤ), IsTwPair (twPair q i j) ∧ ∀ (k : ℤ), i + j = k → ∀ μ ν : Pair (res _ (tw q i)) (res _ (tw q j)) (res _ (tw q k)), IsTwPair μ → IsTwPair ν → ∀ (E : Spc) {n m w : ℤ} (h : n + m = w), μ.cup E h = ν.cup E h := by
  first
  | exact @GlobalTheory.EtC.TwPairUniq.main
  | exact GlobalTheory.EtC.TwPairUniq.main
  | (intros; apply GlobalTheory.EtC.TwPairUniq.main <;> assumption)
end
