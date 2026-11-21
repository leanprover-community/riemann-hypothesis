import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitExEveryDatum
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceCompactOpenMembershipStatement

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.MoveTyped

open Formalism.L2.NG

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]

theorem isSubrep_bot (ρ : Representation ℂ (GQ L n) W) :
    IsSubrep ρ (⊥ : Submodule ℂ (GAf L n → W)) :=
  ⟨bot_le, fun h f hf => by
    rw [Submodule.mem_bot] at hf ⊢
    subst hf
    exact map_zero _⟩

theorem isSubrep_sup {ρ : Representation ℂ (GQ L n) W} {X Y : Submodule ℂ (GAf L n → W)}
    (hX : IsSubrep ρ X) (hY : IsSubrep ρ Y) : IsSubrep ρ (X ⊔ Y) :=
  ⟨sup_le hX.le hY.le, fun h f hf => by
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hf
    rw [map_add]
    exact Submodule.add_mem_sup (hX.stable h a ha) (hY.stable h b hb)⟩

theorem isSubrep_inf {ρ : Representation ℂ (GQ L n) W} {X Y : Submodule ℂ (GAf L n → W)}
    (hX : IsSubrep ρ X) (hY : IsSubrep ρ Y) : IsSubrep ρ (X ⊓ Y) :=
  ⟨inf_le_right.trans hY.le, fun h f hf => ⟨hX.stable h f hf.1, hY.stable h f hf.2⟩⟩

theorem sup_typed_eq_bot {ρ : Representation ℂ (GQ L n) W} {J : Subgroup (GAf L n)} {χ : J →* ℂˣ}
    {X Y : Submodule ℂ (GAf L n → W)} (hX : IsSubrep ρ X) (hXT : X ⊓ TypeSp ρ J χ = ⊥)
    (hY : IsIrrRep ρ Y) (hYT : Y ⊓ TypeSp ρ J χ = ⊥) : (X ⊔ Y) ⊓ TypeSp ρ J χ = ⊥ := by
  by_cases hXY : X ⊓ Y = ⊥
  · rw [eq_bot_iff]
    rintro v ⟨hv, hvT⟩
    have hvT' : v ∈ AFall L n ρ ∧ ∀ κ : J, rt L n (κ : GAf L n) v = ((χ κ : ℂˣ) : ℂ) • v := hvT
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hv
    have key : ∀ κ : J, rt L n (κ : GAf L n) a = ((χ κ : ℂˣ) : ℂ) • a ∧
        rt L n (κ : GAf L n) b = ((χ κ : ℂˣ) : ℂ) • b := by
      intro κ
      have e := hvT'.2 κ
      rw [map_add, smul_add] at e
      have hmem : rt L n (κ : GAf L n) a - ((χ κ : ℂˣ) : ℂ) • a ∈ X ⊓ Y := by
        refine ⟨Submodule.sub_mem _ (hX.stable _ a ha) (Submodule.smul_mem _ _ ha), ?_⟩
        have hab : rt L n (κ : GAf L n) a - ((χ κ : ℂˣ) : ℂ) • a =
            ((χ κ : ℂˣ) : ℂ) • b - rt L n (κ : GAf L n) b := by
          rw [sub_eq_sub_iff_add_eq_add, e, add_comm]
        rw [hab]
        exact Submodule.sub_mem _ (Submodule.smul_mem _ _ hb) (hY.1.stable _ b hb)
      rw [hXY, Submodule.mem_bot, sub_eq_zero] at hmem
      refine ⟨hmem, ?_⟩
      rw [hmem] at e
      exact add_left_cancel e
    have ha0 : a ∈ X ⊓ TypeSp ρ J χ := ⟨ha, hX.le ha, fun κ => (key κ).1⟩
    have hb0 : b ∈ Y ⊓ TypeSp ρ J χ := ⟨hb, hY.1.le hb, fun κ => (key κ).2⟩
    rw [hXT, Submodule.mem_bot] at ha0
    rw [hYT, Submodule.mem_bot] at hb0
    simp [ha0, hb0]
  · have hle : X ⊓ Y = Y := (hY.2.2 _ (isSubrep_inf hX hY.1) inf_le_right).resolve_left hXY
    have hYX : Y ≤ X := hle ▸ inf_le_left
    rw [sup_eq_left.2 hYX, hXT]

theorem typed_eq_bot_of_iso {ρ : Representation ℂ (GQ L n) W} {J : Subgroup (GAf L n)} {χ : J →* ℂˣ}
    {S S' : Submodule ℂ (GAf L n → W)} (hS : IsSubrep ρ S) (hiso : IsoRep S S')
    (h : S ⊓ TypeSp ρ J χ = ⊥) : S' ⊓ TypeSp ρ J χ = ⊥ := by
  obtain ⟨T, hT⟩ := hiso
  rw [eq_bot_iff]
  rintro u ⟨hu, huT⟩
  have huT' : u ∈ AFall L n ρ ∧ ∀ κ : J, rt L n (κ : GAf L n) u = ((χ κ : ℂˣ) : ℂ) • u := huT
  obtain ⟨f, hfu⟩ : ∃ f : S, T f = ⟨u, hu⟩ := ⟨T.symm _, T.apply_symm_apply _⟩
  have hf : ∀ κ : J, rt L n (κ : GAf L n) (f : GAf L n → W) = ((χ κ : ℂˣ) : ℂ) • (f : GAf L n → W) := by
    intro κ
    let f' : S := ⟨rt L n (κ : GAf L n) f, hS.stable _ _ f.2⟩
    have e := hT κ f f' rfl
    have hTT : T f' = T (((χ κ : ℂˣ) : ℂ) • f) := by
      apply Subtype.ext
      rw [e, map_smul, Submodule.coe_smul, hfu]
      exact huT'.2 κ
    have := congrArg Subtype.val (T.injective hTT)
    simpa [f'] using this
  have hfm : (f : GAf L n → W) ∈ S ⊓ TypeSp ρ J χ := ⟨f.2, hS.le f.2, hf⟩
  rw [h, Submodule.mem_bot] at hfm
  have hf0 : f = 0 := Subtype.ext hfm
  rw [hf0, map_zero] at hfu
  have := congrArg Subtype.val hfu
  simpa using this.symm

theorem typed_of_isoTyp : ∀ {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W : Type} [AddCommGroup W]
    [Module ℂ W] (ρ : Representation ℂ (GQ L n) W) (J : Subgroup (GAf L n)) (χ : J →* ℂˣ)
    (S : Submodule ℂ (GAf L n → W)), Formalism.L2.NG.IsSubrep ρ S →
    Formalism.L2.NG.isoTyp ρ S ⊓ Formalism.L2.NG.TypeSp ρ J χ ≠ ⊥ → S ⊓ Formalism.L2.NG.TypeSp ρ J χ ≠ ⊥ := by
  intro L _ _ _ n W _ _ ρ J χ S hS hne h0
  apply hne
  have hfam : ∀ S' ∈ {S' | IsIrrRep ρ S' ∧ IsoRep S S'}, S' ⊓ TypeSp ρ J χ = ⊥ :=
    fun S' hS' => typed_eq_bot_of_iso hS hS'.2 h0
  have fin : ∀ s : Finset (Submodule ℂ (GAf L n → W)), (↑s : Set _) ⊆ {S' | IsIrrRep ρ S' ∧ IsoRep S S'} →
      IsSubrep ρ (⨆ i ∈ s, i) ∧ (⨆ i ∈ s, i) ⊓ TypeSp ρ J χ = ⊥ := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro _; simp [isSubrep_bot]
    | insert a s ha ih =>
      intro hs
      rw [Finset.coe_insert, Set.insert_subset_iff] at hs
      obtain ⟨h1, h2⟩ := ih hs.2
      rw [Finset.iSup_insert, sup_comm]
      exact ⟨isSubrep_sup h1 hs.1.1.1, sup_typed_eq_bot h1 h2 hs.1.1 (hfam a hs.1)⟩
  rw [eq_bot_iff]
  rintro v ⟨hv, hvT⟩
  unfold isoTyp at hv
  obtain ⟨s, hs, hvs⟩ := Submodule.mem_sSup_iff_exists_finset.1 hv
  have hb := (fin s hs).2
  rw [eq_bot_iff] at hb
  exact hb ⟨hvs, hvT⟩

end GlobalTheory.MoveTyped
end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inf_typeSpace_ne_bot_of_isotypicPart : ∀ {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (GQ L n) W) (J : Subgroup (GAf L n)) (χ : J →* ℂˣ) (S : Submodule ℂ (GAf L n → W)), Formalism.L2.NG.IsSubrep ρ S → Formalism.L2.NG.isoTyp ρ S ⊓ Formalism.L2.NG.TypeSp ρ J χ ≠ ⊥ → S ⊓ Formalism.L2.NG.TypeSp ρ J χ ≠ ⊥ := by
  atlas_forward_decl GlobalTheory.MoveTyped.typed_of_isoTyp
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.AutPart

theorem heckePol_map_eq_frobPol : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : SideA D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C) (hCS : ChoiceSide D cf M Bs.exp C tp) (hMI : MtInput D M tp.tup C.Q) (hstar : ∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) (hE : ∀ j g, ∃ z : ℤ, eExp D j g = z) (hsp : ∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) (hCh : GlobalTheory.RowTie.ChebSplit D.nd) (big : D.what₂.places.Pl → Finset ℂ) (X : LocNd (lay0 D)) (T : LocTw X) (Sp : NdSpec A.pl M C big X T) (i : X.nd.Loc) (ι : Type) [Finite ι] (F : ι → Submodule ℂ (GAf D.host.E D.R.nV → (mlX M X i).wt.W)) (irr : ∀ P, NG.IsIrrRep (mlX M X i).wt.ρ (F P)) (hinj : ∀ P P', NG.IsoRep (F P) (F P') → P = P') (hsurj : ∀ S', NG.IsIrrRep (mlX M X i).wt.ρ S' → (NG.isoTyp (mlX M X i).wt.ρ S').comap (mlX M X i).real ≠ ⊥ → ∃ P, NG.IsoRep (F P) S') (hne : ∀ P, (NG.isoTyp (mlX M X i).wt.ρ (F P)).comap (mlX M X i).real ≠ ⊥) (hind : iSupIndep (fun P => (NG.isoTyp (mlX M X i).wt.ρ (F P)).comap (mlX M X i).real)) (htop : ⨆ P, (NG.isoTyp (mlX M X i).wt.ρ (F P)).comap (mlX M X i).real = ⊤) (ptV : ι → Option (X.nd.X i)), (∀ P x, ptV P = some x ↔ (∀ (w : PlE D.host) (k : ℕ) (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)), SplitOut X.nd i w → IsConjPl D.host w s.w → IsUnif D.host.E s.v ϖ → 1 ≤ k → k ≤ D.R.nV → ∀ y ∈ ((NG.isoTyp (mlX M X i).wt.ρ (F P)).comap (mlX M X i).real), NG.tN (mlX M X i).J s ϖ k ((mlX M X i).real y) = (((qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))).toRingHom.comp (Sp.iq i)).comp (algebraMap (X.nd.O i) (FractionRing (X.nd.O i)))) ((X.nd.hT i w k : X.nd.X i → X.nd.O i) x) • (mlX M X i).real y)) → ∀ P x, ptV P = some x → ∀ w, SplitOut X.nd i w → (heckePol X.nd i x w).map (((qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))).toRingHom.comp (Sp.iq i)).comp (algebraMap (X.nd.O i) (FractionRing (X.nd.O i)))) = ((D.naut.frobEig (D.naut.lpTw (D.nbc.locAU (X.nd.j i) (A.au.cls (X.nd.j i) (X.nd.j_range i).1 (X.nd.j_range i).2 { (mlX M X i).wt with S := F P, irrS := irr P }) w) ((1 - (D.R.nV : ℝ)) / 2))).map fun α => Polynomial.X - Polynomial.C α).prod := by
  intro D cf jE A low Pq S hL eig θ Bs M C tp hCS hMI hstar hE hsp hCh big X T Sp i ι _ F irr hinj hsurj hne hind htop ptV hpt P x hx w hw
  obtain ⟨s, ϖ, hc, hu⟩ := GlobalTheory.SplitConjPlace.splitEx_all D w hw.1
  have heig := (hpt P x).1 hx
  have hlev := GlobalTheory.T.split_place_compact_open_membership D cf jE A M C tp hMI big X T Sp i w s hw hc
  have hne' : Formalism.L2.NG.isoTyp (mlX M X i).wt.ρ (F P) ⊓ Formalism.L2.NG.TypeSp (mlX M X i).wt.ρ (mlX M X i).J (mlX M X i).χ ≠ ⊥ := by
    obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (hne P)
    rw [Submodule.ne_bot_iff]
    refine ⟨(mlX M X i).real y, ⟨hy, ?_⟩, fun h0 => hy0 ((mlX M X i).real_inj (h0.trans (map_zero _).symm))⟩
    rw [← (mlX M X i).real_range]; exact LinearMap.mem_range_self _ _
  obtain ⟨f, ⟨hfF, hfT⟩, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (GlobalTheory.T.inf_typeSpace_ne_bot_of_isotypicPart (mlX M X i).wt.ρ (mlX M X i).J (mlX M X i).χ (F P) (irr P).1 hne')
  have hfR : f ∈ LinearMap.range (mlX M X i).real := by rw [(mlX M X i).real_range]; exact hfT
  obtain ⟨y, rfl⟩ := hfR
  have hyV : y ∈ (Formalism.L2.NG.isoTyp (mlX M X i).wt.ρ (F P)).comap (mlX M X i).real := by
    show (mlX M X i).real y ∈ Formalism.L2.NG.isoTyp (mlX M X i).wt.ρ (F P)
    exact (le_sSup (show F P ∈ {S' | Formalism.L2.NG.IsIrrRep (mlX M X i).wt.ρ S' ∧ Formalism.L2.NG.IsoRep (F P) S'} from
      ⟨irr P, LinearEquiv.refl ℂ _, fun h f f' e => e⟩)) hfF
  have hsph : ∀ κ ∈ Umax D.host.E D.R.nV, TrivOutside {s.v} κ →
      Formalism.L2.NG.rt D.host.E D.R.nV κ ((mlX M X i).real y) = (mlX M X i).real y := by
    intro κ hκ ht
    have hJ : κ ∈ (mlX M X i).J := ((hlev κ ht).1).2 hκ
    have := hfT.2 ⟨κ, hJ⟩
    rw [this, (hlev κ ht).2 hJ]; simp
  have hpol := A.au.locPol (X.nd.j i) (X.nd.j_range i).1 (X.nd.j_range i).2
    { (mlX M X i).wt with S := F P, irrS := irr P } s w ϖ hc hu (mlX M X i).J (fun κ ht => (hlev κ ht).1)
    ((mlX M X i).real y) hfF hf0 hsph
    (fun k => (((qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))).toRingHom.comp (Sp.iq i)).comp (algebraMap (X.nd.O i) (FractionRing (X.nd.O i)))) ((X.nd.hT i w k : X.nd.X i → X.nd.O i) x))
    (fun k hk1 hk2 => heig w k s ϖ hw hc hu hk1 hk2 y hyV)
  refine Eq.trans ?_ hpol
  simp [heckePol, Polynomial.map_sum]

end GlobalTheory.AutPart
end
end
