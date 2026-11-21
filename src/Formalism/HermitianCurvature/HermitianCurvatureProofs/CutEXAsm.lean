import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEX2
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SliceContOn
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FnValLift
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BasePointMemDomain
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FrameTransport

section
noncomputable section

open Matrix MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutEX

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem residue_top_exceptional : ResTop := by
  intro E _ _ k ρ hρ J c g
  subst hρ
  simp [Q.resG, Q.wCell]

theorem radial_extension_holds : RadExt := by
  intro Wp Wq _ _ _ _ k ρ z z' π π' Ψ Ψ' h
  apply Subtype.ext
  funext c g
  by_cases hx : ((c, g) : (Fin ρ → ℂ) × Q.Mx k ρ) ∈ Q.DomR k ρ z z'
  · exact h _ hx
  · rw [Ψ.2.1 (c, g) hx, Ψ'.2.1 (c, g) hx]

theorem radial_of_function_holds : RadOfFun := by
  classical
  intro Wp Wq _ _ _ _ k ρ z z' π π' f hloc hequiv
  have hUW : ∀ {w : Fin (2 * ρ + k + 1) → ℂ} {h : Mx k ρ}, h ∈ UWset k ρ w → h ∈ Glev k ρ (Fin.last ρ) :=
    fun hh => ⟨hh.1, fun a _ => hh.2.1 a⟩
  refine ⟨⟨fun c g => if (c, g) ∈ DomR k ρ z z' then f g else 0, ?_, ?_, ?_⟩, ?_⟩
  · intro x hx
    show (if (x.1, x.2) ∈ DomR k ρ z z' then f x.2 else 0) = 0
    exact if_neg hx
  · intro x₀ hx₀
    obtain ⟨hΩ, hG, hpos⟩ := hx₀
    obtain ⟨U, F, hU, hgU, hF, hFe⟩ := hloc x₀.2 hG hpos
    refine ⟨OmX ρ ×ˢ (U ∩ {g | 0 < GGl k ρ z z' g}), fun x => F x.2, ?_, ?_, ?_, ?_⟩
    · exact (Formalism.FourierDecayAlt.P.Qx5.isOpen_OmX ρ).prod
        (hU.inter (isOpen_lt continuous_const (Formalism.FourierDecayAlt.P.Qx5.GGl_continuous k ρ z z')))
    · exact ⟨hΩ, hgU, hpos⟩
    · exact hF.comp contDiff_snd.contDiffOn (fun x hx => hx.2.1)
    · intro x hx hxG
      have hxD : (x.1, x.2) ∈ DomR k ρ z z' := ⟨hx.1, hxG, hx.2.2⟩
      show (if (x.1, x.2) ∈ DomR k ρ z z' then f x.2 else 0) = F x.2
      rw [if_pos hxD]
      exact hFe x.2 hx.2.1 hxG
  · intro x hx h hh h' hh'
    obtain ⟨hΩ, hG, hpos⟩ := hx
    have hD : (x.1, h * x.2 * h') ∈ DomR k ρ z z' :=
      ⟨hΩ, Formalism.FourierDecayAlt.P.Qx5.Glev_mul (Formalism.FourierDecayAlt.P.Qx5.Glev_mul (hUW hh) hG) (hUW hh'),
        by rw [Formalism.FourierDecayAlt.P5.Rad.GGl_uw hh hh']; exact hpos⟩
    have hD0 : (x.1, x.2) ∈ DomR k ρ z z' := ⟨hΩ, hG, hpos⟩
    show (if (x.1, h * x.2 * h') ∈ DomR k ρ z z' then f (h * x.2 * h') else 0) =
      π h ∘SL (if (x.1, x.2) ∈ DomR k ρ z z' then f x.2 else 0) ∘SL π' h'
    rw [if_pos hD, if_pos hD0]
    exact hequiv x.2 hG hpos h hh h' hh'
  · intro x hx
    show (if (x.1, x.2) ∈ DomR k ρ z z' then f x.2 else 0) = f x.2
    exact if_pos hx

theorem determinant_vanishing_holds : ZxDet := by
  intro r h hh v
  unfold PBQ.zxH
  rw [Matrix.det_reindex_self, Matrix.det_mul]
  exact mul_ne_zero (LeftFubiniLemmas.lh_unit _ v).ne_zero
    (Formalism.FourierDecayAlt.P.PBM.hMat_det_ne _ _ (fun a => Formalism.FourierDecayAlt.P.PBJ.Asm.ptScal_ne h hh.1 a a.isLt))

end Formalism.FourierDecayAlt.P.CutEX

namespace Formalism.FourierDecayAlt.P

theorem residue_top_exceptional_level : CutEX.ResTop := CutEX.residue_top_exceptional
theorem radial_extension_exceptional : CutEX.RadExt := CutEX.radial_extension_holds
theorem radial_of_function_exceptional : CutEX.RadOfFun := CutEX.radial_of_function_holds
theorem determinant_exceptional_holds : CutEX.ZxDet := CutEX.determinant_vanishing_holds

end Formalism.FourierDecayAlt.P
end
end

section
open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.WordCorrespondence

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.PBH

theorem transport_gen {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (k n i r' : ℕ) (hn : i + r' = n) (hr' : r' = 0)
    {z z' : Fin (2 * n + k + 1) → ℂ} {zs zs' : Fin (2 * r' + k + 1) → ℂ}
    (hz : D.castV hn (liftVec k i r' zs) = z) (hz' : D.castV hn (liftVec k i r' zs') = z')
    {π : Mx k n → (Wp →L[ℂ] Wp)} {π' : Mx k n → (Wq →L[ℂ] Wq)} {πs : Mx k r' → (Wp →L[ℂ] Wp)}
    {πs' : Mx k r' → (Wq →L[ℂ] Wq)}
    (hπ : ∀ y, πs y = π (D.castM hn (ιLev k i r' y))) (hπ' : ∀ y, πs' y = π' (D.castM hn (ιLev k i r' y)))
    (X₀ : ActualOps k n z z' π π') (L₀ : R.LevelData (Pr (RadSp k n z z' π π')) n)
    (st₀ : Fr.Start (Pr (RadSp k n z z' π π')))
    (X : ActualOps k r' zs zs' πs πs') (L : R.LevelData (Pr (RadSp k r' zs zs' πs πs')) r')
    (st : Fr.Start (Pr (RadSp k r' zs zs' πs πs')))
    (hL₀ : IsActualLevel X₀ L₀) (hL : IsActualLevel X L) (s : ℂ) (hst₀ : ∀ Y, st₀.QQ Y = s • X₀.QQ Y)
    (hst : ∀ Y, st.QQ Y = s • X.QQ Y) (hq : st₀.q = st.q) (hinv : st₀.inv = st.inv)
    (hSL₀ : Fr.IsStarLevel L₀) (hSL : Fr.IsStarLevel L) (hs₀ : Fr.IsLevelStart L₀ st₀) (hs : Fr.IsLevelStart L st)
    (c : Fin n → ℂ) (hc : c ∈ OmX n) :
    ∃ T : RadSp k n z z' π π' →ₗ[ℂ] RadSp k r' zs zs' πs πs',
      (∀ Ψ c' g, (T Ψ : Fn k r' (Wq →L[ℂ] Wp)) c' g = (Ψ : Fn k n (Wq →L[ℂ] Wp)) c (D.castM hn (ιLev k i r' g))) ∧
      ∀ (w : List C.Letter), Fr.admitted st₀ (D.positionted w) → Fr.admitted st (D.positionted w) →
      ∀ (Ψ : Wd.Ix (Fin w.length) → RadSp k n z z' π π') (e : Wd.Ix (Fin w.length)) (c' : Fin r' → ℂ)
        (g : B.Mat k r'),
        (P5.act (Fr.ofWord L₀ st₀ (D.positionted w)).F Ψ e : Fn k n (Wq →L[ℂ] Wp)) c (D.castM hn (ιLev k i r' g)) =
          (P5.act (Fr.ofWord L st (D.positionted w)).F (fun e' => T (Ψ e')) e : Fn k r' (Wq →L[ℂ] Wp)) c' g := by
  subst hn
  rw [P.JCTx5.castV_rfl] at hz hz'
  subst hz hz'
  obtain rfl : πs = fun y => π (ιLev k i r' y) := funext fun y => by rw [hπ, P.JCTx5.castM_rfl]
  obtain rfl : πs' = fun y => π' (ιLev k i r' y) := funext fun y => by rw [hπ', P.JCTx5.castM_rfl]
  have fr := fun (j : Fin 6) v => fn_rs hr' hc X₀ X j v
  have tr := fun Y (a b : Fin 2) v => t_rs hr' hc X₀ X Y a b v
  obtain ⟨-, -, -, -, -, -, h0ζ, h0ζi, h0ζb, h0ζbi, h0G, h0Gi, h0TT⟩ := hL₀
  obtain ⟨-, -, -, -, -, -, hζ, hζi, hζb, hζbi, hG, hGi, hTT⟩ := hL
  have G : Gen (rsL hr' hc zs zs' π π') L₀ L :=
    { ζ := by rw [h0ζ, hζ]; exact rel_mk (fr 0) (fr 2)
      ζi := by rw [h0ζi, hζi]; exact rel_mk (fr 1) (fr 3)
      ζb := by rw [h0ζb, hζb]; exact rel_mk (fr 2) (fr 0)
      ζbi := by rw [h0ζbi, hζbi]; exact rel_mk (fr 3) (fr 1)
      GG := by rw [h0G, hG]; exact rel_mk (fr 4) (fr 4)
      GGi := by rw [h0Gi, hGi]; exact rel_mk (fr 5) (fr 5)
      TT := by rw [h0TT, hTT, tz_lift, tz_lift] }
  have hQ : ∀ Y, MRel (rsL hr' hc zs zs' π π') (st₀.QQ Y) (st.QQ Y) := fun Y => by
    rw [hst₀, hst]
    exact mrel_smul s fun a b => rel_mk (fun v => tr Y a b v) (fun v => tr (star Y) b a v)
  refine ⟨rsL hr' hc zs zs' π π', fun Ψ c' g => by rw [P.JCTx5.castM_rfl]; rfl, fun w h₀ h Ψ e c' g => ?_⟩
  rw [P.JCTx5.castM_rfl]
  have key := act_frame G hQ hq hinv hSL₀ hSL hs₀ hs (D.positionted w) h₀ h Ψ e
  exact congrArg (fun v : RadSp k r' zs zs' _ _ => (v : Fn k r' (Wq →L[ℂ] Wp)) c' g) key

end Formalism.FourierDecayAlt.P.WordCorrespondence

theorem Formalism.FourierDecayAlt.P.frame_transport_to_last_level : Formalism.FourierDecayAlt.P.PBI.FrameTransport := by
  intro Wp Wq _ _ _ _ _ _ P p X₀ μ₀ L₀ st₀ X μ L st hD₀ hD c hc
  obtain ⟨T, hT, hact⟩ := Formalism.FourierDecayAlt.P.WordCorrespondence.transport_gen P.k P.r P.r (P.r - P.r) (by omega) (by omega)
    (p.T.z_lev P.r le_rfl) (p.T.z'_lev P.r le_rfl) (p.T.π_lev P.r le_rfl) (p.T.π'_lev P.r le_rfl)
    X₀ L₀ st₀ X L st hD₀.2.2.1 hD.2.2.1 (Formalism.FourierDecayAlt.M.sgn P p.l0) hD₀.2.2.2.1 hD.2.2.2.1
    (hD₀.2.2.2.2.1.trans hD.2.2.2.2.1.symm) (hD₀.2.2.2.2.2.1.trans hD.2.2.2.2.2.1.symm)
    hD₀.2.2.2.2.2.2.1 hD.2.2.2.2.2.2.1 hD₀.2.2.2.2.2.2.2 hD.2.2.2.2.2.2.2 c hc
  exact ⟨T, hT, fun w h₀ h Ψ e c' g _ _ => hact w h₀ h Ψ e c' g⟩
end
end

section
open Matrix MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.FinRangeListSplitting

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.PBH

section split

variable {k ρ : ℕ} {z z' : Fin (2 * (1 + ρ) + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
  {π : Mx k (1 + ρ) → (Wp →L[ℂ] Wp)} {π' : Mx k (1 + ρ) → (Wq →L[ℂ] Wq)} {S : Type} [Fintype S] [DecidableEq S]

theorem finRange_split (ρ : ℕ) :
    (List.finRange (1 + ρ)).reverse = (List.finRange ρ).reverse.map shS ++ [⟨0, by omega⟩] := by
  refine List.ext_getElem (by simp; omega) fun i h1 h2 => ?_
  by_cases hi : i < ρ
  · rw [List.getElem_append_left (by simpa using hi)]
    simp only [List.getElem_reverse, List.getElem_map, List.getElem_finRange, List.length_finRange]
    ext
    simp [shS]
    omega
  · rw [List.getElem_append_right (by simp; omega)]
    simp only [List.getElem_reverse, List.getElem_finRange, List.length_finRange, List.length_map,
      List.length_reverse, List.getElem_singleton]
    ext
    simp
    omega

theorem bTall_split (L : R.LevelData (Pr (RadSp k (1 + ρ) z z' π π')) (1 + ρ)) (w : List (Wd.Letter ℂ S)) :
    P5.bTall L w = ((List.finRange ρ).reverse.map fun l => P5.bTl L (shS l) w).prod * P5.bTl L ⟨0, by omega⟩ w := by
  unfold P5.bTall
  rw [finRange_split, List.map_append, List.map_map, List.prod_append]
  simp [Function.comp_def]

end split

section rel

variable {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] {T : V →ₗ[ℂ] V'}
  {S : Type} [Fintype S] [DecidableEq S]

theorem arel_listProd {ι : Type} (f : ι → Wd.SlopeTestRemainingChoices S (Pr V)) (f' : ι → Wd.SlopeTestRemainingChoices S (Pr V'))
    (h : ∀ i, ARel T (f i) (f' i)) : ∀ l : List ι, ARel T (l.map f).prod (l.map f').prod
  | [] => by simp only [List.map_nil, List.prod_nil]; exact arel_one
  | a :: l => by
    simp only [List.map_cons, List.prod_cons]
    exact arel_mul (h a) (arel_listProd f f' h l)

end rel

section tr

variable {k ρ : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  {z z' : Fin (2 * ρ + k + 1) → ℂ} {π : Mx k (1 + ρ) → (Wp →L[ℂ] Wp)} {π' : Mx k (1 + ρ) → (Wq →L[ℂ] Wq)}

theorem bTall_tr {t : ℂ} (ht : t ≠ 0)
    {X : ActualOps k (1 + ρ) (liftVec k 1 ρ z) (liftVec k 1 ρ z') π π'}
    {Xs : ActualOps k ρ z z' (fun y => π (ιLev k 1 ρ y)) (fun y => π' (ιLev k 1 ρ y))}
    {L : R.LevelData (Pr (RadSp k (1 + ρ) (liftVec k 1 ρ z) (liftVec k 1 ρ z') π π')) (1 + ρ)}
    {Ls : R.LevelData (Pr (RadSp k ρ z z' (fun y => π (ιLev k 1 ρ y)) (fun y => π' (ιLev k 1 ρ y)))) ρ}
    (hL : IsActualLevel X L) (hLs : IsActualLevel Xs Ls) {S : Type} [Fintype S] [DecidableEq S]
    (w : List (Wd.Letter ℂ S)) (x : Wd.Ix S → RadSp k (1 + ρ) (liftVec k 1 ρ z) (liftVec k 1 ρ z') π π')
    (e : Wd.Ix S) :
    trL ht z z' π π' (P5.act (P5.bTall L w) x e) =
      P5.act (P5.bTall Ls w) (fun a => trL ht z z' π π' (P5.act (P5.bTl L ⟨0, by omega⟩ w) x a)) e := by
  have hop := fun (l : Fin ρ) (i : Fin 6) Φ => op_tr ht X Xs l i Φ
  have hsite : ∀ l : Fin ρ, ARel (trL ht z z' π π') (P5.bTl L (shS l) w) (P5.bTl Ls l w) := by
    intro l
    refine Formalism.FourierDecayAlt.P.PBP.arel_bT ?_ ?_ ?_ w
    · show Rel _ (L.p (shS l)) (Ls.p l)
      rw [hL.1, hLs.1]
      exact rel_mk (fun v => hop l 0 v) (fun v => by simp only [LinearMap.neg_apply, hop l 3, map_neg])
    · show Rel _ (L.c (shS l)) (Ls.c l)
      rw [hL.2.2.1, hLs.2.2.1]
      exact rel_mk (fun v => hop l 1 v) (fun v => hop l 4 v)
    · show Rel _ (L.ci (shS l)) (Ls.ci l)
      rw [hL.2.2.2.1, hLs.2.2.2.1]
      exact rel_mk (fun v => hop l 2 v) (fun v => hop l 5 v)
  have hall : ARel (trL ht z z' π π') ((List.finRange ρ).reverse.map fun l => P5.bTl L (shS l) w).prod
      (P5.bTall Ls w) := arel_listProd _ _ hsite _
  rw [bTall_split, Formalism.FourierDecayAlt.P5.act_mul]
  exact act_tr hall _ e

end tr

section cast

variable {k n ρ : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem bTall_cast (hn : 1 + ρ = n) {z z' : Fin (2 * n + k + 1) → ℂ} {zs zs' : Fin (2 * ρ + k + 1) → ℂ}
    (hz : z = D.castV hn (liftVec k 1 ρ zs)) (hz' : z' = D.castV hn (liftVec k 1 ρ zs'))
    {π : Mx k n → (Wp →L[ℂ] Wp)} {π' : Mx k n → (Wq →L[ℂ] Wq)}
    {πs : Mx k ρ → (Wp →L[ℂ] Wp)} {πs' : Mx k ρ → (Wq →L[ℂ] Wq)}
    (hπ : ∀ y, πs y = π (D.castM hn (ιLev k 1 ρ y))) (hπ' : ∀ y, πs' y = π' (D.castM hn (ιLev k 1 ρ y)))
    (X : ActualOps k n z z' π π') (Xs : ActualOps k ρ zs zs' πs πs')
    (L : R.LevelData (Pr (RadSp k n z z' π π')) n) (Ls : R.LevelData (Pr (RadSp k ρ zs zs' πs πs')) ρ)
    (hL : IsActualLevel X L) (hLs : IsActualLevel Xs Ls) {t : ℂ} (ht : t ≠ 0) :
    ∃ T : RadSp k n z z' π π' →ₗ[ℂ] RadSp k ρ zs zs' πs πs',
      (∀ Φ c g, (T Φ : Fn k ρ (Wq →L[ℂ] Wp)) c g =
        (Φ : Fn k n (Wq →L[ℂ] Wp)) (fun l => consC t c (Fin.cast hn.symm l)) (D.castM hn (ιLev k 1 ρ g))) ∧
      ∀ (S : Type) [Fintype S] [DecidableEq S] (w : List (Wd.Letter ℂ S)) (x : Wd.Ix S → RadSp k n z z' π π')
        (e : Wd.Ix S),
        T (P5.act (P5.bTall L w) x e) =
          P5.act (P5.bTall Ls w) (fun a => T (P5.act (P5.bTl L ⟨0, by omega⟩ w) x a)) e := by
  subst hn
  rw [Formalism.FourierDecayAlt.P.JCTx5.castV_rfl] at hz hz'
  subst hz hz'
  obtain rfl : πs = fun y => π (ιLev k 1 ρ y) := funext fun y => by rw [hπ, Formalism.FourierDecayAlt.P.JCTx5.castM_rfl]
  obtain rfl : πs' = fun y => π' (ιLev k 1 ρ y) := funext fun y => by rw [hπ', Formalism.FourierDecayAlt.P.JCTx5.castM_rfl]
  refine ⟨trL ht zs zs' π π', fun Φ c g => ?_, fun S _ _ w x e => bTall_tr ht hL hLs w x e⟩
  rw [Formalism.FourierDecayAlt.P.JCTx5.castM_rfl]
  rfl

end cast

section misc

theorem exists_cons {n ρ : ℕ} (hn : 1 + ρ = n) (c : Fin n → ℂ) :
    ∃ (t : ℂ) (c' : Fin ρ → ℂ), c = fun l => consC t c' (Fin.cast hn.symm l) := by
  refine ⟨c ⟨0, by omega⟩, fun i => c ⟨i.val + 1, by omega⟩, funext fun l => ?_⟩
  unfold consC
  by_cases h : l.val = 0
  · rw [dif_pos (by simpa using h)]
    exact congrArg c (Fin.ext h)
  · rw [dif_neg (by simpa using h)]
    exact congrArg c (Fin.ext (by simp; omega))

theorem omX_cons {n ρ : ℕ} (hn : 1 + ρ = n) {t : ℂ} {c : Fin ρ → ℂ}
    (h : (fun l => consC t c (Fin.cast hn.symm l)) ∈ OmX n) : t ≠ 0 ∧ c ∈ OmX ρ := by
  refine ⟨?_, fun i => ?_⟩
  · have := h ⟨0, by omega⟩
    simpa [consC] using this
  · have := h ⟨i.val + 1, by omega⟩
    simpa [consC] using this

theorem hcell_cons {n ρ : ℕ} (hn : 1 + ρ = n) (t : ℂ) (c : Fin ρ → ℂ) :
    PBI.hcell (fun l : Fin n => consC t c (Fin.cast hn.symm l)) = (1, t) :: PBI.hcell c := by
  subst hn
  refine List.ext_getElem (by simp [PBI.hcell]; omega) fun i h1 h2 => ?_
  simp only [PBI.hcell, List.getElem_ofFn]
  rcases i with _ | i
  · simp [consC]
  · simp [consC]

theorem hcell_nil {n : ℕ} (hn : n = 0) (c : Fin n → ℂ) : PBI.hcell c = [] := by
  subst hn; rfl

theorem prod_cons {n ρ : ℕ} (hn : 1 + ρ = n) (k : ℕ) (t : ℂ) (c : Fin ρ → ℂ) :
    (∏ i : Fin n, ‖consC t c (Fin.cast hn.symm i)‖ ^ (2 * (n - (i : ℕ)) + k)) =
      ‖t‖ ^ (2 * n + k) * ∏ i : Fin ρ, ‖c i‖ ^ (2 * (ρ - (i : ℕ)) + k) := by
  subst hn
  rw [← (finCongr (Nat.add_comm ρ 1)).prod_comp, Fin.prod_univ_succ]
  congr 1
  simp only [consC, finCongr_apply, Fin.val_cast, Fin.val_succ]
  refine Finset.prod_congr rfl fun i _ => ?_
  congr 2
  omega

theorem iota_split {k n ρ m : ℕ} (hn : 1 + ρ = n) (hm : m = 0) (e1 : n + m = n) (e2 : ρ + m = ρ)
    (g : B.Mat k m) :
    D.castM e1 (ιLev k n m g) = D.castM hn (ιLev k 1 ρ (D.castM e2 (ιLev k ρ m g))) := by
  subst hn hm
  rw [Formalism.FourierDecayAlt.P.JCTx5.castM_rfl, Formalism.FourierDecayAlt.P.JCTx5.castM_rfl, Formalism.FourierDecayAlt.P.JCTx5.castM_rfl]
  exact (ιLev_comp g).symm

theorem castM_iota_self {k a : ℕ} (ha : a = 0) (e : a + a = a) (g : B.Mat k a) : D.castM e (ιLev k a a g) = g := by
  subst ha
  exact Formalism.FourierDecayAlt.P.Dx2.Tower.castMat_levelEmbed_zero e g

theorem resG_empty {k a : ℕ} (ha : a = 0) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (J : Mx k a → E)
    (c : Fin a → ℂ) (g : Mx k a) : resG k a (Fin.last a) J c g = J g := by
  subst ha
  simp [resG, wCell]

theorem ptSize_append (h h' : C.LPt) : D.ptSize (h ++ h') = D.ptSize h + D.ptSize h' := by
  simp [D.ptSize]

end misc

end Formalism.FourierDecayAlt.P.FinRangeListSplitting
end
end

section
open Matrix MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.FinRangeListSplitting

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P5

section core

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

def StepHyp (P : M.Par) (p : KB.Pl P Wp Wq) (G : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) : Prop :=
  ∀ (j : ℕ) (hj : j + 1 ≤ P.r) (h : C.LPt) (hh : D.IsLocPt h j)
    (X : Q.ActualOps (JC.parLev P j).k (JC.parLev P j).r (p.T.bs j).z (p.T.bs j).z' (p.T.bs j).π (p.T.bs j).π')
    (μ : Measure (Mt P.k (P.r - j)))
    (L : R.LevelData (Q.Pr (Q.RadSp (JC.parLev P j).k (JC.parLev P j).r (p.T.bs j).z (p.T.bs j).z' (p.T.bs j).π
      (p.T.bs j).π')) (JC.parLev P j).r)
    (st : Fr.Start (Q.Pr (Q.RadSp (JC.parLev P j).k (JC.parLev P j).r (p.T.bs j).z (p.T.bs j).z' (p.T.bs j).π
      (p.T.bs j).π')))
    (Ψ : Wd.Ix (Fin w.length) →
      Q.RadSp (JC.parLev P j).k (JC.parLev P j).r (p.T.bs j).z (p.T.bs j).z' (p.T.bs j).π (p.T.bs j).π'),
    P5.IsData (JC.parLev P j) (p.T.bs j).z (p.T.bs j).z' (p.T.bs j).π (p.T.bs j).π' X μ L st p.l0 →
    (∀ e, Top.IsRadOf (JC.parLev P j) (p.T.bs j) (Ψ e) (KB.slv p.T G j (by omega) w h hh.2 e)) →
    ∀ (t : ℂ) (ht : D.IsLocPt (h ++ [(1, t)]) (j + 1)) (e : Wd.Ix (Fin w.length)),
    ∀ y ∈ Q.DomR P.k (P.r - (j + 1)) (p.T.bs (j + 1)).z (p.T.bs (j + 1)).z',
      (P5.act (P5.bTl L (⟨0, by change 0 < P.r - j; omega⟩ : Fin (JC.parLev P j).r) (D.positionted w)) Ψ e :
          Q.Fn (JC.parLev P j).k (JC.parLev P j).r (Wq →L[ℂ] Wp))
        (fun l => PBH.consC t y.1 (Fin.cast (by change P.r - j = 1 + (P.r - (j + 1)); omega) l))
          (D.castM (by change 1 + (P.r - (j + 1)) = P.r - j; omega) (ιLev P.k 1 (P.r - (j + 1)) y.2)) =
        ((‖t‖ ^ (2 * (P.r - j) + P.k) : ℝ) : ℂ) •
          Q.resG P.k (P.r - (j + 1)) (Fin.last _)
            (B.JF (p.T.bs (j + 1)) (KB.slv p.T G (j + 1) hj w (h ++ [(1, t)]) ht.2 e)) y.1 y.2

def sW (P : M.Par) (p : KB.Pl P Wp Wq) (G : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter)
    (e : Wd.Ix (Fin w.length)) (q : C.LPt) (hq : D.ptSize q = P.r) : B.Mat P.k (P.r - P.r) → (Wq →L[ℂ] Wp) :=
  D.castF (by rw [hq]) (D.sliceAt P.k P.r p.T.base.z p.T.base.z'
    (D.uwG P.k P.r p.T.base.z p.T.base.z' G P.r le_rfl w e) q)

theorem castF_slice_congr {k r a : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (z z' : Fin (2 * r + k + 1) → ℂ) (F : B.Mat k r → E) {q q' : C.LPt} (hq : q = q')
    (p1 : a = r - D.ptSize q) (p2 : a = r - D.ptSize q') :
    D.castF p1 (D.sliceAt k r z z' F q) = D.castF p2 (D.sliceAt k r z z' F q') := by
  subst hq; rfl

theorem listProd_zero {A : Type*} [Monoid A] {n : ℕ} (hn : n = 0) (f : Fin n → A) :
    ((List.finRange n).reverse.map f).prod = 1 := by
  subst hn; rfl

theorem smul_inv_real {V : Type*} [AddCommGroup V] [Module ℂ V] {a : ℝ} (ha : a ≠ 0) (v : V) :
    ((a : ℝ) : ℂ) • (((a⁻¹ : ℝ) : ℂ) • v) = v := by
  rw [smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ ha, Complex.ofReal_one, one_smul]

theorem core (P : M.Par) (p : KB.Pl P Wp Wq) (G : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter)
    (hst : StepHyp P p G w) :
    ∀ (m j : ℕ), P.r - j = m → ∀ (hjr : j ≤ P.r) (h : C.LPt) (hh : D.IsLocPt h j)
    (X : Q.ActualOps (JC.parLev P j).k (JC.parLev P j).r (p.T.bs j).z (p.T.bs j).z' (p.T.bs j).π (p.T.bs j).π')
    (μ : Measure (Mt P.k (P.r - j)))
    (L : R.LevelData (Q.Pr (Q.RadSp (JC.parLev P j).k (JC.parLev P j).r (p.T.bs j).z (p.T.bs j).z' (p.T.bs j).π
      (p.T.bs j).π')) (JC.parLev P j).r)
    (st : Fr.Start (Q.Pr (Q.RadSp (JC.parLev P j).k (JC.parLev P j).r (p.T.bs j).z (p.T.bs j).z' (p.T.bs j).π
      (p.T.bs j).π')))
    (Ψ : Wd.Ix (Fin w.length) →
      Q.RadSp (JC.parLev P j).k (JC.parLev P j).r (p.T.bs j).z (p.T.bs j).z' (p.T.bs j).π (p.T.bs j).π'),
    P5.IsData (JC.parLev P j) (p.T.bs j).z (p.T.bs j).z' (p.T.bs j).π (p.T.bs j).π' X μ L st p.l0 →
    (∀ e, Top.IsRadOf (JC.parLev P j) (p.T.bs j) (Ψ e) (KB.slv p.T G j hjr w h hh.2 e)) →
    ∀ (e : Wd.Ix (Fin w.length)) (c : Fin (P.r - j) → ℂ), c ∈ OmX (P.r - j) →
    ∀ g : B.Mat P.k (P.r - P.r), g ∈ Q.Glev P.k (P.r - P.r) (Fin.last _) →
      0 < Q.GGl P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' g →
      (P5.act (P5.bTall L (D.positionted w)) Ψ e : Q.Fn (JC.parLev P j).k (JC.parLev P j).r (Wq →L[ℂ] Wp)) c
          (D.castM (by change (P.r - j) + (P.r - P.r) = P.r - j; omega) (ιLev P.k (P.r - j) (P.r - P.r) g)) =
        ((∏ i : Fin (P.r - j), ‖c i‖ ^ (2 * ((P.r - j) - (i : ℕ)) + P.k) : ℝ) : ℂ) •
          B.JF (p.T.bs P.r) (sW P p G w e (h ++ PBI.hcell c)
            (by rw [ptSize_append, hh.2, PBI.ptSize_hcell]; omega)) g := by
  have h0 : P.r - P.r = 0 := Nat.sub_self _
  intro m
  induction m with
  | zero =>
    intro j hjm hjr h hh X μ L st Ψ hD hΨ e c hc g hg hgG
    obtain rfl : j = P.r := by omega
    have hb : P5.bTall L (D.positionted w) = 1 := listProd_zero h0 _
    rw [hb, show P5.act (1 : Wd.SlopeTestRemainingChoices _ _) Ψ = Ψ from Formalism.FourierDecayAlt.P.PBF.polyAction_one₂ Ψ]
    have hcg : D.castM (by omega : (P.r - P.r) + (P.r - P.r) = P.r - P.r) (ιLev P.k (P.r - P.r) (P.r - P.r) g) = g :=
      castM_iota_self h0 _ g
    refine (congrArg (fun g' => ((Ψ e).1 : Q.Fn P.k (P.r - P.r) (Wq →L[ℂ] Wp)) c g') hcg).trans ?_
    refine (hΨ e (c, g) ⟨hc, hg, hgG⟩).trans ?_
    refine (resG_empty h0 _ _ _).trans ?_
    have hp1 : (∏ i : Fin (P.r - P.r), ‖c i‖ ^ (2 * ((P.r - P.r) - (i : ℕ)) + P.k)) = 1 := by
      have : IsEmpty (Fin (P.r - P.r)) := ⟨fun i => by have := i.2; omega⟩
      simp
    have hfin : B.JF (p.T.bs P.r) (KB.slv p.T G P.r hjr w h hh.2 e) g =
        ((∏ i : Fin (P.r - P.r), ‖c i‖ ^ (2 * ((P.r - P.r) - (i : ℕ)) + P.k) : ℝ) : ℂ) •
          B.JF (p.T.bs P.r) (sW P p G w e (h ++ PBI.hcell c)
            (by rw [ptSize_append, hh.2, PBI.ptSize_hcell]; omega)) g := by
      rw [hp1, Complex.ofReal_one, one_smul]
      exact congrArg (fun F => B.JF (p.T.bs P.r) F g)
        (castF_slice_congr _ _ _ (by rw [hcell_nil h0 c, List.append_nil]) _ _)
    exact hfin
  | succ m ih =>
    intro j hjm hjr h hh X μ L st Ψ hD hΨ e c hc g hg hgG
    have hj : j + 1 ≤ P.r := by omega
    have hn : 1 + (P.r - (j + 1)) = P.r - j := by omega

    have hPl : IsPlace (JC.parLev P (j + 1)) (p.T.bs (j + 1)).z (p.T.bs (j + 1)).z' (p.T.bs (j + 1)).π
        (p.T.bs (j + 1)).π' := Formalism.FourierDecayAlt.P.JCTx5.isPlace_lev P p.T ⟨j + 1, by omega⟩ p.hP
    obtain ⟨Xs⟩ := Formalism.FourierDecayAlt.P.actual_operators_exist _ _ _ _ _ _ _ hPl
    obtain ⟨Ls, sts, h1, h2, h3, h4, h5, h6⟩ := Formalism.FourierDecayAlt.P.level_start_actual _ _ _ _ _ _ _ hPl Xs p.l0
    obtain ⟨μs, hμs⟩ := Formalism.FourierDecayAlt.P.exists_zeta_normalized_haar P.k (P.r - (j + 1)) Wp Wq (p.T.bs (j + 1))
    have hDs : P5.IsData (JC.parLev P (j + 1)) (p.T.bs (j + 1)).z (p.T.bs (j + 1)).z' (p.T.bs (j + 1)).π
        (p.T.bs (j + 1)).π' Xs μs Ls sts p.l0 := ⟨hPl, hμs.1, h1, h2, h3, h4, h5, h6⟩

    obtain ⟨t, c', rfl⟩ := exists_cons hn c
    obtain ⟨ht0, hc'⟩ := omX_cons hn hc
    have ht : D.IsLocPt (h ++ [(1, t)]) (j + 1) := Formalism.FourierDecayAlt.P.PBP.isLocPt_snoc hh ht0
    obtain ⟨T, hTr, hTall⟩ := bTall_cast (k := (JC.parLev P j).k) (n := (JC.parLev P j).r)
      (ρ := (JC.parLev P (j + 1)).r) hn (PBH.levTower_bs_z_eq_castV_liftVec p.T j hj) (PBH.levTower_bs_z'_eq_castV_liftVec p.T j hj)
      (PBH.tower_π p.T j hj) (PBH.tower_π' p.T j hj) X Xs L Ls hD.2.2.1 hDs.2.2.1 ht0
    have e2 : P.r - (j + 1) + (P.r - P.r) = P.r - (j + 1) := by omega
    set g2 := D.castM e2 (ιLev P.k (P.r - (j + 1)) (P.r - P.r) g) with hg2
    have hι := iota_split (k := P.k) hn h0 (by omega) e2 g
    refine (congrArg (fun g' => ((P5.act (P5.bTall L (D.positionted w)) Ψ e).1 : Q.Fn P.k (P.r - j) (Wq →L[ℂ] Wp))
      (fun l => PBH.consC t c' (Fin.cast hn.symm l)) g') hι).trans ?_
    have key := hTr (P5.act (P5.bTall L (D.positionted w)) Ψ e) c' g2
    refine key.symm.trans ?_
    refine (congrArg (fun Φ => (Φ.1 : Q.Fn P.k (P.r - (j + 1)) (Wq →L[ℂ] Wp)) c' g2)
      (hTall _ (D.positionted w) Ψ e)).trans ?_

    set lam : ℝ := ‖t‖ ^ (2 * (P.r - j) + P.k) with hlam
    have hlam0 : lam ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.2 ht0)
    let Ψ' : Wd.Ix (Fin w.length) → Q.RadSp (JC.parLev P (j + 1)).k (JC.parLev P (j + 1)).r (p.T.bs (j + 1)).z
        (p.T.bs (j + 1)).z' (p.T.bs (j + 1)).π (p.T.bs (j + 1)).π' :=
      fun a => ((lam⁻¹ : ℝ) : ℂ) • T (P5.act (P5.bTl L ⟨0, by change 0 < P.r - j; omega⟩ (D.positionted w)) Ψ a)
    have hΨ' : ∀ a, Top.IsRadOf (JC.parLev P (j + 1)) (p.T.bs (j + 1)) (Ψ' a)
        (KB.slv p.T G (j + 1) hj w (h ++ [(1, t)]) ht.2 a) := by
      intro a y hy
      have e1 := hTr (P5.act (P5.bTl L ⟨0, by change 0 < P.r - j; omega⟩ (D.positionted w)) Ψ a) y.1 y.2
      have e3 := hst j hj h hh X μ L st Ψ hD hΨ t ht a y hy
      have hcl : ∀ v : Wq →L[ℂ] Wp, ((lam⁻¹ : ℝ) : ℂ) • (((lam : ℝ) : ℂ) • v) = v := fun v => by
        rw [smul_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ hlam0, Complex.ofReal_one, one_smul]
      exact (congrArg (fun v => ((lam⁻¹ : ℝ) : ℂ) • v) (e1.trans e3)).trans (hcl _)
    have hfun : (fun a => ((lam : ℝ) : ℂ) • Ψ' a) =
        (fun a => T (P5.act (P5.bTl L ⟨0, by change 0 < P.r - j; omega⟩ (D.positionted w)) Ψ a)) := by
      funext a
      exact smul_inv_real hlam0 _
    have hA : P5.act (P5.bTall Ls (D.positionted w)) (fun a => T (P5.act (P5.bTl L ⟨0, by change 0 < P.r - j; omega⟩ (D.positionted w)) Ψ a)) e =
        ((lam : ℝ) : ℂ) • P5.act (P5.bTall Ls (D.positionted w)) Ψ' e :=
      (congrArg (fun x => P5.act (P5.bTall Ls (D.positionted w)) x e) hfun).symm.trans
        (congrFun (Formalism.FourierDecayAlt.P.PBP.act_smul' (P5.bTall Ls (D.positionted w)) Ψ' ((lam : ℝ) : ℂ)) e)
    refine (congrArg (fun Φ => (Φ.1 : Q.Fn P.k (P.r - (j + 1)) (Wq →L[ℂ] Wp)) c' g2) hA).trans ?_
    have IH := ih (j + 1) (by omega) hj (h ++ [(1, t)]) ht Xs μs Ls sts Ψ' hDs hΨ' e c' hc' g hg hgG
    refine (congrArg (fun v => ((lam : ℝ) : ℂ) • v) IH).trans ?_
    have hP : ((lam : ℝ) : ℂ) * ((∏ i : Fin (P.r - (j + 1)), ‖c' i‖ ^ (2 * ((P.r - (j + 1)) - (i : ℕ)) + P.k) : ℝ) : ℂ) =
        ((∏ i : Fin (P.r - j), ‖PBH.consC t c' (Fin.cast hn.symm i)‖ ^ (2 * ((P.r - j) - (i : ℕ)) + P.k) : ℝ) : ℂ) := by
      rw [prod_cons hn, Complex.ofReal_mul]
    have hq : (h ++ [(1, t)]) ++ PBI.hcell c' = h ++ PBI.hcell (fun l => PBH.consC t c' (Fin.cast hn.symm l)) := by
      rw [hcell_cons hn, List.append_assoc]
      rfl
    rw [smul_smul]
    exact congr_arg₂ (fun (a : ℂ) (F : B.Mat P.k (P.r - P.r) → (Wq →L[ℂ] Wp)) => a • B.JF (p.T.bs P.r) F g) hP
      (castF_slice_congr _ _ _ hq _ _)

theorem first_basis_vector_isRadial (P : M.Par) (p : KB.Pl P Wp Wq) (G : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter)
    (ΦG : Q.RadSp P.k P.r p.T.base.z p.T.base.z' p.T.base.π p.T.base.π') (hΦG : Top.IsRadOf P p.T.base ΦG G)
    (e : Wd.Ix (Fin w.length)) :
    Top.IsRadOf P p.T.base (Top.firstStateVector ΦG e) (if e = Wd.e1 then G else 0) := by
  intro x hx
  by_cases he : e = Wd.e1
  · rw [show Top.firstStateVector ΦG e = ΦG from if_pos he, if_pos he]
    exact hΦG x hx
  · rw [show Top.firstStateVector ΦG e = 0 from if_neg he, if_neg he]
    have hz : B.JF p.T.base (0 : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) = fun _ => 0 :=
      funext fun g => Formalism.FourierDecayAlt.P.JCx2.bc_JF_zero (Bs := p.T.base) g
    rw [hz]
    simp [Q.resG]

theorem first_basis_vector_isRadial_slice (P : M.Par) (p : KB.Pl P Wp Wq) (G : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter)
    (ΦG : Q.RadSp P.k P.r p.T.base.z p.T.base.z' p.T.base.π p.T.base.π') (hΦG : Top.IsRadOf P p.T.base ΦG G)
    (e : Wd.Ix (Fin w.length)) :
    Top.IsRadOf (JC.parLev P 0) (p.T.bs 0) (Top.firstStateVector ΦG e) (KB.slv p.T G 0 (Nat.zero_le _) w [] rfl e) := by
  have hfun : KB.slv p.T G 0 (Nat.zero_le _) w [] rfl e = if e = Wd.e1 then G else 0 := by
    funext γ
    have hcm : D.castM (k := P.k) (a := P.r - 0) (b := P.r - D.ptSize []) rfl γ = γ := by
      ext i j; rfl
    simp only [KB.slv, D.castF]
    rw [hcm, Formalism.FourierDecayAlt.P.Dx1.SN.sliceAt_nil P.k P.r _ _ p.T.base.z_mem p.T.base.z'_mem,
      Formalism.FourierDecayAlt.P.Dx1.LZ.uwG_zero]
  have h0 := first_basis_vector_isRadial P p G w ΦG hΦG e
  intro x hx
  refine (h0 x hx).trans ?_
  exact congrArg (fun F : B.Mat P.k P.r → (Wq →L[ℂ] Wp) =>
    Q.resG P.k P.r (Fin.last P.r) (B.JF p.T.base F) x.1 x.2) hfun.symm

theorem isLocPt_nil : D.IsLocPt [] 0 := ⟨fun b hb => by simp at hb, rfl⟩

end core

end Formalism.FourierDecayAlt.P.FinRangeListSplitting

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.FinRangeListSplitting

theorem pb_radWordSliceOfHeadPic (hHP : PBP.HeadPic) : PBI.RadWordSlice := by
  intro Wp Wq _ _ _ _ _ _ P p X₀ μ₀ L₀ st₀ hD₀ G hG w hcut ΦG hΦG e c hc g hg hgG
  have hst : StepHyp P p G w := fun j hj h hh X μ L st Ψ hD hΨ t ht a y hy =>
    hHP Wp Wq P p G j hj w h hh X μ L st Ψ hD hG hcut hΨ t ht a y hy
  exact core P p G w hst (P.r - 0) 0 rfl (Nat.zero_le _) [] isLocPt_nil X₀ μ₀ L₀ st₀ (Top.firstStateVector ΦG) hD₀
    (first_basis_vector_isRadial_slice P p G w ΦG hΦG) e c hc g hg hgG

theorem level_zero_picture_of_slice : PBI.PicSlice := by
  intro Wp Wq _ _ _ _ _ _ P p G hG ΦG hΦG c hc g hg hgG
  have hst : StepHyp P p G [] := fun j hj h hh X μ L st Ψ hD hΨ t ht a y hy =>
    Formalism.FourierDecayAlt.P.head_picture_empty_word Wp Wq P p G j hj h hh L Ψ hG hΨ t ht a y hy
  have hPl : IsPlace (JC.parLev P 0) (p.T.bs 0).z (p.T.bs 0).z' (p.T.bs 0).π (p.T.bs 0).π' :=
    Formalism.FourierDecayAlt.P.JCTx5.isPlace_lev P p.T ⟨0, by omega⟩ p.hP
  obtain ⟨X⟩ := Formalism.FourierDecayAlt.P.actual_operators_exist _ _ _ _ _ _ _ hPl
  obtain ⟨L, st, h1, h2, h3, h4, h5, h6⟩ := Formalism.FourierDecayAlt.P.level_start_actual _ _ _ _ _ _ _ hPl X p.l0
  obtain ⟨μ, hμ⟩ := Formalism.FourierDecayAlt.P.exists_zeta_normalized_haar P.k (P.r - 0) Wp Wq (p.T.bs 0)
  have hD : P5.IsData (JC.parLev P 0) (p.T.bs 0).z (p.T.bs 0).z' (p.T.bs 0).π (p.T.bs 0).π' X μ L st p.l0 :=
    ⟨hPl, hμ.1, h1, h2, h3, h4, h5, h6⟩
  have key := core P p G [] hst (P.r - 0) 0 rfl (Nat.zero_le _) [] isLocPt_nil X μ L st (Top.firstStateVector ΦG) hD
    (first_basis_vector_isRadial_slice P p G [] ΦG hΦG) (fun _ => 0) c hc g hg hgG
  have hb0 : P5.bTall L (D.positionted ([] : List C.Letter)) = 1 := by
    unfold P5.bTall
    have h1 : ∀ l, P5.bTl L l (D.positionted ([] : List C.Letter)) = 1 := fun l => rfl
    simp [h1]
  have hL : P5.act (P5.bTall L (D.positionted ([] : List C.Letter))) (Top.firstStateVector ΦG) (fun _ => 0) = ΦG := by
    rw [hb0]
    exact (congrFun (Formalism.FourierDecayAlt.P.PBF.polyAction_one₂ (Top.firstStateVector ΦG)) _).trans (if_pos rfl)
  exact (congrArg (fun Φ : Q.RadSp P.k P.r p.T.base.z p.T.base.z' p.T.base.π p.T.base.π' =>
    (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (D.castM (by omega) (ιLev P.k P.r (P.r - P.r) g))) hL).symm.trans key

end Formalism.FourierDecayAlt.P
end
end

section
noncomputable section

open Matrix MeasureTheory Filter Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutEX

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem isOpen_UT (k r : ℕ) (z z' : Fin (2 * (r - r) + k + 1) → ℂ) : IsOpen (UT k r z z') := by
  have h1 : Continuous fun q : (Fin r → Fin r → ℂ) × Mt k (r - r) => (Matrix.of q.1).det :=
    Continuous.matrix_det (continuous_fst)
  have h2 : Continuous fun q : (Fin r → Fin r → ℂ) × Mt k (r - r) =>
      Q.GGl k (r - r) z z' (Matrix.of q.2) :=
    (Formalism.FourierDecayAlt.P.Qx8.GGl_cont k (r - r) z z').comp continuous_snd
  exact (isOpen_ne_fun h1 continuous_const).inter (isOpen_lt continuous_const h2)

section asm

theorem omX_zero {r : ℕ} (c : Fin (r - r) → ℂ) : c ∈ OmX (r - r) := fun l => by
  exfalso; have := l.isLt; omega

theorem parFam_slice {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {k r : ℕ}
    {z z' : Fin (2 * (r - r) + k + 1) → ℂ} {f : (Fin r → Fin r → ℂ) × Mt k (r - r) → E}
    (hf : PBI.ParFam k (r - r) (UT k r z z') f) (Z : Fin r → Fin r → ℂ) (hZ : (Matrix.of Z).det ≠ 0) :
    ∀ g₀ : Q.Mx k (r - r), g₀ ∈ Q.Glev k (r - r) (Fin.last (r - r)) → 0 < Q.GGl k (r - r) z z' g₀ →
      ∃ (U : Set (Q.Mx k (r - r))) (F : Q.Mx k (r - r) → E), IsOpen U ∧ g₀ ∈ U ∧ ContDiffOn ℝ ∞ F U ∧
        ∀ g ∈ U, g ∈ Q.Glev k (r - r) (Fin.last (r - r)) → f (Z, Matrix.of.symm g) = F g := by
  intro g₀ hg₀ hG
  obtain ⟨U', F', hU', hq, hF', hag⟩ := hf (Z, Matrix.of.symm g₀) ⟨hZ, hG⟩ hg₀
  have hc : Continuous fun g : Q.Mx k (r - r) => ((Z, Matrix.of.symm g) : (Fin r → Fin r → ℂ) × Mt k (r - r)) :=
    continuous_const.prodMk continuous_id
  have hcd : ContDiff ℝ ∞ fun g : Q.Mx k (r - r) => ((Z, Matrix.of.symm g) : (Fin r → Fin r → ℂ) × Mt k (r - r)) :=
    contDiff_const.prodMk contDiff_id
  refine ⟨(fun g => ((Z, Matrix.of.symm g) : (Fin r → Fin r → ℂ) × Mt k (r - r))) ⁻¹' U', fun g => F' (Z, Matrix.of.symm g),
    hU'.preimage hc, hq, hF'.comp hcd.contDiffOn (fun g hg => hg), fun g hg hgG => hag _ hg hgG⟩

end asm

section closed

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem det_upUni {n : ℕ} {u : Matrix (Fin n) (Fin n) ℂ} (hu : Formalism.DoubleCosetMeasures.IsUpUni u) : u.det = 1 := by
  rw [Matrix.det_of_upperTriangular hu.1]
  simp [hu.2]

theorem isClosed_upUni (n : ℕ) : IsClosed {u : Matrix (Fin n) (Fin n) ℂ | Formalism.DoubleCosetMeasures.IsUpUni u} := by
  have h1 : IsClosed {u : Matrix (Fin n) (Fin n) ℂ | u.IsUpperTriangular} := by
    have : {u : Matrix (Fin n) (Fin n) ℂ | u.IsUpperTriangular} = ⋂ i, ⋂ j, ⋂ (_ : j < i), {u | u i j = 0} := by
      ext u; simp [Matrix.IsUpperTriangular, Matrix.BlockTriangular]
    rw [this]
    exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
      isClosed_eq ((continuous_apply j).comp (continuous_apply i)) continuous_const
  have h2 : IsClosed {u : Matrix (Fin n) (Fin n) ℂ | ∀ a, u a a = 1} := by
    have : {u : Matrix (Fin n) (Fin n) ℂ | ∀ a, u a a = 1} = ⋂ a, {u | u a a = 1} := by ext; simp
    rw [this]
    exact isClosed_iInter fun a => isClosed_eq ((continuous_apply a).comp (continuous_apply a)) continuous_const
  exact h1.inter h2

theorem isClosed_KU {n : ℕ} {Y : Type} [MetricSpace Y] {K : Set ((Fin n → Fin n → ℂ) × Y)} (hK : IsCompact K)
    (hKd : ∀ q ∈ K, (Matrix.of q.1).det ≠ 0) :
    IsClosed {q : (Fin n → Fin n → ℂ) × Y | ∃ u : Matrix (Fin n) (Fin n) ℂ, Formalism.DoubleCosetMeasures.IsUpUni u ∧
      (Matrix.of.symm (Matrix.of q.1 * u), q.2) ∈ K} := by
  refine isClosed_of_closure_subset fun q hq => ?_
  obtain ⟨s, hsK, hs⟩ := mem_closure_iff_seq_limit.1 hq
  choose u hu hus using hsK
  obtain ⟨W, hWK, φ, hφ, hlim⟩ := hK.tendsto_subseq hus

  have hdetc : Continuous fun q : (Fin n → Fin n → ℂ) × Y => (Matrix.of q.1).det :=
    Continuous.matrix_det continuous_fst
  have hd1 : Tendsto (fun m => (Matrix.of (s (φ m)).1).det) atTop (nhds (Matrix.of q.1).det) :=
    (hdetc.tendsto q).comp (hs.comp hφ.tendsto_atTop)
  have he : ∀ m, (Matrix.of (Matrix.of.symm (Matrix.of (s (φ m)).1 * u (φ m)), (s (φ m)).2).1).det =
      (Matrix.of (s (φ m)).1).det := by
    intro m; simp [Matrix.det_mul, det_upUni (hu (φ m))]
  have hd2 : Tendsto (fun m => (Matrix.of (s (φ m)).1).det) atTop (nhds (Matrix.of W.1).det) :=
    ((hdetc.tendsto W).comp hlim).congr (fun m => by simp only [Function.comp_apply]; exact he m)
  have hdq : (Matrix.of q.1).det = (Matrix.of W.1).det := tendsto_nhds_unique hd1 hd2
  have hqd : (Matrix.of q.1).det ≠ 0 := by rw [hdq]; exact hKd W hWK

  have hinv : Tendsto (fun m => (Matrix.of (s (φ m)).1)⁻¹) atTop (nhds (Matrix.of q.1)⁻¹) := by
    have hc : ContinuousAt (fun M : Matrix (Fin n) (Fin n) ℂ => M⁻¹) (Matrix.of q.1) :=
      continuousAt_matrix_inv _ (by simpa [Ring.inverse, isUnit_iff_ne_zero] using hqd)
    exact hc.tendsto.comp ((continuous_fst.tendsto q).comp (hs.comp hφ.tendsto_atTop))
  have hW1 : Tendsto (fun m => Matrix.of (s (φ m)).1 * u (φ m)) atTop (nhds (Matrix.of W.1)) :=
    ((continuous_fst.tendsto W).comp hlim).congr (fun m => rfl)
  have hu' : Tendsto (fun m => u (φ m)) atTop (nhds ((Matrix.of q.1)⁻¹ * Matrix.of W.1)) := by
    have := hinv.mul hW1
    refine this.congr' (Eventually.of_forall fun m => ?_)
    have hdm : (Matrix.of (s (φ m)).1).det ≠ 0 := by
      rw [← he m]; exact hKd _ (hus (φ m))
    simp only
    rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdm), Matrix.one_mul]
  have hUU : Formalism.DoubleCosetMeasures.IsUpUni ((Matrix.of q.1)⁻¹ * Matrix.of W.1) :=
    (isClosed_upUni n).mem_of_tendsto hu' (Eventually.of_forall fun m => hu (φ m))
  refine ⟨_, hUU, ?_⟩
  have hY : Tendsto (fun m => (s (φ m)).2) atTop (nhds W.2) :=
    ((continuous_snd.tendsto W).comp hlim).congr (fun m => rfl)
  have hY' : Tendsto (fun m => (s (φ m)).2) atTop (nhds q.2) :=
    (continuous_snd.tendsto q).comp (hs.comp hφ.tendsto_atTop)
  have hq2 : q.2 = W.2 := tendsto_nhds_unique hY' hY
  have e1 : Matrix.of q.1 * ((Matrix.of q.1)⁻¹ * Matrix.of W.1) = Matrix.of W.1 := by
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hqd), Matrix.one_mul]
  rw [e1, hq2]
  exact hWK

end closed

theorem exceptional_assumption_holds : Asm := by
  intro hUw hST hPS hPR hPSupp hPE hMk hMC hTP hZx hHF hRST hROF hRE hRT hFP hRW hPicS
  intro Wp Wq _ _ _ _ _ _ P p F w X μ L st Cb X₀ μ₀ L₀ st₀ hD hD₀ hTL hdd hF hcut e h hh
  classical
  have hr0 : P.r - P.r = 0 := by omega

  obtain ⟨F₁, hF₁, hloc, hsl, K₁, hK₁c, hK₁0, hK₁⟩ := exists_compact_cutoff_coefficient p F hF h hh
  have hT₁ : TopCls p.T.base F₁ := ⟨hF₁, K₁, hK₁c, hK₁0, fun g _ hne => hK₁ g hne⟩

  set u : Wd.Ix (Fin w.length) → B.Mat P.k P.r → (Wq →L[ℂ] Wp) :=
    fun e' => D.uwG P.k P.r p.T.base.z p.T.base.z' F₁ P.r le_rfl w e' with hu
  have hTu : ∀ e', TopCls p.T.base (u e') := fun e' => hUw Wp Wq P p F₁ hT₁ w e'

  have hAdm : Fr.admitted st (D.positionted w) :=
    admissible_of_range Wp Wq (JC.parLev P P.r) _ _ _ _ X μ L st p.l0 w p.hl.1 p.hl.2.1 hD hcut
  have hAdm₀ : Fr.admitted st₀ (D.positionted w) :=
    admissible_of_range Wp Wq P _ _ _ _ X₀ μ₀ L₀ st₀ p.l0 w p.hl.1 p.hl.2.1 hD₀ hcut

  set Ψf : (Fin P.r → Fin P.r → ℂ) → Wd.Ix (Fin w.length) → Mt P.k (P.r - P.r) → (Wq →L[ℂ] Wp) :=
    fun Z e' y => if (Z, y) ∈ UT P.k P.r (p.T.bs P.r).z (p.T.bs P.r).z' then
      pbTop p (u e') (Matrix.of Z) (Matrix.of y) else 0 with hΨfdef
  have hΨf_pos : ∀ Z e' y, (Z, y) ∈ UT P.k P.r (p.T.bs P.r).z (p.T.bs P.r).z' →
      Ψf Z e' y = pbTop p (u e') (Matrix.of Z) (Matrix.of y) := fun Z e' y hq => if_pos hq
  have hΨUT : ∀ e' (q : (Fin P.r → Fin P.r → ℂ) × Mt P.k (P.r - P.r)),
      q ∉ UT P.k P.r (p.T.bs P.r).z (p.T.bs P.r).z' → Ψf q.1 e' q.2 = 0 := fun e' q hq => if_neg hq
  have hΨsm : ∀ e', PBI.ParFam P.k (P.r - P.r) (UT P.k P.r (p.T.bs P.r).z (p.T.bs P.r).z')
      (fun q => Ψf q.1 e' q.2) := by
    intro e' q₀ hq₀ hq₀G
    obtain ⟨U, Fe, hU, hq₀U, hFe, hag⟩ := hPS Wp Wq P p (u e') (hTu e') q₀ hq₀ hq₀G
    exact ⟨U ∩ UT P.k P.r (p.T.bs P.r).z (p.T.bs P.r).z', Fe, hU.inter (isOpen_UT _ _ _ _), ⟨hq₀U, hq₀⟩,
      hFe.mono Set.inter_subset_left, fun q hq hqG => (hΨf_pos q.1 e' q.2 hq.2).trans (hag q hq.1 hqG)⟩
  have hΨsupp : ∀ e', ∃ K : Set ((Fin P.r → Fin P.r → ℂ) × Mt P.k (P.r - P.r)), IsCompact K ∧
      K ⊆ UT P.k P.r (p.T.bs P.r).z (p.T.bs P.r).z' ∧
      ∀ q : (Fin P.r → Fin P.r → ℂ) × Mt P.k (P.r - P.r), Matrix.of q.2 ∈ Q.Glev P.k (P.r - P.r) (Fin.last _) →
        Ψf q.1 e' q.2 ≠ 0 →
        ∃ v : Matrix (Fin P.r) (Fin P.r) ℂ, Formalism.DoubleCosetMeasures.IsUpUni v ∧ (Matrix.of.symm (Matrix.of q.1 * v), q.2) ∈ K :=
    by
    intro e'
    obtain ⟨K, hKc, hKU, hK⟩ := hPSupp Wp Wq P p (u e') (hTu e')
    refine ⟨K, hKc, hKU, fun q hqG hne => ?_⟩
    by_cases hq : q ∈ UT P.k P.r (p.T.bs P.r).z (p.T.bs P.r).z'
    · rw [hΨf_pos q.1 e' q.2 hq] at hne
      exact hK q hq.1 hqG hne
    · exact absurd (hΨUT e' q hq) hne
  choose Ku hKuc hKuU hKu using hΨsupp
  have hΨex : ∀ (Z : Fin P.r → Fin P.r → ℂ) (e' : Wd.Ix (Fin w.length)),
      ∃ Ψ : Q.RadSp (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z' (p.T.bs P.r).π
          (p.T.bs P.r).π',
        ∀ c y, Matrix.of y ∈ Q.Glev P.k (P.r - P.r) (Fin.last _) →
          (Ψ : Q.Fn (JC.parLev P P.r).k (JC.parLev P P.r).r (Wq →L[ℂ] Wp)) c (Matrix.of y) = Ψf Z e' y := by
    intro Z e'
    by_cases hZ : (Matrix.of Z).det ≠ 0
    · obtain ⟨Ψ, hΨ⟩ := hROF Wp Wq P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (p.T.bs P.r).π (p.T.bs P.r).π'
        (fun g => pbTop p (u e') (Matrix.of Z) g) (parFam_slice (hPS Wp Wq P p (u e') (hTu e')) Z hZ)
        (fun g hg hG h₁ hh₁ h₂ hh₂ => hPE Wp Wq P p (u e') (hTu e') (Matrix.of Z) hZ g hg h₁ hh₁ h₂ hh₂)
      refine ⟨Ψ, fun c y hy => ?_⟩
      by_cases hG : 0 < Q.GGl P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (Matrix.of y)
      · exact (hΨ (c, Matrix.of y) ⟨omX_zero c, hy, hG⟩).trans (hΨf_pos Z e' y ⟨hZ, hG⟩).symm
      · exact (Ψ.2.1 (c, Matrix.of y) (fun hx => hG hx.2.2)).trans
          (hΨUT e' (Z, y) (fun hq => hG hq.2)).symm
    · refine ⟨0, fun c y hy => ?_⟩
      show (0 : Wq →L[ℂ] Wp) = _
      symm
      exact hΨUT e' (Z, y) (fun hq => hZ hq.1)
  choose Ψ hΨ using hΨex

  obtain ⟨Φf, hΦval, hΦsm, hΦsupp, hΦswap⟩ := hFP Wp Wq P p X μ L st hD w hAdm (Fin P.r → Fin P.r → ℂ)
    (UT P.k P.r (p.T.bs P.r).z (p.T.bs P.r).z') (isOpen_UT _ _ _ _) (fun q hq => ⟨trivial, hq.2⟩) Ψ Ψf
    (fun Z e' c y hy => hΨ Z e' c y hy) hΨsm
  set K : Set ((Fin P.r → Fin P.r → ℂ) × Mt P.k (P.r - P.r)) := ⋃ e', Ku e' with hKdef
  have hKc : IsCompact K := isCompact_iUnion hKuc
  have hKU : K ⊆ UT P.k P.r (p.T.bs P.r).z (p.T.bs P.r).z' := Set.iUnion_subset hKuU
  set K'' : Set ((Fin P.r → Fin P.r → ℂ) × Mt P.k (P.r - P.r)) :=
    {q | ∃ v : Matrix (Fin P.r) (Fin P.r) ℂ, Formalism.DoubleCosetMeasures.IsUpUni v ∧ (Matrix.of.symm (Matrix.of q.1 * v), q.2) ∈ K}
    with hK''def
  have hK''cl : closure K'' = K'' := (isClosed_KU hKc (fun q hq => (hKU hq).1)).closure_eq
  have hΦ0 : ∀ q, q ∈ UT P.k P.r (p.T.bs P.r).z (p.T.bs P.r).z' →
      Matrix.of q.2 ∈ Q.Glev P.k (P.r - P.r) (Fin.last _) → q ∉ K'' → Φf q.1 e q.2 = 0 := by
    intro q hq hqG hqK
    refine hΦsupp K'' (fun e' q' hq' hnot => ?_) e q hq hqG ?_
    · by_contra hne
      obtain ⟨v, hv, hvK⟩ := hKu e' q' hq' hne
      exact hnot ⟨v, hv, Set.mem_iUnion.2 ⟨e', hvK⟩⟩
    · rw [hK''cl]; exact hqK

  have hΨR : ∀ (Z : Fin P.r → Fin P.r → ℂ) (v : Matrix (Fin P.r) (Fin P.r) ℂ), Formalism.DoubleCosetMeasures.IsUpUni v → ∀ e',
      Ψ (Matrix.of.symm (Matrix.of Z * v)) e' = psiU p v • Ψ Z e' := by
    intro Z v hv e'
    refine hRE Wp Wq P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (p.T.bs P.r).π (p.T.bs P.r).π' _ _ fun x hx => ?_
    show (Ψ (Matrix.of.symm (Matrix.of Z * v)) e' : Q.Fn (JC.parLev P P.r).k (JC.parLev P P.r).r (Wq →L[ℂ] Wp)) x.1 x.2 =
      psiU p v • (Ψ Z e' : Q.Fn (JC.parLev P P.r).k (JC.parLev P P.r).r (Wq →L[ℂ] Wp)) x.1 x.2
    have h1 := hΨ (Matrix.of.symm (Matrix.of Z * v)) e' x.1 (Matrix.of.symm x.2) hx.2.1
    have h2 := hΨ Z e' x.1 (Matrix.of.symm x.2) hx.2.1
    refine h1.trans ?_
    refine Eq.trans ?_ (congrArg (fun X => psiU p v • X) h2.symm)
    have hd : (Matrix.of (Matrix.of.symm (Matrix.of Z * v))).det = (Matrix.of Z).det := by
      simp [Matrix.det_mul, det_upUni hv]
    by_cases hq : (Z, Matrix.of.symm x.2) ∈ UT P.k P.r (p.T.bs P.r).z (p.T.bs P.r).z'
    · have hq' : (Matrix.of.symm (Matrix.of Z * v), Matrix.of.symm x.2) ∈ UT P.k P.r (p.T.bs P.r).z (p.T.bs P.r).z' :=
        ⟨hd ▸ hq.1, hq.2⟩
      rw [hΨf_pos _ e' _ hq', hΨf_pos _ e' _ hq]
      exact hPR Wp Wq P p (u e') (hTu e') (Matrix.of Z) v x.2 hv
    · have hq' : (Matrix.of.symm (Matrix.of Z * v), Matrix.of.symm x.2) ∉ UT P.k P.r (p.T.bs P.r).z (p.T.bs P.r).z' :=
        fun h' => hq ⟨hd ▸ h'.1, h'.2⟩
      rw [hΨUT e' (_, _) hq', hΨUT e' (_, _) hq, smul_zero]
  have hΦR : ∀ (Z : Fin P.r → Fin P.r → ℂ) (y : Mt P.k (P.r - P.r)) (v : Matrix (Fin P.r) (Fin P.r) ℂ),
      Matrix.of y ∈ Q.Glev P.k (P.r - P.r) (Fin.last _) → Formalism.DoubleCosetMeasures.IsUpUni v →
      Φf (Matrix.of.symm (Matrix.of Z * v)) e y = psiU p v • Φf Z e y := by
    intro Z y v hy hv
    rw [← hΦval _ e (fun _ => 0) y hy, ← hΦval Z e (fun _ => 0) y hy]
    have : Ψ (Matrix.of.symm (Matrix.of Z * v)) = fun e' => psiU p v • Ψ Z e' := funext (hΨR Z v hv)
    rw [this]
    erw [Formalism.FourierDecayAlt.P.PBP.act_smul']
    rfl

  obtain ⟨b, b', β, κ, hb, hbc, hb', hb'c, hκ, hβ, hK', hmk⟩ := hMk Wp Wq P p
  obtain ⟨K', hK'c, hK'U, hK'mem⟩ := hK' K hKc hKU
  classical
  set Φ₀ : (Fin P.r → Fin P.r → ℂ) → Mt P.k (P.r - P.r) → (Wq →L[ℂ] Wp) :=
    fun Z y => if (Z, y) ∈ UT P.k P.r (p.T.bs P.r).z (p.T.bs P.r).z' then κ⁻¹ • Φf Z e y else 0 with hΦ₀def
  set Φβ : (Fin P.r → Fin P.r → ℂ) → Mt P.k (P.r - P.r) → (Wq →L[ℂ] Wp) :=
    fun Z' y' => ((β Z' : ℝ) : ℂ) • Φ₀ Z' y' with hΦβdef
  have hΦβsm : PBI.ParFam P.k (P.r - P.r) (UT P.k P.r (p.T.bs P.r).z (p.T.bs P.r).z') (fun q => Φβ q.1 q.2) := by
    intro q₀ hq₀ hq₀G
    obtain ⟨U, Fe, hU, hq₀U, hFe, hag⟩ := hΦsm e q₀ hq₀ hq₀G
    have hβq : ContDiffOn ℝ ∞ (fun q : (Fin P.r → Fin P.r → ℂ) × Mt P.k (P.r - P.r) => β q.1)
        (UT P.k P.r (p.T.bs P.r).z (p.T.bs P.r).z') :=
      hβ.comp contDiff_fst.contDiffOn (fun q hq => hq.1)
    refine ⟨U ∩ UT P.k P.r (p.T.bs P.r).z (p.T.bs P.r).z', fun q => β q.1 • κ⁻¹ • Fe q, hU.inter (isOpen_UT _ _ _ _),
      ⟨hq₀U, hq₀⟩, ?_, fun q hq hqG => ?_⟩
    · exact (hβq.mono Set.inter_subset_right).smul ((hFe.const_smul κ⁻¹).mono Set.inter_subset_left)
    · show ((β q.1 : ℝ) : ℂ) • (if (q.1, q.2) ∈ UT P.k P.r (p.T.bs P.r).z (p.T.bs P.r).z' then
          κ⁻¹ • Φf q.1 e q.2 else 0) = β q.1 • κ⁻¹ • Fe q
      rw [if_pos hq.2, Complex.coe_smul]
      rw [show Φf q.1 e q.2 = Fe q from hag q hq.1 hqG]
  have hΦβK : ∀ q, Matrix.of q.2 ∈ Q.Glev P.k (P.r - P.r) (Fin.last _) → q ∉ K' → Φβ q.1 q.2 = 0 := by
    intro q hqG hqK
    show ((β q.1 : ℝ) : ℂ) • (if (q.1, q.2) ∈ UT P.k P.r (p.T.bs P.r).z (p.T.bs P.r).z' then
        κ⁻¹ • Φf q.1 e q.2 else 0) = 0
    by_cases hβ0 : β q.1 = 0
    · rw [hβ0]; simp
    split_ifs with hq
    · have hqK'' : q ∉ K'' := fun h' => hqK (hK'mem q hq.1 hβ0 h')
      rw [hΦ0 q hq hqG hqK'', smul_zero, smul_zero]
    · rw [smul_zero]
  set F₂ := F2 b b' Φβ with hF₂def
  have hT₂ : TopCls p.T.base F₂ := hMC Wp Wq P p b b' hb hbc hb' hb'c Φβ hΦβsm K' hK'c hK'U hΦβK

  have hE₀ : ∀ (Z : Fin P.r → Fin P.r → ℂ) (y : Mt P.k (P.r - P.r)),
      Matrix.of y ∈ Q.Glev P.k (P.r - P.r) (Fin.last _) → ∀ h₁ ∈ UWset P.k (P.r - P.r) (p.T.bs P.r).z,
      ∀ h₂ ∈ UWset P.k (P.r - P.r) (p.T.bs P.r).z',
        Φ₀ Z (Matrix.of.symm (h₁ * Matrix.of y * h₂)) = ((p.T.bs P.r).π h₁).comp ((Φ₀ Z y).comp ((p.T.bs P.r).π' h₂)) := by
    intro Z y hy h₁ hh₁ h₂ hh₂
    have hGG : Q.GGl P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (h₁ * Matrix.of y * h₂) =
        Q.GGl P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (Matrix.of y) := Formalism.FourierDecayAlt.P5.Rad.GGl_uw hh₁ hh₂ _
    have hy' : h₁ * Matrix.of y * h₂ ∈ Q.Glev P.k (P.r - P.r) (Fin.last _) :=
      Formalism.FourierDecayAlt.P.Qx8.glev_mul (Formalism.FourierDecayAlt.P.Qx8.glev_mul (Formalism.FourierDecayAlt.P.Qx8.uw_glev _ hh₁) hy)
        (Formalism.FourierDecayAlt.P.Qx8.uw_glev _ hh₂)
    have hiff : (Z, Matrix.of.symm (h₁ * Matrix.of y * h₂)) ∈ UT P.k P.r (p.T.bs P.r).z (p.T.bs P.r).z' ↔
        (Z, y) ∈ UT P.k P.r (p.T.bs P.r).z (p.T.bs P.r).z' := by
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨h1, ?_⟩
        change 0 < Q.GGl P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (h₁ * Matrix.of y * h₂) at h2
        rw [hGG] at h2; exact h2
      · rintro ⟨h1, h2⟩
        refine ⟨h1, ?_⟩
        show 0 < Q.GGl P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (h₁ * Matrix.of y * h₂)
        rw [hGG]; exact h2
    show (if (Z, Matrix.of.symm (h₁ * Matrix.of y * h₂)) ∈ UT P.k P.r (p.T.bs P.r).z (p.T.bs P.r).z' then
        κ⁻¹ • Φf Z e (Matrix.of.symm (h₁ * Matrix.of y * h₂)) else 0) =
      ((p.T.bs P.r).π h₁).comp ((if (Z, y) ∈ UT P.k P.r (p.T.bs P.r).z (p.T.bs P.r).z' then κ⁻¹ • Φf Z e y else 0).comp
        ((p.T.bs P.r).π' h₂))
    by_cases hq : (Z, y) ∈ UT P.k P.r (p.T.bs P.r).z (p.T.bs P.r).z'
    · rw [if_pos (hiff.2 hq), if_pos hq]
      have e1 := hΦval Z e (fun _ => 0) (Matrix.of.symm (h₁ * Matrix.of y * h₂)) hy'
      have e2 := hΦval Z e (fun _ => 0) y hy
      have hx : ((fun _ => 0, Matrix.of y) : (Fin (JC.parLev P P.r).r → ℂ) × Q.Mx P.k (P.r - P.r)) ∈
          Q.DomR (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z' := ⟨omX_zero _, hy, hq.2⟩
      have e3 := (P5.act (Fr.ofWord L st (D.positionted w)).F (Ψ Z) e).2.2.2 _ hx h₁ hh₁ h₂ hh₂
      rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, ← e1, ← e2]
      exact congrArg (fun X => κ⁻¹ • X) e3
    · rw [if_neg (fun h' => hq (hiff.1 h')), if_neg hq]
      simp
  have hR₀ : ∀ (Z : Fin P.r → Fin P.r → ℂ) (y : Mt P.k (P.r - P.r)) (v : Matrix (Fin P.r) (Fin P.r) ℂ),
      (Matrix.of Z).det ≠ 0 → Matrix.of y ∈ Q.Glev P.k (P.r - P.r) (Fin.last _) → Formalism.DoubleCosetMeasures.IsUpUni v →
      Φ₀ (Matrix.of.symm (Matrix.of Z * v)) y = psiU p v • Φ₀ Z y := by
    intro Z y v hZ hy hv
    have hiff : (Matrix.of.symm (Matrix.of Z * v), y) ∈ UT P.k P.r (p.T.bs P.r).z (p.T.bs P.r).z' ↔
        (Z, y) ∈ UT P.k P.r (p.T.bs P.r).z (p.T.bs P.r).z' := by
      have hd : (Matrix.of (Matrix.of.symm (Matrix.of Z * v))).det = (Matrix.of Z).det := by
        simp [Matrix.det_mul, det_upUni hv]
      exact ⟨fun h' => ⟨hd ▸ h'.1, h'.2⟩, fun h' => ⟨hd.symm ▸ h'.1, h'.2⟩⟩
    show (if (Matrix.of.symm (Matrix.of Z * v), y) ∈ UT P.k P.r (p.T.bs P.r).z (p.T.bs P.r).z' then
        κ⁻¹ • Φf (Matrix.of.symm (Matrix.of Z * v)) e y else 0) =
      psiU p v • (if (Z, y) ∈ UT P.k P.r (p.T.bs P.r).z (p.T.bs P.r).z' then κ⁻¹ • Φf Z e y else 0)
    by_cases hq : (Z, y) ∈ UT P.k P.r (p.T.bs P.r).z (p.T.bs P.r).z'
    · rw [if_pos (hiff.2 hq), if_pos hq, hΦR Z y v hy hv, smul_comm]
    · rw [if_neg (fun h' => hq (hiff.1 h')), if_neg hq, smul_zero]
  have hmkΦ : ∀ (Z : Fin P.r → Fin P.r → ℂ) (y : Mt P.k (P.r - P.r)), (Matrix.of Z).det ≠ 0 →
      Matrix.of y ∈ Q.Glev P.k (P.r - P.r) (Fin.last _) →
      pbTop p F₂ (Matrix.of Z) (Matrix.of y) = κ • Φ₀ Z y :=
    fun Z y hZ hy => hmk Φ₀ hE₀ hR₀ Z y hZ hy
  have hF₂val : ∀ (Z : Fin P.r → Fin P.r → ℂ) (y : Mt P.k (P.r - P.r)),
      (Z, y) ∈ UT P.k P.r (p.T.bs P.r).z (p.T.bs P.r).z' → Matrix.of y ∈ Q.Glev P.k (P.r - P.r) (Fin.last _) →
      pbTop p F₂ (Matrix.of Z) (Matrix.of y) = Φf Z e y := by
    intro Z y hq hy
    rw [hmkΦ Z y hq.1 hy]
    show κ • (if (Z, y) ∈ UT P.k P.r (p.T.bs P.r).z (p.T.bs P.r).z' then κ⁻¹ • Φf Z e y else 0) = _
    rw [if_pos hq, smul_smul, mul_inv_cancel₀ hκ, one_smul]

  have hVopen : IsOpen {y : Mt P.k (P.r - P.r) | 0 < Q.GGl P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (Matrix.of y)} :=
    isOpen_lt continuous_const ((Formalism.FourierDecayAlt.P.Qx8.GGl_cont _ _ _ _).comp continuous_id)
  have hkey : ∀ (h' : C.LPt) (hh' : D.IsLocPt h' P.r)
      (Ψh : Wd.Ix (Fin w.length) → Q.RadSp (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z'
        (p.T.bs P.r).π (p.T.bs P.r).π'),
      (∀ e', Top.IsRadOf (JC.parLev P P.r) (p.T.bs P.r) (Ψh e')
        (D.castF (by rw [hh'.2]; rfl) (D.sliceAt P.k P.r p.T.base.z p.T.base.z' (u e') h'))) →
      ∀ (c : Fin (JC.parLev P P.r).r → ℂ) (γ : B.Mat P.k (P.r - P.r)), γ ∈ B.GV P.k (P.r - P.r) →
        0 < Q.GGl P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' γ →
        B.JF (p.T.bs P.r) (D.castF (by rw [hh'.2]) (D.sliceAt P.k P.r p.T.base.z p.T.base.z' F₂ h')) γ =
          (P5.act (Fr.ofWord L st (D.positionted w)).F Ψh e :
            Q.Fn (JC.parLev P P.r).k (JC.parLev P P.r).r (Wq →L[ℂ] Wp)) c γ := by
    intro h' hh' Ψh hΨh c γ hγG hγGG
    have hγL : γ ∈ Q.Glev P.k (P.r - P.r) (Fin.last _) := ((hTP Wp Wq P p).2 γ).1 hγG

    have hHFe : ∀ e', PBI.ParFam P.k (P.r - P.r)
          (Set.univ ×ˢ {y | 0 < Q.GGl P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (Matrix.of y)})
          (fun q : PBQ.XH h' × Mt P.k (P.r - P.r) => PBQ.ellH h' q.1 (Ψf (PBQ.zxH h' P.r hh'.2 q.1) e' q.2)) ∧
        ∃ Kp : Set (PBQ.XH h'), IsCompact Kp ∧ ∀ v ∉ Kp, ∀ y : Mt P.k (P.r - P.r),
          Matrix.of y ∈ Q.Glev P.k (P.r - P.r) (Fin.last _) → Ψf (PBQ.zxH h' P.r hh'.2 v) e' y = 0 :=
      fun e' => hHF Wp Wq P p h' hh' (fun q => Ψf q.1 e' q.2) (hΨsm e') (Ku e') (hKuc e') (hKuU e') (hKu e')
    choose hsm2 Kpe hKpec hKpev using hHFe
    set Kp : Set (PBQ.XH h') := ⋃ e', Kpe e' with hKpdef
    have hKpc : IsCompact Kp := isCompact_iUnion hKpec
    have hKpv : ∀ e', ∀ v ∉ Kp, ∀ y : Mt P.k (P.r - P.r),
        Matrix.of y ∈ Q.Glev P.k (P.r - P.r) (Fin.last _) → Ψf (PBQ.zxH h' P.r hh'.2 v) e' y = 0 :=
      fun e' v hv y hy => hKpev e' v (fun h'' => hv (Set.mem_iUnion.2 ⟨e', h''⟩)) y hy

    set a : PBQ.XH h' → ℂ := fun v => G.psi U.betaU (U.subS (LeftFubiniLemmas.lhOf (D.ptPerm h') v)) with hadef
    have hell : ∀ v (X : Wq →L[ℂ] Wp), PBQ.ellH h' v X = a v • X := fun v X => rfl
    set Ψ' : PBQ.XH h' → Wd.Ix (Fin w.length) → Q.RadSp (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z
        (p.T.bs P.r).z' (p.T.bs P.r).π (p.T.bs P.r).π' := fun v e' => a v • Ψ (PBQ.zxH h' P.r hh'.2 v) e' with hΨ'def
    set Ψ'f : PBQ.XH h' → Wd.Ix (Fin w.length) → Mt P.k (P.r - P.r) → (Wq →L[ℂ] Wp) :=
      fun v e' y => PBQ.ellH h' v (Ψf (PBQ.zxH h' P.r hh'.2 v) e' y) with hΨ'fdef
    have hval' : ∀ v e' c' y, Matrix.of y ∈ Q.Glev P.k (P.r - P.r) (Fin.last _) →
        (Ψ' v e' : Q.Fn (JC.parLev P P.r).k (JC.parLev P P.r).r (Wq →L[ℂ] Wp)) c' (Matrix.of y) = Ψ'f v e' y := by
      intro v e' c' y hy
      show a v • (Ψ (PBQ.zxH h' P.r hh'.2 v) e' : Q.Fn (JC.parLev P P.r).k (JC.parLev P P.r).r (Wq →L[ℂ] Wp)) c'
        (Matrix.of y) = PBQ.ellH h' v (Ψf (PBQ.zxH h' P.r hh'.2 v) e' y)
      rw [hell]
      exact congrArg (fun X => a v • X) (hΨ _ e' c' y hy)
    obtain ⟨Φf', hΦval', hΦsm', hΦsupp', hΦswap'⟩ := hFP Wp Wq P p X μ L st hD w hAdm (PBQ.XH h')
      (Set.univ ×ˢ {y | 0 < Q.GGl P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (Matrix.of y)})
      (isOpen_univ.prod hVopen) le_rfl Ψ' Ψ'f hval' hsm2

    have h5 : ∀ v y, Matrix.of y ∈ Q.Glev P.k (P.r - P.r) (Fin.last _) →
        Φf' v e y = PBQ.ellH h' v (Φf (PBQ.zxH h' P.r hh'.2 v) e y) := by
      intro v y hy
      rw [← hΦval' v e (fun _ => 0) y hy, ← hΦval (PBQ.zxH h' P.r hh'.2 v) e (fun _ => 0) y hy, hell]
      show (P5.act (Fr.ofWord L st (D.positionted w)).F (fun e' => a v • Ψ (PBQ.zxH h' P.r hh'.2 v) e') e :
        Q.Fn (JC.parLev P P.r).k (JC.parLev P P.r).r (Wq →L[ℂ] Wp)) (fun _ => 0) (Matrix.of y) = _
      erw [Formalism.FourierDecayAlt.P.PBP.act_smul']
      rfl

    have h6 : ∀ v y, v ∉ Kp → Matrix.of y ∈ Q.Glev P.k (P.r - P.r) (Fin.last _) →
        0 < Q.GGl P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (Matrix.of y) → Φf' v e y = 0 := by
      intro v y hv hy hG
      refine hΦsupp' (Kp ×ˢ Set.univ) (fun e' q hqG hq => ?_) e (v, y) ⟨trivial, hG⟩ hy ?_
      · have hq1 : q.1 ∉ Kp := fun h'' => hq ⟨h'', trivial⟩
        show PBQ.ellH h' q.1 (Ψf (PBQ.zxH h' P.r hh'.2 q.1) e' q.2) = 0
        rw [hKpv e' q.1 hq1 q.2 hqG, map_zero]
      · rw [(hKpc.isClosed.prod isClosed_univ).closure_eq]
        exact fun h'' => hv h''.1

    haveI : IsFiniteMeasure ((volume : Measure (PBQ.XH h')).restrict Kp) :=
      isFiniteMeasure_restrict.mpr hKpc.measure_lt_top.ne
    have hνc : ((volume : Measure (PBQ.XH h')).restrict Kp) Kpᶜ = 0 := by
      rw [Measure.restrict_apply hKpc.isClosed.measurableSet.compl]; simp

    have hsw := hΦswap' ((volume : Measure (PBQ.XH h')).restrict Kp) Kp hKpc hνc Ψh (Matrix.of.symm γ)
      {y | 0 < Q.GGl P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (Matrix.of y)} hVopen hγGG hγL
      (fun q hq => ⟨trivial, hq.2⟩) (fun e' c' y' hy' hy'G => ?_) e c
    · obtain ⟨-, hJ⟩ := hST Wp Wq P p F₂ hT₂ h' hh' γ hγG hγGG
      rw [hJ]
      have hpt : ∀ v, PBQ.ellH h' v (pbTop p F₂ (PBQ.zxH h' P.r hh'.2 v) γ) = Φf' v e (Matrix.of.symm γ) := by
        intro v
        rw [h5 v (Matrix.of.symm γ) hγL]
        congr 1
        exact hF₂val (PBQ.zxH h' P.r hh'.2 v) (Matrix.of.symm γ) ⟨hZx P.r h' hh' v, hγGG⟩ hγL
      rw [integral_congr_ae (Eventually.of_forall hpt),
        ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Kp) (fun v hv => h6 v (Matrix.of.symm γ) hv hγL hγGG)]
      exact hsw.symm
    · have hx : ((c', Matrix.of y') : (Fin (JC.parLev P P.r).r → ℂ) × Q.Mx P.k (P.r - P.r)) ∈
          Q.DomR (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z' := ⟨omX_zero c', hy'G, hy'⟩
      have hGV : Matrix.of y' ∈ B.GV P.k (P.r - P.r) := ((hTP Wp Wq P p).2 (Matrix.of y')).2 hy'G
      obtain ⟨-, hJu⟩ := hST Wp Wq P p (u e') (hTu e') h' hh' (Matrix.of y') hGV hy'
      refine (hΨh e' _ hx).trans ?_
      refine (hRT _ (JC.parLev P P.r).k (JC.parLev P P.r).r hr0 _ _ _).trans ?_
      refine hJu.trans ?_
      have hcong : ∀ v, PBQ.ellH h' v (pbTop p (u e') (PBQ.zxH h' P.r hh'.2 v) (Matrix.of y')) = Ψ'f v e' y' :=
        fun v => (congrArg (PBQ.ellH h' v) (hΨf_pos (PBQ.zxH h' P.r hh'.2 v) e' y' ⟨hZx P.r h' hh' v, hy'⟩)).symm
      rw [integral_congr_ae (Eventually.of_forall hcong)]
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Kp) (fun v hv => by
        show PBQ.ellH h' v (Ψf (PBQ.zxH h' P.r hh'.2 v) e' y') = 0
        rw [hKpv e' v hv y' hy'G, map_zero])]

  obtain ⟨Φ₂, hΦ₂⟩ := Formalism.FourierDecayAlt.P.PBN.radExists p hT₂.1
  refine ⟨F₁, F₂, hF₁, hT₂.1, fun ζ => hloc w hcut e Cb hdd ζ, ?_, ?_⟩
  ·
    intro Φ₁ hΦ₁ x hx
    rw [← hΦ₂ x hx]
    obtain ⟨g, hgL, hgGG, hxg⟩ := (hTP Wp Wq P p).1 x hx
    have hc : x.1 ∈ OmX P.r := hx.1
    have hgGV : g ∈ B.GV P.k (P.r - P.r) := ((hTP Wp Wq P p).2 g).2 hgL
    have hhc : D.IsLocPt (PBI.hcell x.1) P.r := by
      refine ⟨fun bl hbl => ?_, PBI.ptSize_hcell x.1⟩
      obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hbl
      exact ⟨le_rfl, hc j⟩
    have hRSTc : ∀ e', ∃ Ψc : Q.RadSp (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z'
        (p.T.bs P.r).π (p.T.bs P.r).π', Top.IsRadOf (JC.parLev P P.r) (p.T.bs P.r) Ψc
          (D.castF (by rw [hhc.2]; rfl) (D.sliceAt P.k P.r p.T.base.z p.T.base.z' (u e') (PBI.hcell x.1))) :=
      fun e' => hRST Wp Wq P p (u e') (hTu e') (PBI.hcell x.1) hhc
    choose Ψc hΨc using hRSTc
    set W : ℂ := ((∏ j : Fin P.r, ‖x.1 j‖ ^ (2 * (P.r - (j : ℕ)) + P.k) : ℝ) : ℂ) with hW

    have hR : (Φ₂ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 =
        W • (P5.act (Fr.ofWord L st (D.positionted w)).F Ψc e :
          Q.Fn (JC.parLev P P.r).k (JC.parLev P P.r).r (Wq →L[ℂ] Wp)) (fun _ => 0) g := by
      rw [hxg, hPicS Wp Wq P p F₂ hT₂.1 Φ₂ hΦ₂ x.1 hc g hgL hgGG]
      exact congrArg (fun X => W • X) (hkey (PBI.hcell x.1) hhc Ψc hΨc (fun _ => 0) g hgGV hgGG)
    rw [hR]

    obtain ⟨T, hT, hFT⟩ := Formalism.FourierDecayAlt.P.frame_transport_to_last_level Wp Wq P p X₀ μ₀ L₀ st₀ X μ L st hD₀ hD x.1 hc
    have hTb : ∀ e', T (P5.act (P5.bTall L₀ (D.positionted w)) (Top.firstStateVector Φ₁) e') = W • Ψc e' := by
      intro e'
      refine hRE Wp Wq P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (p.T.bs P.r).π (p.T.bs P.r).π' _ _ fun y hy => ?_
      show (T (P5.act (P5.bTall L₀ (D.positionted w)) (Top.firstStateVector Φ₁) e') :
          Q.Fn (JC.parLev P P.r).k (JC.parLev P P.r).r (Wq →L[ℂ] Wp)) y.1 y.2 =
        W • (Ψc e' : Q.Fn (JC.parLev P P.r).k (JC.parLev P P.r).r (Wq →L[ℂ] Wp)) y.1 y.2
      refine (hT _ y.1 y.2).trans ?_
      refine (hRW Wp Wq P p X₀ μ₀ L₀ st₀ hD₀ F₁ hF₁ w hcut Φ₁ hΦ₁ e' x.1 hc y.2 hy.2.1 hy.2.2).trans ?_
      refine congrArg (fun X => W • X) ?_
      refine Eq.symm ((hΨc e' y hy).trans ?_)
      exact hRT _ (JC.parLev P P.r).k (JC.parLev P P.r).r hr0 _ _ _
    rw [hxg]
    have hmul := Formalism.FourierDecayAlt.P.Topx1.act_mul ((Fr.ofWord L₀ st₀ (D.positionted w)).F) (P5.bTall L₀ (D.positionted w))
      (Top.firstStateVector Φ₁)
    rw [hmul, hFT w hAdm₀ hAdm _ e (fun _ => 0) g hgL hgGG]
    have : (fun e' => T (P5.act (P5.bTall L₀ (D.positionted w)) (Top.firstStateVector Φ₁) e')) = fun e' => W • Ψc e' :=
      funext hTb
    rw [this]
    erw [Formalism.FourierDecayAlt.P.PBP.act_smul']
    rfl
  ·
    intro Φ hΦ c γ hγG hγGG
    refine hkey h hh Φ (fun e' => ?_) c γ hγG hγGG
    have h1 := hΦ e'
    rw [hsl w e'] at h1
    exact h1

end Formalism.FourierDecayAlt.P.CutEX
end
end
