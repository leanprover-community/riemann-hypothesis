import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.WordFrameBounds.Lt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatchingWordOf
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.WordFrameBounds.PLocWord
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.PFrameOk
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.MatchAll

section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

open PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcN.F2

namespace PositivityTheory.Rg.BcB.F.B3

attribute [local instance] borelG borelF borelA GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

namespace PWordId2

section Frame

variable {hR : Rd.ReadLimit} {π : Submodule ℂ (UA E n → ℂ)} {S T : Finset (Pl E)} {F₀ : Frame0 hR π S} (F : RunFrame F₀ T)
omit [IsCMField E] in
theorem wa_v_one {w : Pl E} (u : (w.adicCompletion E)ˣ)
    (h : ordL (u : w.adicCompletion E) = 0) : Valued.v (u : w.adicCompletion E) = 1 := by
  have h0 : Valued.v (u : w.adicCompletion E) ≠ 0 := (Valuation.ne_zero_iff _).2 u.ne_zero
  unfold ordL at h
  rw [dif_neg h0, neg_eq_zero] at h
  have h1 : WithZero.unzero h0 = 1 := by simpa using congrArg Multiplicative.ofAdd h
  rw [← WithZero.coe_unzero h0, h1]
  rfl

theorem wa_mu_loc (w : Pl E) : F.d.μ w = F₀.μ.loc w := by
  rw [F.same.2.2.1]; exact F₀.μloc w

theorem wa_mu_unit (w : Pl E) (u : (w.adicCompletion E)ˣ) : ‖((F.d.μ w u : ℂˣ) : ℂ)‖ = 1 := by
  rw [wa_mu_loc]; exact F₀.hμ.1 _

theorem wa_good (w : Pl E) (hw : w ∈ F₀.Sec) (hB : w ∉ F.d.B) (hs : IsSplitAt w) : F.d.Good w := by
  simp only [LocData.B, Finset.mem_union, not_or] at hB
  obtain ⟨⟨hT, hS0⟩, hBad⟩ := hB
  have hun := (F₀.good w hw (by rw [← F.same.1]; exact hS0) (by rw [← F.same.2.1]; exact hBad)).2
  exact ⟨hs, hT, hS0, hBad, fun u hu => by rw [wa_mu_loc]; exact hun u (wa_v_one u hu)⟩

theorem wa_notin_B {w : Pl E} (hw : F.d.Good w) : w ∉ F.d.B := by
  obtain ⟨-, hT, hS, hB, -⟩ := hw
  simp [LocData.B, hT, hS, hB]

theorem wa_ug_ok (x : F.Γ) : (F.ug x).Ok F₀.Sec F.d.B := by
  rcases x with _ | x | x
  · exact trivial
  · exact trivial
  · exact ⟨x.1.2.1, wa_notin_B F x.1.2.2, GlobalTheory.CompanionTheory.MatchWord.isHecke_hU F.d F.ok (if_pos x.1.2.2.1) x.2.1⟩

theorem wa_ul_ok (hE : GlobalTheory.BCT.Unr E) (ws : List (List (F.Γ × Bool))) : ∀ x ∈ lU F ws, x.Ok F₀.Sec F.d.B := by
  intro x hx
  obtain ⟨p, -, rfl⟩ := List.mem_map.1 hx
  unfold ul
  split_ifs
  · exact (U.unitary_adjoint_holds E hE n F₀.Sec F₀.lam F.d.KU F.fam F.d.B (F.d.gU F.m) F.R F.levOff _ (wa_ug_ok F p.1)).1
  · exact wa_ug_ok F p.1

theorem wa_sph_map (L : List (F.Γ × Bool)) (w : Pl E) :
    U.UGen.sph (L.map (ul F)) w = MLM.wordUS F.d w (atPlace F.d w (L.map (lt F))) := by
  induction L with
  | nil => rfl
  | cons p L ih =>
    obtain ⟨x, b⟩ := p
    rcases x with u | y | y
    · have hul : ul F (Sum.inl u, b) = Sum.inl (if b then starRingEnd ℂ 1 else 1) := by
        cases b <;> rfl
      rw [List.map_cons, hul, U.pu_sph_inl, ih]; rfl
    · have hul : ul F (Sum.inr (Sum.inl y), b) = Sum.inl (if b then starRingEnd ℂ (F.dval y) else F.dval y) := by
        cases b <;> rfl
      rw [List.map_cons, hul, U.pu_sph_inl, ih]; rfl
    · have hul : ul F (Sum.inr (Sum.inr y), b) =
          Sum.inr ⟨y.1.1, if b then lstar (F.d.hU y.1.1 y.2.1) else F.d.hU y.1.1 y.2.1⟩ := by
        cases b <;> rfl
      rw [List.map_cons, hul]
      by_cases hw : y.1.1 = w
      · subst hw
        rw [U.pu_sph_self, ih]
        have e : atPlace F.d y.1.1 (lt F (Sum.inr (Sum.inr y), b) :: L.map (lt F)) =
            (y.2.1, y.2.2, b) :: atPlace F.d y.1.1 (L.map (lt F)) := by simp [atPlace, lt]
        rw [List.map_cons, e]
        cases b <;> rfl
      · rw [U.pu_sph_ne _ _ _ _ hw, ih]
        have e : atPlace F.d w (lt F (Sum.inr (Sum.inr y), b) :: L.map (lt F)) = atPlace F.d w (L.map (lt F)) := by
          simp [atPlace, lt, hw]
        rw [List.map_cons, e]

theorem wa_atPlace_ls (ws : List (List (F.Γ × Bool))) (w : Pl E) :
    atPlace F.d w (ls F ws) = atPlace F.d w (ws.flatten.map (lt F)) := by
  induction ws with
  | nil => rfl
  | cons v ws ih =>
    have e1 : ls F (v :: ws) = List.replicate F.m (Sum.inl ()) ++ (v.map (lt F) ++ ls F ws) := by
      simp [ls]
    have e2 : atPlace F.d w (List.replicate F.m (Sum.inl () : LL F.d)) = [] := by
      induction F.m with
      | zero => rfl
      | succ k ihk => simp [List.replicate_succ, atPlace] at ihk ⊢
    rw [e1, List.flatten_cons, List.map_append]
    simp only [atPlace, List.filterMap_append] at ih e2 ⊢
    rw [e2, ih, List.nil_append]

theorem count_ls (ws : List (List (F.Γ × Bool))) : (ls F ws).countP Sum.isLeft = F.m * ws.length := by
  induction ws with
  | nil => simp [ls]
  | cons v ws ih =>
    have e1 : ls F (v :: ws) = List.replicate F.m (Sum.inl ()) ++ (v.map (lt F) ++ ls F ws) := by
      simp [ls]
    have h2 : (v.map (lt F)).countP Sum.isLeft = 0 := by
      rw [List.countP_eq_zero]
      intro a ha
      obtain ⟨⟨x, b⟩, -, rfl⟩ := List.mem_map.1 ha
      rcases x with _ | _ | _ <;> simp [lt]
    rw [e1, List.countP_append, List.countP_append, ih, h2, List.countP_replicate, List.length_cons]
    simp [Sum.isLeft]
    ring

theorem sph_eq (ws : List (List (F.Γ × Bool))) (w : Pl E) :
    U.UGen.sph (lU F ws) w = MLM.wordUS F.d w (atPlace F.d w (ls F ws)) := by
  rw [wa_atPlace_ls, lU, wa_sph_map]

theorem lm (hE : GlobalTheory.BCT.Unr E) (h' : LocMatch) (ws : List (List (F.Γ × Bool))) (hws : ws ≠ []) :
    (∀ w ∈ F.d.B, IsHecke (F.d.KU w) (F.d.gU F.m w)) ∧
    (∃ w ∈ F₀.Sec, ∀ y, U.fam F.d.B F.d.KU (F.d.gU F.m) ws.length (lU F ws) w y ≠ 0 → y.1.val.charpoly.Separable) ∧
    ∀ a ≤ n, (IsTestP ((prodL F.d (ls F ws) a).tr F.d.P F.d.one) ∧ IsTestP (prodL F.d (ls F ws) a).t ∧
      IsTestP (seen ((prodL F.d (ls F ws) a).tr F.d.P F.d.one) (prodL F.d (ls F ws) a).t) ∧
      ∀ w ∈ F₀.Sec, Match n a (n - a) w (F.d.μ w) (U.fam F.d.B F.d.KU (F.d.gU F.m) ws.length (lU F ws) w)
        (seen ((prodL F.d (ls F ws) a).tr F.d.P F.d.one) (prodL F.d (ls F ws) a).t w)) ∧
      ∃ w ∈ F₀.Sec, ¬ IsSplitAt w ∧ RegAt2 a (n - a) w ((prodL F.d (ls F ws) a).tr F.d.P F.d.one w) := by
  have hk1 : 1 ≤ ws.length := List.length_pos_iff.2 hws
  exact h' E hE n F.d F.ok F.mok F₀.Sec F₀.hSec F.levOff F.T_ne (wa_mu_unit F) (fun w hw hB hs => wa_good F w hw hB hs)
    (ls F ws) F.m ws.length F.m_pos hk1 (count_ls F ws) (lU F ws) (fun w _ => sph_eq F ws w)

theorem trace_eq (hE : GlobalTheory.BCT.Unr E) (h' : LocMatch) (ws : List (List (F.Γ × Bool))) (hws : ws ≠ []) :
    GlobalTheory.BCT.IsTest (KL n) F.d.KU (U.fam F.d.B F.d.KU (F.d.gU F.m) ws.length (lU F ws)) ∧
    LinearMap.trace ℂ _ ((F.R.u ^ ws.length * ((lU F ws).map F.R.op).prod :
      EuclideanSpace ℂ (Fin F.R.d) →L[ℂ] EuclideanSpace ℂ (Fin F.R.d)) :
      EuclideanSpace ℂ (Fin F.R.d) →ₗ[ℂ] EuclideanSpace ℂ (Fin F.R.d)) =
    U.UGen.sc (lU F ws) * geomU F₀.Sec F₀.lam (U.fam F.d.B F.d.KU (F.d.gU F.m) ws.length (lU F ws)) := by
  obtain ⟨hHk, hSep, -⟩ := lm F hE h' ws hws
  obtain ⟨hTest, htr⟩ := U.unitary_words_holds E hE n F₀.Sec F₀.lam F.d.KU F.fam F.d.B (F.d.gU F.m) F.R F.levOff hHk ws.length
    (lU F ws) (wa_ul_ok F hE ws)
  exact ⟨hTest, htr hSep⟩

end Frame

end PWordId2

end PositivityTheory.Rg.BcB.F.B3

end
end

section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

open PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcN.F2

namespace PositivityTheory.Rg.BcB.F.B3

attribute [local instance] borelG borelF borelA GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

namespace PWordId2

section Frame

variable {hR : Rd.ReadLimit} {π : Submodule ℂ (UA E n → ℂ)} {S T : Finset (Pl E)} {F₀ : Frame0 hR π S} (F : RunFrame F₀ T)

theorem wb_wd_ok {B : Block E} (t₀ : PT B) (h₀ : t₀.Ok) : ∀ w : List (BGen B), (∀ g ∈ w, g.Ok) → (BGen.wd w t₀).Ok
  | [], _ => h₀
  | .inl _ :: w, h => wb_wd_ok t₀ h₀ w fun g hg => h g (List.mem_cons_of_mem _ hg)
  | .inr s :: w, h => (BlockFiniteConvolution.blkOp₀ E B s _ (h _ List.mem_cons_self)
      (wb_wd_ok t₀ h₀ w fun g hg => h g (List.mem_cons_of_mem _ hg))).2.2.1

theorem wb_adj_ok {B : Block E} : ∀ g : BGen B, g.Ok → g.adj.Ok
  | .inl _, _ => trivial
  | .inr s, h => (BlockFiniteConvolution.blkOp₀ E B s s h h).2.2.2.2.1

theorem wb_eL_adj (d : LocData E n) {a : ℕ} (ha : a ≤ n) : (d.eL a).adj.Eqv d.P (d.eL a) :=
  ⟨fun w _ => congrFun (LocComm.adj_m d (ha := ha) (Or.inl rfl)) w, fun _ _ => LocComm.lfStar_idem _,
    funext fun _ => LocComm.lfStar_idem _⟩

theorem wb_letter (i : F₀.C.ι) (p : F.Γ × Bool) :
    (∀ s, gl F i p = Sum.inr s → s.ψ = fm F₀.Sec F.d.P (F.B i) (Equiv.refl _) (locL F.d _ (F₀.C.le i) (lt F p))) ∧
      ∀ c, gl F i p = Sum.inl c → locL F.d _ (F₀.C.le i) (lt F p) = F.d.eL _ := by
  have A := BlockFiniteConvolution.fmAlg' E F.d.kap F₀.Sec F.d.P (F.B i) (Equiv.refl _) F₀.hSec (FrameOk.wirtinger_sub F)
  have O := (BlockFiniteConvolution.locOk₀ E n F.d F.ok _ (F₀.C.le i)).2.2.2
  have he : adjF (F.ψ i (F.d.eL _)) = fm F₀.Sec F.d.P (F.B i) (Equiv.refl _) (F.d.eL _) :=
    (A _ _ (O _ (Or.inl rfl)) (O _ (Or.inl rfl))).2.2.2.2.trans (fm_congr _ (wb_eL_adj F.d (F₀.C.le i)))
  obtain ⟨x | x | x, b⟩ := p
  · refine ⟨fun s hs => ?_, fun _ _ => rfl⟩
    cases b
    · obtain rfl : F.t₀ i = s := Sum.inr.inj hs
      rfl
    · obtain rfl : (F.t₀ i).adj = s := Sum.inr.inj hs
      exact he
  · refine ⟨fun s hs => ?_, fun _ _ => rfl⟩
    by_cases h : i = x.1
    · have e : F.g (.inr (.inl x)) i = .inr (F.tD i x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2) := if_pos h
      unfold gl at hs
      rw [e] at hs
      cases b
      · obtain rfl := Sum.inr.inj hs
        rfl
      · obtain rfl := Sum.inr.inj hs
        exact he
    · have e : F.g (.inr (.inl x)) i = .inl (F.dval x) := if_neg h
      unfold gl at hs
      rw [e] at hs
      cases b <;> exact absurd hs Sum.inl_ne_inr
  · cases b
    · refine ⟨fun s hs => ?_, fun c hc => absurd hc Sum.inr_ne_inl⟩
      obtain rfl := Sum.inr.inj hs
      rfl
    · refine ⟨fun s hs => ?_, fun c hc => absurd hc Sum.inr_ne_inl⟩
      obtain rfl := Sum.inr.inj hs
      have o := O _ (Or.inr ⟨x.1.1, x.2.1, x.2.2, x.1.2.2, rfl⟩)
      exact (A _ _ o o).2.2.2.2

theorem blk_eq (h : LocWord) (hF : F.Struct) (i : F₀.C.ι) (ws : List (List (F.Γ × Bool))) :
    (prodL F.d (ls F ws) (F₀.C.a i)).Ok F.d.P ∧ (tw F i ws).Ok ∧
    (tw F i ws).ψ = rt (F₀.u₁ _) (F₀.u₂ _) (fm F₀.Sec F.d.P (F.B i) (Equiv.refl _) (prodL F.d (ls F ws) (F₀.C.a i))) ∧
    trM (tw F i ws).Φ (MM F i) = (F.B i).vol⁻¹ • adel F₀.Sec (F₀.u₁ (F₀.C.a i)) (F₀.u₂ (F₀.C.a i))
      ((tw F i ws).arch (F₀.A i).Ta (F₀.A i).Tb) ((prodL F.d (ls F ws) (F₀.C.a i)).tr F.d.P F.d.one)
      (prodL F.d (ls F ws) (F₀.C.a i)).t := by

  have O := BlockFiniteConvolution.locOk₀ E n F.d F.ok _ (F₀.C.le i)
  have L := (h E n F.d F.ok _ (F₀.C.le i) [Sum.inl ()] 0 rfl).1
  let prs : List (BGen (F.B i) × LM F.d.kap (F₀.C.a i) (n - F₀.C.a i)) := (Sum.inr (F.t₁ i), F.d.fixL _) ::
    (ws.map fun w => List.replicate F.m (Sum.inr (F.β i), F.d.betaL _ (F₀.C.le i)) ++
      w.map fun p => (gl F i p, locL F.d _ (F₀.C.le i) (lt F p))).flatten
  have e1 : prs.map Prod.fst = Sum.inr (F.t₁ i) :: (ws.map (bw F i)).flatten := by
    simp only [prs, List.map_cons, List.map_flatten, List.map_map, Function.comp_def, List.map_append, List.map_replicate]
    rfl
  have e2 : prs.map Prod.snd = F.d.fixL _ :: (ls F ws).map (locL F.d _ (F₀.C.le i)) := by
    simp only [prs, ls, List.map_cons, List.map_flatten, List.map_map, Function.comp_def, List.map_append, List.map_replicate]
    rfl
  have e3 : prodL F.d (ls F ws) (F₀.C.a i) = (prs.map Prod.snd).foldr LM.mul (F.d.eL _) := by
    rw [e2, prodL, dif_pos (F₀.C.le i)]
  have e4 : tw F i ws = BGen.wd (prs.map Prod.fst) (F.t₂ i) := by rw [e1]; rfl
  have R := adelRep2 (S := F₀.Sec) (B := F.B i) (Equiv.refl _) F₀.hSec (FrameOk.wirtinger_sub F) (fun w _ => O.1 w) (F₀.u₁ _) (F₀.u₂ _)
    (F₀.A i).Ta (F₀.A i).Tb F.d.one (F.d.eL _) (F.d.eL _) (F.t₂ i) (L (.inr (.inl ()))).1 (L (.inr (.inl ()))).1
    (L (.inr (.inl ()))).2.1 rfl prs (by
      intro p hp
      rcases List.mem_cons.1 hp with rfl | hp
      · exact ⟨O.2.2.1, (MatchAll.matchLMId E n F.d F.ok _ (F₀.C.le i) _ (Or.inr (Or.inl rfl))).2,
          fun s hs => by obtain rfl := Sum.inr.inj hs; rfl, fun c hc => absurd hc Sum.inr_ne_inl⟩
      obtain ⟨l, hl, hp⟩ := List.mem_flatten.1 hp
      obtain ⟨w, -, rfl⟩ := List.mem_map.1 hl
      rcases List.mem_append.1 hp with hp | hp
      · obtain rfl := List.eq_of_mem_replicate hp
        exact ⟨(L (.inl ())).1, (L (.inl ())).2.1, fun s hs => by obtain rfl := Sum.inr.inj hs; rfl,
          fun c hc => absurd hc Sum.inr_ne_inl⟩
      · obtain ⟨q, -, rfl⟩ := List.mem_map.1 hp
        exact ⟨(L _).1, (L _).2.1, wb_letter F i q⟩)
  refine ⟨e3 ▸ R.1, wb_wd_ok _ (hF.tok i).2 _ fun g hg => ?_, ?_, ?_⟩
  · rcases List.mem_cons.1 hg with rfl | hg
    · exact (hF.tok i).1
    obtain ⟨l, hl, hg⟩ := List.mem_flatten.1 hg
    obtain ⟨w, -, rfl⟩ := List.mem_map.1 hl
    rcases List.mem_append.1 hg with hg | hg
    · obtain rfl := List.eq_of_mem_replicate hg
      exact hF.βok i
    · obtain ⟨⟨x, b⟩, -, rfl⟩ := List.mem_map.1 hg
      cases b
      · exact hF.ok x i
      · exact wb_adj_ok _ (hF.ok x i)
  · rw [e3, e4]; exact R.2.1
  · rw [e3, e4]; exact R.2.2

end Frame

end PWordId2

end PositivityTheory.Rg.BcB.F.B3

end
end

section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

open PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcN.F2

namespace PositivityTheory.Rg.BcB.F.B3

attribute [local instance] borelG borelF borelA GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

namespace PWordId2

section Frame

variable {hR : Rd.ReadLimit} {π : Submodule ℂ (UA E n → ℂ)} {S T : Finset (Pl E)} {F₀ : Frame0 hR π S} (F : RunFrame F₀ T)

theorem wd_val {B : Block E} (w : List (BGen B)) (t₀ : PT B) (hw : ∀ g ∈ w, BGen.Ok g) (h0 : t₀.Ok)
    (χa : InfinitePlace E → Inf B.a) (χb : InfinitePlace E → Inf B.b) :
    (BGen.wd w t₀).Ok ∧ (BGen.wd w t₀).val χa χb = (w.map (Sum.elim (fun _ => 1) fun s => s.val χa χb)).prod * t₀.val χa χb := by
  induction w with
  | nil => simp [BGen.wd, h0]
  | cons g w ih =>
    obtain ⟨ih1, ih2⟩ := ih (fun g hg => hw g (List.mem_cons_of_mem _ hg))
    rcases g with c | s
    · refine ⟨ih1, ?_⟩
      simp only [BGen.wd, List.foldr_cons, Sum.elim_inl, List.map_cons, List.prod_cons, one_mul] at ih2 ⊢
      exact ih2
    · have hs : s.Ok := hw (Sum.inr s) List.mem_cons_self
      have h := BlockFiniteConvolution.blkOp₀ E B s (BGen.wd w t₀) hs ih1
      refine ⟨h.2.2.1, ?_⟩
      have e : BGen.wd (Sum.inr s :: w) t₀ = s.mul (BGen.wd w t₀) := rfl
      rw [e, h.2.2.2.2.2.2.1, ih2, List.map_cons, List.prod_cons, Sum.elim_inr, mul_assoc]

variable {F} in
theorem pt_val (i : F₀.C.ι) (wa wb : InfinitePlace E → List (Bool × ℕ)) (ψ : Matrix F.κ F.κ (Hf E (F₀.C.a i) (n - F₀.C.a i) → ℂ)) (r : ℝ) :
    ((F₀.A i).pt wa wb ψ r).val (F₀.A i).χa (F₀.A i).χb =
      (∏ v, zVal (wa v) ((F₀.A i).χa v)) * ∏ v, zVal (wb v) ((F₀.A i).χb v) := by
  have h1 : (∏ v, coshT (F₀.A i).bump (cas ((F₀.A i).χa v))) * ∏ v, coshT (F₀.A i).bump (cas ((F₀.A i).χb v)) = 1 :=
    (F₀.A i).one
  simp only [PT.val, valA, Arch.pt, Arch.valW, Finset.prod_mul_distrib]
  rw [mul_mul_mul_comm, h1, mul_one]

theorem hermA (i : F₀.C.ι) (v : InfinitePlace E) : IsHerm ((F₀.A i).χa v) := FBL.hermInf_holds _ _
theorem hermB (i : F₀.C.ι) (v : InfinitePlace E) : IsHerm ((F₀.A i).χb v) := FBL.hermInf_holds _ _

theorem ptL_val (i : F₀.C.ι) (L : LM F.d.kap (F₀.C.a i) (n - F₀.C.a i)) :
    (F.ptL i L).val (F₀.A i).χa (F₀.A i).χb = 1 := by
  simp [RunFrame.ptL, pt_val, zVal]

theorem t₂_val (i : F₀.C.ι) : (F.t₂ i).val (F₀.A i).χa (F₀.A i).χb = 1 := by
  simp [RunFrame.t₂, pt_val, zVal]

theorem letter (i : F₀.C.ι) (x : F.Γ) :
    Sum.elim id (fun _ => 1) (F.g x i) * Sum.elim (fun _ => 1) (fun s : PT (F.B i) => s.val (F₀.A i).χa (F₀.A i).χb) (F.g x i) =
      Sum.elim id (fun _ => 1) (F.ug x) := by
  rcases x with u | x | x
  · simp [RunFrame.g, RunFrame.ug, RunFrame.t₀, ptL_val]
  · simp only [RunFrame.g, RunFrame.ug]
    split_ifs with h
    · subst h
      obtain ⟨j, v, s, m, side⟩ := x
      simp only [Sum.elim_inr, Sum.elim_inl, id, one_mul, RunFrame.tD, pt_val, RunFrame.dval]
      cases side <;> simp [zVal] <;>
        rw [Finset.prod_eq_single v (fun b _ hb => by simp [hb]) (by simp)] <;> simp
    · simp
  · simp [RunFrame.g, RunFrame.ug, ptL_val]

theorem val_eq (hF : F.Struct) (i : F₀.C.ι) (ws : List (List (F.Γ × Bool))) :
    BGen.sc (ws.map (bw F i)).flatten * (tw F i ws).val (F₀.A i).χa (F₀.A i).χb = U.UGen.sc (lU F ws) := by
  have hadj : ∀ g : BGen (F.B i), g.Ok → g.adj.Ok ∧
      Sum.elim id (fun _ => 1) g.adj * Sum.elim (fun _ => 1) (fun s : PT (F.B i) => s.val (F₀.A i).χa (F₀.A i).χb) g.adj =
        starRingEnd ℂ (Sum.elim id (fun _ => 1) g * Sum.elim (fun _ => 1) (fun s : PT (F.B i) => s.val (F₀.A i).χa (F₀.A i).χb) g) := by
    rintro (c | t) hg
    · exact ⟨trivial, by simp [BGen.adj]⟩
    · have h := BlockFiniteConvolution.blkOp₀ E (F.B i) t t hg hg
      refine ⟨h.2.2.2.2.1, ?_⟩
      simp only [BGen.adj, Sum.map_inr, Sum.elim_inr, one_mul]
      exact h.2.2.2.2.2.2.2 _ _ (hermA i) (hermB i)
  have hl : ∀ p : F.Γ × Bool, (gl F i p).Ok ∧
      Sum.elim id (fun _ => 1) (gl F i p) * Sum.elim (fun _ => 1) (fun s : PT (F.B i) => s.val (F₀.A i).χa (F₀.A i).χb) (gl F i p) =
        Sum.elim id (fun _ => 1) (ul F p) := by
    rintro ⟨x, b⟩
    have hx := letter F i x
    cases b
    · simp only [gl, ul, Bool.false_eq_true, if_false]; exact ⟨hF.ok x i, hx⟩
    · simp only [gl, ul, if_true]
      refine ⟨(hadj _ (hF.ok x i)).1, ?_⟩
      rw [(hadj _ (hF.ok x i)).2, hx]
      rcases F.ug x with c | u <;> simp [U.UGen.adj]
  have hok : ∀ g ∈ Sum.inr (F.t₁ i) :: (ws.map (bw F i)).flatten, BGen.Ok g := by
    intro g hg
    rcases List.mem_cons.1 hg with rfl | hg
    · exact (hF.tok i).1
    · obtain ⟨l, hl', hg⟩ := List.mem_flatten.1 hg
      obtain ⟨w, -, rfl⟩ := List.mem_map.1 hl'
      rcases List.mem_append.1 hg with hg | hg
      · rw [List.eq_of_mem_replicate hg]; exact hF.βok i
      · obtain ⟨p, -, rfl⟩ := List.mem_map.1 hg
        exact (hl p).1
  obtain ⟨-, hv⟩ := wd_val _ (F.t₂ i) hok (hF.tok i).2 (F₀.A i).χa (F₀.A i).χb
  rw [tw, hv, t₂_val, List.map_cons, List.prod_cons, Sum.elim_inr, RunFrame.t₁, ptL_val, one_mul, mul_one,
    BGen.sc, ← List.prod_map_mul, U.UGen.sc, lU, List.map_map]
  clear hok hv
  induction ws with
  | nil => simp
  | cons w ws ih =>
    rw [List.map_cons, List.flatten_cons, List.map_append, List.prod_append, ih, List.flatten_cons, List.map_append,
      List.prod_append]
    congr 1
    simp only [bw, List.map_append, List.prod_append, List.map_replicate, List.map_map]
    rw [List.prod_replicate, Sum.elim_inr, Sum.elim_inr, RunFrame.β, ptL_val]
    simp only [mul_one, one_pow, one_mul]
    congr 1
    exact List.map_congr_left fun p _ => (hl p).2

theorem lef_pt (i : F₀.C.ι) (t : PT (F.B i)) (ht : t.Ok) (v : InfinitePlace E) :
    LefAt (F₀.C.νC (F₀.C.a i)) (F₀.C.νC (n - F₀.C.a i)) (F₀.C.l₁ i v) (F₀.C.l₂ i v)
      (t.va v ((F₀.A i).χa v) * t.vb v ((F₀.A i).χb v)) (t.arch (F₀.A i).Ta (F₀.A i).Tb v) := by
  exact (F₀.A i).lef v _ _ _ _ t.T (ht.ka v) (ht.kb v)

end Frame

end PWordId2

end PositivityTheory.Rg.BcB.F.B3

end
end

section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

open PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcN.F2

namespace PositivityTheory.Rg.BcB.F.B3

attribute [local instance] borelG borelF borelA GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

namespace PWordId2

section Frame

variable {hR : Rd.ReadLimit} {π : Submodule ℂ (UA E n → ℂ)} {S T : Finset (Pl E)} {F₀ : Frame0 hR π S} (F : RunFrame F₀ T)
theorem lefAt_smul {a b : ℕ} {ν₁ : Measure (G a)} {ν₂ : Measure (G b)} {l₁ : DomWeight a} {l₂ : DomWeight b} {val : ℂ}
    {ψ : G a × G b → ℂ} (h : LefAt ν₁ ν₂ l₁ l₂ val ψ) (c : ℂ) : LefAt ν₁ ν₂ l₁ l₂ (c * val) fun y => c * ψ y := by
  refine ⟨continuous_const.mul h.1, h.2.1.mul_left, fun d₁ d₂ h₁ h₂ => ?_⟩
  rw [integral_const_mul, h.2.2 d₁ d₂ h₁ h₂]
  ring

theorem adel_scale {a b : ℕ} (S : Set (Pl E)) (u₁ : GL (Fin a) E) (u₂ : GL (Fin b) E) (ψ : InfinitePlace E → G a × G b → ℂ)
    (φ₁ φ₂ : ∀ w : Pl E, GLw a w × GLw b w → ℂ) (c : InfinitePlace E → ℂ) :
    adel S u₁ u₂ (fun v y => c v * ψ v y) φ₁ φ₂ = (∏ v, c v) • adel S u₁ u₂ ψ φ₁ φ₂ := by
  funext x
  simp only [adel, Finset.prod_mul_distrib, Pi.smul_apply, smul_eq_mul, mul_assoc]

theorem main (hE : GlobalTheory.BCT.Unr E) (h : LocWord) (h' : LocMatch) (hF : F.Struct) : WordIdAt F := by
  choose c₀ hc₀ hT using fun i => BlockFiniteConvolution.pTTest₀ E (F.B i)
  refine ⟨fun i => F₀.C.c i * (F.B i).vol, c₀, hc₀, fun ws hws => ?_⟩
  obtain ⟨-, -, hm⟩ := lm F hE h' ws hws
  have hP : (↑F.d.P : Set (Pl E)) ⊆ F₀.Sec := FrameOk.wirtinger_sub F
  refine ⟨fun i => ?_, ?_⟩
  · obtain ⟨b1, b2, b3, -⟩ := blk_eq F h hF i ws
    exact hT i F.d.kap F₀.Sec F.d.P (Equiv.refl _) F₀.hSec hP
      (fun w _ => (BlockFiniteConvolution.locOk₀ E n F.d F.ok _ (F₀.C.le i)).1 w) _ _ (F₀.hu _).1 (F₀.hu _).2 _ _ F.d.one _ _
      ⟨(F₀.A i).vca, (F₀.A i).vcb⟩ b2 b1 b3 (hm _ (F₀.C.le i)).2
  obtain ⟨t1, t2⟩ := trace_eq F hE h' ws hws
  obtain ⟨v₀⟩ : Nonempty (InfinitePlace E) := inferInstance
  have hμ : ∀ w, F.d.μ w = F₀.μ.loc w := fun w => by rw [← F₀.μloc w, F.same.2.2.1]
  let sc : F₀.C.ι → InfinitePlace E → ℂ := fun i v => if v = v₀ then BGen.sc (ws.map (bw F i)).flatten else 1
  have hsc : ∀ i, ∏ v, sc i v = BGen.sc (ws.map (bw F i)).flatten := fun i => by simp [sc]
  have key := F₀.C.eq F₀.Sec F₀.hSec F.d.KU _ F.levOff.2.1 t1 F₀.u₁ F₀.u₂ F₀.hu
    (fun a => (prodL F.d (ls F ws) a).tr F.d.P F.d.one) (fun a => (prodL F.d (ls F ws) a).t)
    (fun a ha => ⟨(hm a ha).1.1, (hm a ha).1.2.1, (hm a ha).1.2.2.1, fun w hw => hμ w ▸ (hm a ha).1.2.2.2 w hw⟩)
    (fun i => by
      obtain ⟨w, hw, hs, hr⟩ := (hm _ (F₀.C.le i)).2
      refine ⟨w, hw, fun y hy => hr y ?_⟩
      simpa [seen, hs] using hy)
    (fun i v => sc i v * ((tw F i ws).va v ((F₀.A i).χa v) * (tw F i ws).vb v ((F₀.A i).χb v)))
    (fun i v y => sc i v * (tw F i ws).arch (F₀.A i).Ta (F₀.A i).Tb v y)
    (fun i v => lefAt_smul (lef_pt F i _ (blk_eq F h hF i ws).2.1 v) _) (U.UGen.sc (lU F ws))
    (fun i => by
      rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, hsc, ← val_eq F hF i ws]
      rfl)
  refine t2.trans (key.trans (Finset.sum_congr rfl fun i _ => ?_))
  have hv : (F.B i).vol ≠ 0 := (BlockFiniteConvolution.finConv' E (F.B i) F₀.Sec F₀.hSec).1
  rw [adel_scale, hsc, (blk_eq F h hF i ws).2.2.2, FBL.ellHom_holds, FBL.ellHom_holds]
  field_simp

end Frame

end PWordId2

end PositivityTheory.Rg.BcB.F.B3

end
end
