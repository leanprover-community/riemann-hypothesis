import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TiedColumnData
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotConditionOfFalse
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedVectorEqOfStandardData
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsTwIffCanonEq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JetsInIffStepField
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmQuadraticFormEqAlternatingForm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsColInJetsIn
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHalfSelectionSplitPlacesBase

section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.TwEx

open JetEx

def stepSet (P : Pre) (χ : Formalism.L2.Host.HChar P.host.E)
    (k : P.Word × ℕ × Finset (HeightOneSpectrum (𝓞 P.host.E)) × Finset (HeightOneSpectrum (𝓞 P.host.E))) : Set ℂ :=
  jetSet (hostAmb (amb0 P.host) (chiId χ)) (P.R.N k.2.1) (P.R.N (k.2.1 + 1)) k.2.2.1
    ((∏ Q ∈ k.2.2.2, qOf Q) ^ (P.R.m + 1) * (P.T k.1 * (∏ Q ∈ k.2.2.2, qOf Q) ^ (P.R.m + 1))) (totDeg P k.1 k.2.1)

def allSet (P : Pre) (χ : Formalism.L2.Host.HChar P.host.E) (Ξ : Set (Formalism.L2.Host.HChar P.host.E)) : Set ℂ :=
  ⋃ k ∈ {k : P.Word × ℕ × Finset (HeightOneSpectrum (𝓞 P.host.E)) × Finset (HeightOneSpectrum (𝓞 P.host.E)) |
      (k.2.1 < P.R.m ∧ (∀ Q ∈ k.2.2.1, Q ∈ badP P Ξ) ∧ ∀ Q ∈ k.2.2.2, Q ∈ badP P Ξ) ∧ FinAlg (stepSet P χ k)}, stepSet P χ k

theorem finAlg_allSet (P : Pre) (χ : Formalism.L2.Host.HChar P.host.E) {Ξ : Set (Formalism.L2.Host.HChar P.host.E)} (h : Ξ.Finite) : FinAlg (allSet P χ Ξ) := by
  have hb := badPrimes_finite₂ P h
  have hs : {S : Finset (HeightOneSpectrum (𝓞 P.host.E)) | ∀ Q ∈ S, Q ∈ badP P Ξ}.Finite :=
    hb.toFinset.powerset.finite_toSet.subset fun S hS =>
      Finset.mem_coe.2 (Finset.mem_powerset.2 fun Q hQ => hb.mem_toFinset.2 (hS Q hQ))
  refine finAlg_biUnion ?_ fun k hk => hk.2
  exact (Set.finite_univ.prod ((Set.finite_Iio P.R.m).prod (hs.prod hs))).subset fun k hk => ⟨trivial, hk.1⟩

open Classical in

def gens (P : Pre) (χ : Formalism.L2.Host.HChar P.host.E) (Ξ : Set (Formalism.L2.Host.HChar P.host.E)) : Finset ℂ :=
  if h : FinAlg (allSet P χ Ξ) then h.choose else ∅

theorem gens_algebraic (P : Pre) (χ : Formalism.L2.Host.HChar P.host.E) (Ξ : Set (Formalism.L2.Host.HChar P.host.E)) : ∀ z ∈ gens P χ Ξ, IsAlgebraic ℚ z := by
  unfold gens
  split_ifs with h
  · exact h.choose_spec.1
  · simp

theorem allSet_subset (P : Pre) (χ : Formalism.L2.Host.HChar P.host.E) {Ξ : Set (Formalism.L2.Host.HChar P.host.E)} (h : Ξ.Finite) {K : Subfield ℂ}
    (hK : ∀ z ∈ gens P χ Ξ, z ∈ K) : allSet P χ Ξ ⊆ K := by
  have h1 := finAlg_allSet P χ h
  rw [gens, dif_pos h1] at hK
  exact h1.choose_spec.2.trans (Subfield.closure_le.2 hK)

theorem jetsIn_of_isTw {B : Base} {X : PreX B.toPre} (hL : StagesInhab.HasLetters B.toPre) {I : TC B X} (h : I.Ok) (ht : I.IsTw)
    (hJ : I.J = amb0 B.host) (hK : ∀ z ∈ gens B.toPre I.C.chiPsi (Set.range I.xi), z ∈ B.embLL.fieldRange) :
    ColIn.JetsIn I := by
  have hall := allSet_subset B.toPre I.C.chiPsi (Set.finite_range I.xi) hK
  refine I.jetsIn_iff.2 fun a u i hi N N' c x hx e he => ?_
  have hM : I.modulus a u = (∏ Q ∈ rowSG (B.primes X) I.sel (I.tup a), qOf Q) ^ (B.R.m + 1) *
      (B.T u * (∏ Q ∈ rowSG (B.primes X) I.sel (I.tup a), qOf Q) ^ (B.R.m + 1)) := by
    have eA : (I.cst a).A = B.R.m + 1 := by rw [ht.cst_eq a]; rfl
    have eB : (I.cst a).B = B.R.m + 1 := by rw [ht.cst_eq a]; rfl
    unfold ColIn.modulus cAof cBof
    rw [eA, eB, Finset.prod_coe_sort _ qOf]
  have hS : stepSet B.toPre I.C.chiPsi (u, i, I.Sb a u, rowSG (B.primes X) I.sel (I.tup a)) =
      jetSet I.A (B.R.N i) (B.R.N (i + 1)) (I.Sb a u) (I.modulus a u) (totDeg B.toPre u i) := by
    rw [hM, ColIn.A, hJ]
    exact (jetSet_amb B _ _ _ _ _ _ _).symm
  have hpos : 0 < I.modulus a u := by
    rw [hM]
    have := Finset.prod_pos fun Q (_ : Q ∈ rowSG (B.primes X) I.sel (I.tup a)) =>
      Nat.pos_of_ne_zero (by simpa using qPow_ne_zero Q 1 : qOf Q ≠ 0)
    have := (B.T_prime u).pos
    positivity
  refine hall (Set.mem_iUnion₂.2 ⟨(u, i, I.Sb a u, rowSG (B.primes X) I.sel (I.tup a)),
    ⟨⟨hi, Sb_subset h a u, rowSG_subset h a⟩, ?_⟩, ?_⟩)
  · rw [hS]
    exact finAlg_step hL h a u _ _ _ _ hpos
  · rw [hS]
    exact ⟨N, N', c, x, e, hx, degree_eq_totDeg B u i e he, rfl⟩

theorem lg_gens (K : Top.Ctx) : Top.large₂ K fun B f T => ∀ z ∈ gens B.toPre f.chiPsi (T.set f), z ∈ B.embLL.fieldRange :=
  ⟨fun _ _ _ => ∅, fun _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, fun P f _ _ Ξ => gens P f.chiPsi Ξ, by simp,
    fun P f _ _ Ξ => gens_algebraic P f.chiPsi Ξ, fun _ _ _ _ h _ _ => h.2⟩

theorem exists_quot {K : Top.Ctx} {P : Pre} (h : K.Over P) (X : PreX P) :
    ∃ X' : PreX P, X'.piG = X.piG ∧ ∀ u, P.cOf u * (X'.piT u : P.host.E) = (X'.piT P.u₀ : P.host.E) := by
  obtain ⟨sp, hT, hY, hA, hV, hz, rfl, -⟩ := h
  refine ⟨{ X with
    piT := K.Lv.piT
    piT_K := K.Lv.piT_K
    piT_norm := K.Lv.piT_norm
    piT_cong := fun u => Ideal.mem_span_singleton.1 (K.Lv.piT_cong u) }, rfl, fun u => ?_⟩
  exact div_mul_cancel₀ _ (K.Lv.piT_ne u)

theorem evLg_canonical : GlobalTheory.Mem.Top.EvLg fun _ B f T => (letI := B.host.cmStar; ∀ (a : Fin B.sp.X'.rank) (b : Fin (B.sp.X B.R.m).rank), (a : ℕ) = b → B.sp.iX' (B.sp.X'.frame a) = (B.sp.X B.R.m).frame b) → Nonempty (PreX B.toPre) → ∀ Pv, IsSel B.fields Pv → ∃ (X : PreX B.toPre) (I : TC B X), I.Ok ∧ TC.Pins B X ∧ I.IsTw ∧ ColIn.JetsIn I ∧ I.sel = Pv ∧ I.C = f ∧ I.S = {p | p ∈ GlobalTheory.Mem.Top.offSet B.toPre ∧ p ≠ B.host.pde ∧ p ≠ B.host.pde'} ∧ Set.range I.xi = T.set f ∧ ∀ C W V S N G, Formalism.L2.Host.ValLL0 (assemble B C W V S N G) (GlobalTheory.Mem.Top.Fr.at ⟨B, C, W, V, S, N, G⟩ f) ∧ GlobalTheory.Mem.Per.FieldOK B.host B.embLL B.embE := by
  refine InEx.ev_of_forall fun K => ((InEx.lg_colIn K).inter (lg_gens K)).imp fun B f T hO h hi ⟨X₀⟩ Pv hPv => ?_
  obtain ⟨X₁, hX⟩ := InEx.exists_oriented X₀ f.P
  obtain ⟨X, e, hc⟩ := exists_quot hO X₁
  have hX' : InEx.Oriented X f.P := by
    unfold InEx.Oriented at hX ⊢
    rw [e]; exact hX
  obtain ⟨I, a1, rfl, a3, a4, a5, a6, a7⟩ := h.1.1 X hX' Pv hPv (amb0 B.host) (exists_ambIn_ok B.host).choose_spec
  have hk : (canon I).Ok := canon_ok a1 fun a P hP => ((a7 a).2.2.2 P hP).ge
  exact ⟨X, canon I, hk, ⟨hi, hc⟩, canon_isTw I,
    jetsIn_of_isTw (hasLetters_of_over hO) hk (canon_isTw I) a6 (by have := h.2; rw [← a4] at this; exact this), a5, rfl, a3, a4,
    fun C W V S N G => ⟨h.1.2.1 C W V S N G, h.1.2.2⟩⟩

end GlobalTheory.Mem.Col2.TwEx

end
end

section
noncomputable section

namespace GlobalTheory.Mem.Top.Bl

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting NumberField IsDedekindDomain

theorem lg_vals_roots (K : Ctx) : large₂ K fun B f T =>
    (∀ ξ ∈ T.set f, ∀ P, ∃ z : B.LL, B.embLL z = ((ξ.val P : ℂˣ) : ℂ)) ∧
    ∀ ξ ∈ T.set f, ∀ P, ¬ ξ.UnrAt P → ∃ ζ : B.LL, IsPrimitiveRoot ζ (Ideal.absNorm P.asIdeal) := by
  choose Z hZ gZ using fun (B : Pre) (Ξ : Set (HChar B.host.E)) => InEx.exists_holds 1 Ξ
  refine ⟨fun _ _ _ => ∅, fun _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, fun B _ _ _ Ξ => Z B Ξ, by simp,
    fun B _ _ _ Ξ => hZ B Ξ, fun B f T _ hH _ _ => ?_⟩
  have hf := (TwFin.tw_fin B f T).1
  have ht := InEx.isTwist_of_mem_set B f T
  have h2 : ∀ z ∈ Z B.toPre (T.set f), ∃ x, B.embLL x = z := fun z hz => B.mem_LLC.1 (hH.2 z hz)
  have hold := fun ξ hξ => gZ B.toPre _ hf B.LL B.embLL h2 ξ hξ (ht ξ hξ).1
  refine ⟨fun ξ hξ P => RingHom.mem_range.1 ((hold ξ hξ).1 _), fun ξ hξ P hP => ?_⟩
  obtain ⟨ζ, hζ⟩ := ((hold ξ hξ).2 P hP).2
  exact ⟨ζ, by simpa using hζ⟩

theorem step_colW_pinned (h2b : StandardLattice.SiegelMassRatioCM) :
    Step KPx (fun _ _ _ _ => True) fun K B f T => ∃ w : ColW B f T, Pinned K B f T w := by
  refine EvG.imp ((evG_of_ev (ev_preX_frame h2b)).inter (evG_of_ev TwEx.evLg_canonical)) fun K _ _ _ _ H => ?_
  refine ((H.2.inter (InEx.lg_colIn K)).inter (lg_vals_roots K)).imp ?_
  rintro B f T hO ⟨⟨hc, hl⟩, hv, hr⟩ ⟨⟨δ, hδ⟩, hp⟩ - -
  obtain ⟨X₀⟩ := (H.1 _ hO).1
  obtain ⟨Pv, d, hsel, habove, hhalf, hd1, hd2⟩ := exists_half_selection_split_places B
  obtain ⟨X, I, a1, pins, ht, hj, es, a2, a3, a4, -⟩ := hc hp ⟨X₀⟩ Pv hsel
  have hxi : ∀ a, I.xi a ∈ T.set f := fun a => a4 ▸ ⟨a, rfl⟩
  refine ⟨⟨X, I, a1, a2, a3, a4, pins, TrueColsTest.laws a1, TrueColsTest.law0 a1 _, δ, hδ, hl.2.2, hl.2.1⟩, ⟨?_⟩⟩
  refine
    { isTw := ht
      jets := hj
      hX := FieldsLaws.fields_ok B
      above := fun v => es ▸ habove v
      half := es ▸ hhalf
      d3b := d
      selectedPlacesAgree := ⟨fun v hv => es ▸ hd1 v hv, fun v hv => es ▸ hd2 v hv⟩
      vals := fun a P _ => hv _ (hxi a) P
      roots := fun a P hP => ?_ }
  have htw : Chr.IsTwist B.host I.S (I.xi a) := by
    rw [a3]
    exact InEx.isTwist_of_mem_set B f T _ (hxi a)
  obtain ⟨P', h1, h2⟩ := InEx.exists_ram_of_mem_QE B (es ▸ hsel) (I.tup a) htw (a1.xi_reads a) hP
  obtain ⟨ζ, hζ⟩ := hr _ (hxi a) P' h1
  refine ⟨ζ, ?_⟩
  rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, h2]
  exact hζ

end GlobalTheory.Mem.Top.Bl

end
end
