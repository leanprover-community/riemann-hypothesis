import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.AnalyticResolutionHypothesesProjectiveLine
import GroundTheory.HeightsAndTheta.Heights.Intersections.IsSmoothMetricOfIsSmoothHerm
import GroundTheory.HeightsAndTheta.Heights.Intersections.CompsDim
import GroundTheory.HeightsAndTheta.Heights.Intersections.StResExists
import GroundTheory.HeightsAndTheta.Heights.Intersections.FourierIntegralBound
import ReciprocityTheory.AnalyticForms.PotentialTheory.PotentialContDiffAt
import ReciprocityTheory.AnalyticForms.PotentialTheory.HessCEqZeroOfEventuallyEqZero
import ReciprocityTheory.AnalyticForms.PotentialTheory.PLCurveA
import GroundTheory.HeightsAndTheta.Heights.Intersections.StZIntPoint
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Assembly
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedF

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

open GroundTheory.Heights₂.Heights.NumbersDVR (MRing)

def ZIntAdd.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι ℂ)) (e : ℕ) (L : Fin e → HLine ι) (A B : HLine ι),
    IsProjVar P (e + 1) → Nonempty (Res ι P (e + 1)) → (∀ j, IsSmoothMetric P (L j)) →
    IsSmoothMetric P A → IsSmoothMetric P B →
    zInt P (e + 1) (Fin.cons (logH (ReciprocityTheory.ChartRestriction.G.Geo.HermLine.tensor A B)) fun j => logH (L j))
        (fun _ => 1) =
      zInt P (e + 1) (Fin.cons (logH A) fun j => logH (L j)) (fun _ => 1) +
        zInt P (e + 1) (Fin.cons (logH B) fun j => logH (L j)) (fun _ => 1)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

open ReciprocityTheory.AnForm.M Topology
open GroundTheory.Heights₂.Heights.NumbersDVR (MRing)

theorem locDens_congr_germ {n : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas n X)
    (Φ Ψ : Fin n → LocPot X) (j : Fin A.n) (y : Fin n → ℂ)
    (h : ∀ k, (fun y' => (Φ k).φ ((A.chart j).symm y) ((A.chart j).symm y')) =ᶠ[𝓝 y]
      (fun y' => (Ψ k).φ ((A.chart j).symm y) ((A.chart j).symm y'))) :
    locDens A Φ j y = locDens A Ψ j y := by
  unfold locDens ReciprocityTheory.AnForm.maDens
  congr 3
  funext k
  exact ReciprocityTheory.AnForm.M.PLAux.hessC_congr_eventuallyEq (h k)

theorem ZIntAdd.proof : ZIntAdd.Statement := by
  intro K _ _ ι _ P e L A B hP hR hL hA hB
  unfold zInt
  rw [dif_pos hR, dif_pos hR, dif_pos hR]
  set R := hR.some
  unfold Res.int
  have hpA := R.isPotential_pot (isSmoothPot_logH hA)
  have hpB := R.isPotential_pot (isSmoothPot_logH hB)
  have hpL : ∀ j, IsPotential R.atlas (R.pot (logH (L j))) :=
    fun j => R.isPotential_pot (isSmoothPot_logH (hL j))
  have hcons : ∀ Q : LocPot R.R.M, IsPotential R.atlas Q →
      ∀ i, IsPotential R.atlas ((Fin.cons Q fun j => R.pot (logH (L j)) :
        Fin (e + 1) → LocPot R.R.M) i) := by
    intro Q hQ i
    cases i using Fin.cases
    · exact hQ
    · exact hpL _
  have e1 : ∀ φ0 : MCone ι → ℝ,
      mInt R.atlas (fun j => R.pot ((Fin.cons φ0 fun j => logH (L j) : Fin (e + 1) → MCone ι → ℝ) j))
        (fun x => (fun _ => (1 : ℝ)) (R.pt x)) =
      mInt R.atlas (Fin.cons (R.pot φ0) fun j => R.pot (logH (L j))) (fun _ => 1) := by
    intro φ0
    refine ReciprocityTheory.AnForm.M.PLC.mInt_congr_phi _ _ _ (fun i a b => ?_) _
    cases i using Fin.cases <;> rfl
  rw [e1, e1, e1, ← mIntAdd R.atlas (R.pot (logH A)) (R.pot (logH B)) _ hpA hpB hpL _
    (mIntegrableCont _ _ (hcons _ hpA) _ continuous_const)
    (mIntegrableCont _ _ (hcons _ hpB) _ continuous_const)]
  refine ReciprocityTheory.AnForm.M.PLAux.mInt_congr fun j y hy => ?_
  congr 1
  refine locDens_congr_germ _ _ _ j y fun k => ?_
  cases k using Fin.cases
  · set x0 := (R.atlas.chart j).symm y
    have hopen : (R.atlas.chart j).target ∩ (R.atlas.chart j).symm ⁻¹' R.R.src (R.idx x0) ∈ 𝓝 y :=
      ((R.atlas.chart j).continuousOn_symm.isOpen_inter_preimage (R.atlas.chart j).open_target
        (R.R.isOpen_alt_bis _)).mem_nhds ⟨hy, R.mem_src_idx x0⟩
    filter_upwards [hopen] with y' hy'
    have hz : ∀ k, ∃ i, R.liftAt x0 ((R.atlas.chart j).symm y') ⟨k, i⟩ ≠ 0 := (R.liftAt_mem hy'.2).1
    show Real.log (A.h _ * B.h _) = Real.log (A.h _) + Real.log (B.h _)
    exact Real.log_mul (A.pos _ hz).ne' (B.pos _ hz).ne'
  · rfl

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

open MvPolynomial
open GroundTheory.Heights₂.Heights.NumbersDVR (MRing IsMultiHomog IsMultiProjPrime divCycle intNum cycEval)
open GroundTheory.Heights₂.Heights.FieldNumbers (CutRegular.full IntNumSymm.full IntNumAdd.full IntNumBase.full
  homFracDegZero)

set_option linter.unusedSectionVars false

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem zInt_cons_const (P : Ideal (MRing ι ℂ)) (e : ℕ) (c : ℝ) (φ : Fin e → MCone ι → ℝ)
    (g : MCone ι → ℝ) : zInt P (e + 1) (Fin.cons (fun _ => c) φ) g = 0 := by
  unfold zInt
  split_ifs with h
  · unfold Res.int
    rw [← ReciprocityTheory.AnForm.M.mIntConstPot h.some.atlas c (fun j => h.some.pot (φ j))
      (fun x => g (h.some.pt x))]
    refine ReciprocityTheory.AnForm.M.PLC.mInt_congr_phi _ _ _ (fun i a b => ?_) _
    cases i using Fin.cases <;> rfl
  · rfl

theorem zPts_anti {P W : Ideal (MRing ι ℂ)} (h : P ≤ W) {z : MCone ι} (hz : z ∈ zPts W) :
    z ∈ zPts P :=
  ⟨hz.1, fun f hf => hz.2 f (h hf)⟩

theorem isSmoothMetric_mono {P W : Ideal (MRing ι ℂ)} (h : P ≤ W) {L : HLine ι}
    (hL : IsSmoothMetric P L) : IsSmoothMetric W L := by
  intro z hz
  obtain ⟨U, hU, G, hG, hGU⟩ := hL z (zPts_anti h hz)
  exact ⟨U, hU, G, hG, fun w hw => hGU w ⟨hw.1, zPts_anti h hw.2⟩⟩

theorem isSmoothMetric_tensor {P : Ideal (MRing ι ℂ)} {A B : HLine ι} (hA : IsSmoothMetric P A)
    (hB : IsSmoothMetric P B) :
    IsSmoothMetric P (ReciprocityTheory.ChartRestriction.G.Geo.HermLine.tensor A B) := by
  intro z hz
  obtain ⟨U, hU, G, hG, hGU⟩ := hA z hz
  obtain ⟨V, hV, H, hH, hHV⟩ := hB z hz
  refine ⟨U ∩ V, Filter.inter_mem hU hV, G + H,
    (hG.mono Set.inter_subset_left).add (hH.mono Set.inter_subset_right), fun w hw => ?_⟩
  have hw0 : ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0 := hw.2.1
  show Real.log (A.h w * B.h w) = G w + H w
  rw [Real.log_mul (A.pos w hw0).ne' (B.pos w hw0).ne', ← hGU w ⟨hw.1.1, hw.2⟩,
    ← hHV w ⟨hw.1.2, hw.2⟩]
  rfl

theorem isSmoothFn_one (P : Ideal (MRing ι ℂ)) : IsSmoothFn P (fun _ => (1 : ℝ)) :=
  ⟨fun _ _ _ _ => rfl, fun _ _ => ⟨Set.univ, Filter.univ_mem, fun _ => 1, contDiffOn_const,
    fun _ _ => rfl⟩⟩

theorem cons_comp_finRotate {n : ℕ} (c : K → ℤ) (bs : Fin n → K → ℤ) :
    (Fin.cons c bs : Fin (n + 1) → K → ℤ) ∘ finRotate (n + 1) =
      Fin.snoc (α := fun _ => K → ℤ) bs c := by
  funext i
  cases i using Fin.lastCases with
  | last => simp
  | cast i =>
    simp only [Function.comp_apply, finRotate_apply, Fin.coeSucc_eq_succ, Fin.cons_succ,
      Fin.snoc_castSucc]

theorem degrees_step (hPL1 : PoincareLelongAlt.Statement) (hRes : ResExists.Statement) {e : ℕ}
    (ih : ∀ (W : Ideal (MRing ι ℂ)) (L : Fin e → HLine ι), IsProjVar W e →
      (∀ j, IsSmoothMetric W (L j)) →
      zInt W e (fun j => logH (L j)) (fun _ => 1) = (intNum ℂ W (fun j => (L j).a) : ℝ))
    {P : Ideal (MRing ι ℂ)} (hP : IsProjVar P (e + 1)) (L : Fin e → HLine ι)
    (hL : ∀ j, IsSmoothMetric P (L j)) (E : HLine ι) (c : K → ℕ) (hEc : ∀ k, E.a k = c k)
    (hE : IsSmoothMetric P E) :
    zInt P (e + 1) (Fin.cons (logH E) fun j => logH (L j)) (fun _ => 1) =
      (intNum ℂ P (Fin.cons (fun k => (c k : ℤ)) fun j => (L j).a) : ℝ) := by
  obtain ⟨s, hs, hsP⟩ := exists_form hP.1 c
  have hW : ∀ W ∈ comps P s, IsProjVar W e := fun W hW => isProjVar_of_mem_comps hP hs hsP hW
  have h1 := hPL1 K ι P e L E s (fun _ => 1) hP (hRes K ι P (e + 1) hP)
    (fun W hW' => hRes K ι W e (hW W hW')) hL hE ⟨c, hEc, hs, hsP⟩ (isSmoothFn_one P)
  rw [zInt_cons_const] at h1
  have hfin : (comps P s).Finite :=
    (Ideal.finite_minimalPrimes_of_isNoetherianRing _ (P ⊔ Ideal.span {s})).subset fun W h => h.1
  have hsupp : Function.support (fun W => divCycle P s W * intNum ℂ W fun j => (L j).a) ⊆
      (hfin.toFinset : Set (Ideal (MRing ι ℂ))) := by
    intro W hW
    rw [Set.Finite.coe_toFinset]
    by_contra h
    exact hW (by simp only [divCycle, dif_neg (show ¬ (W ∈ (P ⊔ Ideal.span {s}).minimalPrimes ∧
      GroundTheory.Heights₂.Heights.NumbersDVR.IsRelevant W) from h), zero_mul])
  have hsum : (∑ᶠ W ∈ comps P s, (divCycle P s W : ℝ) * zInt W e (fun j => logH (L j)) (fun _ => 1)) =
      ((cycEval (fun W => intNum ℂ W fun j => (L j).a) (divCycle P s) : ℤ) : ℝ) := by
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin, cycEval, finsum_eq_sum_of_support_subset _ hsupp]
    push_cast
    refine Finset.sum_congr rfl fun W hWm => ?_
    rw [Set.Finite.mem_toFinset] at hWm
    rw [ih W L (hW W hWm) fun j => isSmoothMetric_mono
      (le_sup_left.trans hWm.1.1.2) (hL j)]
  have hcut := CutRegular.full ℂ K ι P hP.1 e (relDim_of_isProjVar hP) c s hs hsP fun j => (L j).a
  have hsymm := IntNumSymm.full ℂ K ι P (e + 1) (Fin.cons (fun k => (c k : ℤ)) fun j => (L j).a)
    (finRotate (e + 1))
  rw [cons_comp_finRotate, hcut] at hsymm
  rw [← hsymm]
  linarith

theorem degrees_of (hPL1 : PoincareLelongAlt.Statement) (hRes : ResExists.Statement) (hPt : ZIntPoint.Statement) (e : ℕ) :
    ∀ (P : Ideal (MRing ι ℂ)) (L : Fin e → HLine ι), IsProjVar P e → (∀ j, IsSmoothMetric P (L j)) →
      zInt P e (fun j => logH (L j)) (fun _ => 1) = (intNum ℂ P (fun j => (L j).a) : ℝ) := by
  induction e with
  | zero =>
    intro P L hP _
    rw [hPt K ι P _ hP (hRes K ι P 0 hP)]
    have hrel : GroundTheory.Heights₂.Heights.FieldNumbers.relDim P = 0 := by
      rw [relDim_of_isProjVar hP]
      rfl
    obtain ⟨hfd, hb⟩ := IntNumBase.full ℂ K ι P hP.1 hrel
    have := hP.1.isPrime
    have hbot : homFracDegZero P = ⊥ := IntermediateField.eq_bot_of_isAlgClosed_of_isAlgebraic _
    have h1 : Module.finrank ℂ (homFracDegZero P) = 1 := IntermediateField.finrank_eq_one_iff.mpr hbot
    have hL0 : (fun j => (L j).a) = (![] : Fin 0 → K → ℤ) := Subsingleton.elim _ _
    rw [hL0, hb, h1]
    norm_num
  | succ e ih =>
    intro P M hP hM
    set A := M 0
    set L : Fin e → HLine ι := fun j => M j.succ
    have hL : ∀ j, IsSmoothMetric P (L j) := fun j => hM j.succ
    have hlog : (fun j => logH (M j)) = Fin.cons (logH A) fun j => logH (L j) := by
      funext j
      cases j using Fin.cases <;> rfl
    have hdeg : (fun j => (M j).a) = (Fin.cons A.a fun j => (L j).a : Fin (e + 1) → K → ℤ) := by
      funext j
      cases j using Fin.cases <;> rfl
    rw [hlog, hdeg]
    have ih' : ∀ (W : Ideal (MRing ι ℂ)) (L : Fin e → HLine ι), IsProjVar W e →
        (∀ j, IsSmoothMetric W (L j)) →
        zInt W e (fun j => logH (L j)) (fun _ => 1) = (intNum ℂ W (fun j => (L j).a) : ℝ) := ih
    let b : K → ℕ := fun k => (-(A.a k)).toNat
    let B : HLine ι := ReciprocityTheory.ChartRestriction.G.Geo.HermLine.sqMetric b
    have hB : IsSmoothMetric P B :=
      isSmoothMetric_of_isSmoothHerm P B (ReciprocityTheory.ChartRestriction.G.Geo.isSmoothHerm_sqMetric b)
    have hA : IsSmoothMetric P A := hM 0
    let c : K → ℕ := fun k => (A.a k + b k).toNat
    have hc : ∀ k, (ReciprocityTheory.ChartRestriction.G.Geo.HermLine.tensor A B).a k = c k := by
      intro k
      show A.a k + (b k : ℤ) = ((A.a k + b k).toNat : ℤ)
      simp only [b]
      omega
    have hC := degrees_step hPL1 hRes ih' hP L hL _ c hc (isSmoothMetric_tensor hA hB)
    have hBs := degrees_step hPL1 hRes ih' hP L hL B b (fun k => rfl) hB
    have hsum := ZIntAdd.proof K ι P e L A B hP (hRes K ι P (e + 1) hP) hL hA hB
    have hadd := IntNumAdd.full ℂ K ι P hP.1.multiHomog hP.1.relevant (e + 1) (relDim_of_isProjVar hP)
      (Fin.cons A.a fun j => (L j).a) 0 A.a (fun k => (b k : ℤ))
    simp only [Fin.update_cons_zero] at hadd
    have hcs : (fun k => ((c k : ℕ) : ℤ)) = A.a + fun k => (b k : ℤ) := by
      funext k
      simp only [c, b, Pi.add_apply]
      omega
    rw [hcs, hadd] at hC
    push_cast at hC
    linarith

theorem Degrees.proof (hPL1 : PoincareLelongAlt.Statement) (hRes : ResExists.Statement) (hPt : ZIntPoint.Statement) :
    Degrees.Statement := by
  intro K _ _ ι _ P e L hP _ hL
  exact degrees_of hPL1 hRes hPt e P L hP hL

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
end
end
