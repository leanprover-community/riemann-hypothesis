import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJABddKap
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJABddGen
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJABddSSnDatumBd
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJABddSSnChain
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJABddKapTP
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJABddKapNrmW
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSnGeom
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSnRepDatumUnit
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAGaugeLines
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRhoExists
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJABddScalBound
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SlicesFiniteRegularityBuilt
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ModelPlaceBuilt2OfHat
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatOpRFinal

section
open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JA

open NumberField Formalism.FourierDecayAlt.P.CutMP

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem jABddKapQQ_of_kapRealiser (hR : KapRealiser) : JABddKapQQ := by
  obtain ⟨K, hK, hR⟩ := hR
  refine ⟨K, hK, ?_⟩
  intro Cc Cb hCc hCb E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v e L hFr hGa hQQ hL b hb
  obtain ⟨κ, rfl⟩ := hb
  obtain ⟨c, ca, hadj, hc, hca, he, hea, hbc, hbca, hbig⟩ :=
    hR Cc Cb hCc hCb E Wp Wq S T f χ ν' m₀ top A₀ hB v e hFr hGa hQQ κ
  refine ⟨SSn.orderZeroDifferentialOperator S v c ca hadj, SSn.order_zero_operator_order, ⟨?_, ?_⟩, ?_, fun J hJ => ⟨?_, ?_, ?_⟩⟩
  · intro Tm hTm
    simp only [SSn.orderZeroDifferentialOperator, List.mem_singleton] at hTm
    subst hTm
    exact ⟨hc, hca⟩
  · intro p hp f' _ g hg
    rw [SSn.order_zero_operator_apply, SSn.order_zero_operator_apply]
    exact he p hp g hg.1 _
  · intro Tm hTm ε hε m
    simp only [SSn.orderZeroDifferentialOperator, List.mem_singleton] at hTm
    subst hTm
    obtain ⟨C1, h1⟩ := hbc ε hε m
    obtain ⟨C2, h2⟩ := hbca ε hε m
    refine ⟨max C1 C2, fun u w hu hw hl g hg hG => ⟨?_, ?_⟩⟩
    · have hpow : 0 ≤ B.gN g ^ (Cb * ((S.G.r : ℝ) + 1) * m) := Real.rpow_nonneg (Real.sqrt_nonneg _) _
      rw [zero_add]
      exact (h1 u w hu hw hl g hg hG).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hpow)
    · have hpow : 0 ≤ B.gN g ^ (Cb * ((S.G.r : ℝ) + 1) * m) := Real.rpow_nonneg (Real.sqrt_nonneg _) _
      rw [zero_add]
      exact (h2 u w hu hw hl g hg hG).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hpow)
  · rw [SSn.order_zero_operator_apply]; exact SSn.equivariant_coefficient_preserves_forms hc he hJ
  · rw [SSn.order_zero_operator_adjoint]; exact SSn.equivariant_coefficient_preserves_forms hca hea hJ
  · rw [SSn.order_zero_operator_apply]
    exact trJ_kap_of_bigCell S T v e κ c hbig J

theorem jABddKapQQ_of_typeProj (hB : DatumBd) (hG : SSn.SSnGeom) (hP : TypeProj) : JABddKapQQ :=
  jABddKapQQ_of_kapRealiser (kapRealiser_of_typeProj hB hG hP)

end

end Formalism.FourierDecayAlt.P.CutMP.JA
end

section
namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.ChainPf

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

structure Tm (k r : ℕ) where
  j : ℕ
  ws : Fin j → List (Bool × Mat k r)

variable {k r : ℕ} {V E' : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup E'] [NormedSpace ℂ E']

def tval (Ψ : V → E') (F : Mat k r → V) (t : Tm k r) (g : Mat k r) : E' :=
  iteratedFDeriv ℝ t.j Ψ (F g) (fun i => Dw (t.ws i) F g)

def tnext (x : Bool × Mat k r) (t : Tm k r) : List (Tm k r) :=
  ⟨t.j + 1, Fin.cons [x] t.ws⟩ :: List.ofFn fun i : Fin t.j => (⟨t.j, Function.update t.ws i (x :: t.ws i)⟩ : Tm k r)

theorem hasDerivAt_list_sum {ι : Type} (l : List ι) (f : ι → ℝ → E') (f' : ι → E')
    (h : ∀ i ∈ l, HasDerivAt (f i) (f' i) 0) :
    HasDerivAt (fun s => (l.map fun i => f i s).sum) (l.map f').sum 0 := by
  induction l with
  | nil => simpa using hasDerivAt_const (0 : ℝ) (0 : E')
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (h a (by simp)).add (ih fun i hi => h i (by simp [hi]))

theorem list_sum_flatMap {ι κ : Type} (l : List ι) (f : ι → List κ) (g : κ → E') :
    ((l.flatMap f).map g).sum = (l.map fun i => ((f i).map g).sum).sum := by
  induction l with
  | nil => simp
  | cons a l ih => rw [List.flatMap_cons, List.map_append, List.sum_append, ih, List.map_cons, List.sum_cons]

theorem tval_hasDerivAt {Ψ : V → E'} (hΨ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ψ) {F : Mat k r → V}
    {U : Set (Mat k r)} (hF : CkOn ⊤ (U ∩ GV k r) F) {x : Bool × Mat k r} (hx : inLie k r x.2)
    (t : Tm k r) (hws : ∀ i, ∀ y ∈ t.ws i, inLie k r y.2) {g : Mat k r} (hgU : g ∈ U) (hg : g ∈ GV k r) :
    HasDerivAt (fun s : ℝ => tval Ψ F t (crv x g s)) (((tnext x t).map fun t' => tval Ψ F t' g).sum) 0 := by
  have hg' : g ∈ U ∩ GV k r := ⟨hgU, hg⟩
  have hF1 : ∀ n : ℕ∞, CkOn n (U ∩ GV k r) F := fun n => CkOn_mono le_top hF
  have hA : HasDerivAt (fun s : ℝ => iteratedFDeriv ℝ t.j Ψ (F (crv x g s)))
      (fderiv ℝ (iteratedFDeriv ℝ t.j Ψ) (F g) (Dx x F g)) 0 := by
    have h1 := CkOn_diff hx (hF1 1) hg' hg
    have hlt : ((t.j : ℕ) : WithTop ℕ∞) < ((⊤ : ℕ∞) : WithTop ℕ∞) :=
      WithTop.coe_lt_coe.mpr (ENat.coe_lt_top _)
    have h2 : HasFDerivAt (iteratedFDeriv ℝ t.j Ψ) (fderiv ℝ (iteratedFDeriv ℝ t.j Ψ) (F g))
        (F (crv x g 0)) := by
      rw [crv_zero]
      exact ((hΨ.differentiable_iteratedFDeriv hlt) (F g)).hasFDerivAt
    exact h2.comp_hasDerivAt (0 : ℝ) h1
  have hv : ∀ i, HasDerivAt (fun s : ℝ => Dw (t.ws i) F (crv x g s)) (Dw (x :: t.ws i) F g) 0 := by
    intro i
    exact CkOn_diff hx (CkOn_Dw (hws i) (hF1 _)) hg' hg
  have hD := (hA.hasFDerivAt).continuousMultilinearMap_apply (fun i => (hv i).hasFDerivAt)
  refine hD.hasDerivAt.congr_deriv ?_
  simp only [crv_zero, ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.one_apply, one_smul, ContinuousMultilinearMap.apply_apply,
    ContinuousMultilinearMap.toContinuousLinearMap_apply, ContinuousLinearMap.toSpanSingleton_apply]
  simp only [tnext, List.map_cons, List.sum_cons, List.map_ofFn, List.sum_ofFn]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Function.comp_apply]
  congr 1
  funext l
  by_cases h : l = i
  · subst h
    simp
  · simp [Function.update_apply, h]

theorem expand {Ψ : V → E'} (hΨ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ψ) {F : Mat k r → V}
    {U : Set (Mat k r)} (hU : IsOpen U) (hF : CkOn ⊤ (U ∩ GV k r) F) :
    ∀ w : List (Bool × Mat k r), (∀ y ∈ w, inLie k r y.2) →
      ∃ ts : List (Tm k r), ts.length ≤ (w.length + 1).factorial ∧
        (∀ t ∈ ts, t.j ≤ w.length ∧ (∑ i, (t.ws i).length) = w.length ∧ ∀ i, (t.ws i).Sublist w) ∧
        ∀ g ∈ U, g ∈ GV k r → Dw w (fun g => Ψ (F g)) g = (ts.map fun t => tval Ψ F t g).sum := by
  intro w
  induction w with
  | nil =>
    intro _
    refine ⟨[⟨0, Fin.elim0⟩], by simp, ?_, ?_⟩
    · intro t ht
      simp only [List.mem_singleton] at ht
      subst ht
      exact ⟨le_rfl, by simp, fun i => i.elim0⟩
    · intro g _ _
      simp [tval, Dw]
  | cons x w ih =>
    intro hw
    obtain ⟨ts, hlen, hts, hval⟩ := ih (fun y hy => hw y (List.mem_cons_of_mem _ hy))
    have hx : inLie k r x.2 := hw x (by simp)
    refine ⟨ts.flatMap (tnext x), ?_, ?_, ?_⟩
    · have hl : ∀ t ∈ ts, (tnext x t).length ≤ w.length + 1 := by
        intro t ht
        simp only [tnext, List.length_cons, List.length_ofFn]
        have := (hts t ht).1
        omega
      have hs : (ts.map fun t => (tnext x t).length).sum ≤ (ts.map fun _ => w.length + 1).sum :=
        List.sum_le_sum hl
      rw [List.map_const', List.sum_replicate, smul_eq_mul] at hs
      rw [List.length_flatMap, List.length_cons, Nat.factorial_succ]
      calc _ ≤ ts.length * (w.length + 1) := hs
        _ ≤ (w.length + 1).factorial * (w.length + 1 + 1) := Nat.mul_le_mul hlen (by omega)
        _ = (w.length + 1 + 1) * (w.length + 1).factorial := Nat.mul_comm _ _
    · intro t' ht'
      obtain ⟨t, ht, ht'⟩ := List.mem_flatMap.mp ht'
      obtain ⟨hj, hsum, hsub⟩ := hts t ht
      simp only [tnext, List.mem_cons, List.mem_ofFn] at ht'
      rcases ht' with rfl | ⟨i, rfl⟩
      · refine ⟨by simp only [List.length_cons]; omega, ?_, ?_⟩
        · simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, List.length_cons, List.length_nil, hsum]
          omega
        · intro i
          refine Fin.cases ?_ (fun i => ?_) i
          · simp
          · simpa using (hsub i).cons x
      · refine ⟨by simp only [List.length_cons]; omega, ?_, ?_⟩
        · have e : ∀ l, (Function.update t.ws i (x :: t.ws i) l).length = (t.ws l).length + if l = i then 1 else 0 := by
            intro l
            by_cases h : l = i
            · subst h
              simp
            · simp [Function.update_apply, h]
          simp only [e, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true, hsum,
            List.length_cons]
        · intro l
          by_cases h : l = i
          · simpa [h] using (hsub i).cons₂ x
          · simpa [Function.update_apply, h] using (hsub l).cons x
    · intro g hgU hg
      show Dx x (Dw w (fun g => Ψ (F g))) g = _
      rw [Dx_eq]
      have hev : Filter.EventuallyEq (nhds (0 : ℝ)) (fun s : ℝ => Dw w (fun g => Ψ (F g)) (crv x g s))
          (fun s => (ts.map fun t => tval Ψ F t (crv x g s)).sum) := by
        filter_upwards [crv_ev (x := x) hU hgU] with s hs
        exact hval _ hs (crv_mem hx hg s)
      rw [hev.deriv_eq, list_sum_flatMap]
      exact (hasDerivAt_list_sum ts (fun t s => tval Ψ F t (crv x g s))
        (fun t => ((tnext x t).map fun t' => tval Ψ F t' g).sum)
        (fun t ht => tval_hasDerivAt hΨ hF hx t
          (fun i y hy => hw y (List.mem_cons_of_mem _ (((hts t ht).2.2 i).subset hy))) hgU hg)).deriv

theorem chain_bound_holds : Formalism.FourierDecayAlt.P.CutMP.JA.SSn.ChainBd := by
  unfold Formalism.FourierDecayAlt.P.CutMP.JA.SSn.ChainBd
  intro k r V E' _ _ _ _ _ Ψ hΨ F U K hU hF hKU hKG Bg hBg hyp m
  classical
  obtain ⟨C0, hC0⟩ := hyp 0
  have hFb : ∀ g ∈ K, ‖F g‖ ≤ C0 := by
    intro g hg
    have := hC0 [] [] (by simp) (by simp) (by simp) g hg
    simpa [dLR, Rw] using this
  have hΨb : ∀ j : ℕ, ∃ B, ∀ y : V, ‖y‖ ≤ C0 → ‖iteratedFDeriv ℝ j Ψ y‖ ≤ B := by
    intro j
    have hc : Continuous (fun y => iteratedFDeriv ℝ j Ψ y) :=
      hΨ.continuous_iteratedFDeriv (WithTop.coe_le_coe.mpr le_top)
    obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : V) C0).exists_bound_of_continuousOn hc.continuousOn
    exact ⟨B, fun y hy => hB y (mem_closedBall_zero_iff.mpr hy)⟩
  choose Bj hBj using hΨb
  choose Cl hCl using hyp
  obtain ⟨Bs, hBs⟩ : ∃ Bs : ℝ, Bs = ∑ j ∈ Finset.range (m + 1), |Bj j| := ⟨_, rfl⟩
  obtain ⟨Cs, hCs⟩ : ∃ Cs : ℝ, Cs = 1 + ∑ l ∈ Finset.range (m + 1), |Cl l| := ⟨_, rfl⟩
  have hBs0 : 0 ≤ Bs := by
    rw [hBs]
    exact Finset.sum_nonneg fun j _ => abs_nonneg _
  have hCs1 : 1 ≤ Cs := by
    have := Finset.sum_nonneg (fun l (_ : l ∈ Finset.range (m + 1)) => abs_nonneg (Cl l))
    rw [hCs]
    linarith
  have hBj' : ∀ j ≤ m, Bj j ≤ Bs := by
    intro j hj
    rw [hBs]
    exact (le_abs_self _).trans (Finset.single_le_sum (f := fun j => |Bj j|) (fun j _ => abs_nonneg _)
      (Finset.mem_range.mpr (by omega)))
  have hCl' : ∀ l ≤ m, Cl l ≤ Cs := by
    intro l hl
    have := (le_abs_self (Cl l)).trans (Finset.single_le_sum (f := fun l => |Cl l|) (fun l _ => abs_nonneg _)
      (Finset.mem_range.mpr (by omega : l < m + 1)))
    rw [hCs]
    linarith
  refine ⟨(m + 1).factorial * Bs * Cs ^ m, ?_⟩
  intro u v hu hv huv g hg
  have hgG := hKG hg
  have hg1 : 1 ≤ gN g := gN_ge_one hgG
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = gN g ^ Bg := ⟨_, rfl⟩
  have ha1 : 1 ≤ a := by
    rw [ha]
    exact Real.one_le_rpow hg1 hBg
  have hpow : ∀ l : ℕ, gN g ^ (Bg * l) = a ^ l := by
    intro l
    rw [Real.rpow_mul (by linarith), Real.rpow_natCast, ha]
  have hsub : ∀ s : List (Bool × Mat k r), s.Sublist (wL u ++ wR v) → ‖Dw s F g‖ ≤ Cs * a ^ s.length := by
    intro s hs
    unfold wL wR at hs
    obtain ⟨r1, r2, rfl, h1, h2⟩ := List.sublist_append_iff.mp hs
    obtain ⟨u', hu', rfl⟩ := List.sublist_map_iff.mp h1
    obtain ⟨v', hv', rfl⟩ := List.sublist_map_iff.mp h2
    have hl : u'.length + v'.length ≤ m := by
      have := hu'.length_le
      have := hv'.length_le
      omega
    have e : Dw (u'.map (Prod.mk true) ++ v'.map (Prod.mk false)) F g = dLR u' v' F g := by
      rw [dLR_eq]
      rfl
    rw [e]
    have hb := hCl (u'.length + v'.length) u' v' (fun X hX => hu X (hu'.subset hX))
      (fun X hX => hv X (hv'.subset hX)) le_rfl g hg
    rw [hpow] at hb
    have hlen : (u'.map (Prod.mk true) ++ v'.map (Prod.mk false)).length = u'.length + v'.length := by simp
    rw [hlen]
    calc ‖dLR u' v' F g‖ ≤ Cl (u'.length + v'.length) * a ^ (u'.length + v'.length) := hb
      _ ≤ Cs * a ^ (u'.length + v'.length) :=
        mul_le_mul_of_nonneg_right (hCl' _ hl) (pow_nonneg (by linarith) _)
  rw [dLR_eq]
  have hw : ∀ y ∈ wL u ++ wR v, inLie k r y.2 := by
    intro y hy
    simp only [wL, wR, List.mem_append, List.mem_map] at hy
    rcases hy with ⟨X, hX, rfl⟩ | ⟨X, hX, rfl⟩
    · exact (hu X hX).1
    · exact (hv X hX).1
  obtain ⟨ts, hlen, hts, hval⟩ := expand hΨ hU hF (wL u ++ wR v) hw
  rw [hval g (hKU hg) hgG]
  have hL : (wL u ++ wR v).length ≤ m := by
    simp only [wL, wR, List.length_append, List.length_map]
    omega
  have hX : 0 ≤ Bs * Cs ^ m * gN g ^ (Bg * m) :=
    mul_nonneg (mul_nonneg hBs0 (pow_nonneg (by linarith) _)) (Real.rpow_nonneg (by linarith) _)
  have hterm : ∀ t ∈ ts, ‖tval Ψ F t g‖ ≤ Bs * Cs ^ m * gN g ^ (Bg * m) := by
    intro t ht
    obtain ⟨hj, hsum, hsl⟩ := hts t ht
    rw [hpow]
    unfold tval
    calc ‖iteratedFDeriv ℝ t.j Ψ (F g) (fun i => Dw (t.ws i) F g)‖
        ≤ ‖iteratedFDeriv ℝ t.j Ψ (F g)‖ * ∏ i, ‖Dw (t.ws i) F g‖ :=
          ContinuousMultilinearMap.le_opNorm _ _
      _ ≤ Bs * ∏ i, (Cs * a ^ (t.ws i).length) := by
          apply mul_le_mul ((hBj t.j (F g) (hFb g hg)).trans (hBj' _ (by omega)))
            (Finset.prod_le_prod (fun i _ => norm_nonneg _) (fun i _ => hsub _ (hsl i)))
            (Finset.prod_nonneg fun i _ => norm_nonneg _) hBs0
      _ = Bs * (Cs ^ t.j * a ^ (wL u ++ wR v).length) := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
            Finset.prod_pow_eq_pow_sum, hsum]
      _ ≤ Bs * (Cs ^ m * a ^ m) := by
          apply mul_le_mul_of_nonneg_left _ hBs0
          exact mul_le_mul (pow_le_pow_right₀ hCs1 (by omega)) (pow_le_pow_right₀ ha1 hL)
            (pow_nonneg (by linarith) _) (pow_nonneg (by linarith) _)
      _ = Bs * Cs ^ m * a ^ m := by ring
  have key : ∀ l : List (Tm k r), (∀ t ∈ l, ‖tval Ψ F t g‖ ≤ Bs * Cs ^ m * gN g ^ (Bg * m)) →
      ‖(l.map fun t => tval Ψ F t g).sum‖ ≤ l.length * (Bs * Cs ^ m * gN g ^ (Bg * m)) := by
    intro l
    induction l with
    | nil =>
      intro _
      simp
    | cons t l ih =>
      intro hl
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_succ]
      calc _ ≤ ‖tval Ψ F t g‖ + ‖(l.map fun t => tval Ψ F t g).sum‖ := norm_add_le _ _
        _ ≤ (Bs * Cs ^ m * gN g ^ (Bg * m)) + l.length * (Bs * Cs ^ m * gN g ^ (Bg * m)) :=
          add_le_add (hl t (by simp)) (ih fun t' ht' => hl t' (by simp [ht']))
        _ = _ := by ring
  have hfac : (ts.length : ℝ) ≤ ((m + 1).factorial : ℝ) := by
    exact_mod_cast hlen.trans (Nat.factorial_le (by omega))
  calc ‖(ts.map fun t => tval Ψ F t g).sum‖ ≤ ts.length * (Bs * Cs ^ m * gN g ^ (Bg * m)) := key ts hterm
    _ ≤ ((m + 1).factorial : ℝ) * (Bs * Cs ^ m * gN g ^ (Bg * m)) := mul_le_mul_of_nonneg_right hfac hX
    _ = _ := by ring

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.ChainPf
end

section
open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JA

theorem datum_bound_holds : DatumBd := datumBd_of_chain SSn.ChainPf.chain_bound_holds

theorem jABddKapQQ_of_leaves (hG : SSn.SSnGeom) (hP : TypeProj) : JABddKapQQ :=
  jABddKapQQ_of_typeProj datum_bound_holds hG hP

theorem jABddKapQQ_of_cut (hG : SSn.SSnGeom) (hPE : PRho.PRhoExists) (hGL : PRho.GaugeLines)
    (hDU : SSn.Rep.DatumUnit) (hNW : NrmWFacts) : JABddKapQQ :=
  jABddKapQQ_of_leaves hG (typeProj_of hPE hGL hDU hNW)

end Formalism.FourierDecayAlt.P.CutMP.JA
end

section
namespace Formalism.FourierDecayAlt.P.CutMP.JA

theorem jABddKapQQ_of_shared (hG : SSn.SSnGeom) (hPE : PRho.PRhoExists) (hGL : PRho.GaugeLines)
    (hDU : SSn.Rep.DatumUnit) : JABddKapQQ :=
  jABddKapQQ_of_cut hG hPE hGL hDU weighted_norm_facts_hold

end Formalism.FourierDecayAlt.P.CutMP.JA
end

section
open Formalism.FourierDecayAlt

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn

open NumberField Formalism.FourierDecayAlt.P.CutMP

theorem sSnAssemble_of (hC : JA.DatumCompose) : SSnAssemble := by
  intro hG hR
  obtain ⟨K1, hK1, hG⟩ := hG
  obtain ⟨K2, hK2, hR⟩ := hR
  refine ⟨max K1 K2, le_max_of_le_left hK1, ?_⟩
  intro Cc Cb hCc hCb E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v e hFr hGa hQQ l hl
  obtain ⟨a, a', ι, hD⟩ := hG Cc Cb (le_trans (le_max_left _ _) hCc) (le_trans (le_max_left _ _) hCb)
    E Wp Wq S T f χ ν' m₀ top A₀ hB v
  obtain ⟨Φ, Φa, hΦ⟩ := hR Cc (le_trans (le_max_right _ _) hCc) E Wp Wq S T f χ ν' m₀ top A₀ hB v e hFr hGa hQQ l hl
  have hCb0 : 0 ≤ Cb := le_trans (le_max_of_le_left hK1) hCb
  have hBg : 0 ≤ Cb * ((S.G.r : ℝ) + 1) := mul_nonneg hCb0 (by positivity)
  obtain ⟨c, ca, hadj, hc, hca, he, hea, hb, hba, hcv⟩ :=
    hC E Wp Wq S T v _ a a' ι Φ Φa hBg hD ⟨hΦ.1, hΦ.2.1, hΦ.2.2.1, hΦ.2.2.2.1⟩
  refine ⟨c, ca, hadj, hc, hca, he, hea, hb, hba, ?_⟩
  have hPl : Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' :=
    (hB.1.2.2.2.1.2 v).2.2.2.1
  have hTT : (D.parOf S v).TT = Formalism.QuantumDeterminants.Tz S.G.k S.G.r (T v).base.z * Formalism.QuantumDeterminants.Tz S.G.k S.G.r (T v).base.z' := by
    rw [hPl.2.2.2.1, hPl.2.2.2.2.1]; rfl
  intro q hq ρ π
  have hqD : q ∈ JF.QDom S.G.k S.G.r (T v).base.z (T v).base.z' := ⟨hq.1, hTT ▸ hq.2⟩
  have hG' := Formalism.FourierDecayAlt.P.BigCellHermitian.gqDom (T v).base hqD
  have hpos : B.gq (T v).base q ∈ B.GPos (T v).base := ⟨hG'.1, hG'.2.2⟩
  obtain ⟨h1, h2, h3⟩ := hD.2.2.2.2.2.2.2 q hq
  rw [hcv _ hpos, h1, h2, h3]
  exact hΦ.2.2.2.2 q hq ρ π

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn
end
end

section
open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn

theorem sSnRealiser_of (hCh : ChainBd) (hG : SSnGeom) (hR : SSnRep) : SSnRealiser :=
  sSnAssemble_of (JA.datumCompose_of (JA.datumBd_of_chain hCh)) hG hR

theorem jABddSSnQQ_of_leaves (hCh : ChainBd) (hG : SSnGeom) (hR : SSnRep) : JABddSSnQQ :=
  jABddSSnQQ_of real_to_bounded_holds (sSnRealiser_of hCh hG hR)

theorem jABddSSnStarQQ_of_leaves (hCh : ChainBd) (hG : SSnGeom) (hR : SSnRep) : JABddSSnStarQQ :=
  jABddSSnStarQQ_of real_to_bounded_holds (sSnRealiser_of hCh hG hR)

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn
end

section
open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JA

open NumberField Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.P.CutMP.JA.BStar Formalism.FourierDecayAlt.P.MAx2.Adj Formalism.FourierDecayAlt.P.MAx1.An Formalism.QuantumDeterminants
open scoped ComplexConjugate Matrix

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

section deriv

variable {k r : ℕ} {F F' : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedAddCommGroup F'] [NormedSpace ℂ F']

theorem ldV_rl (L : F →L[ℝ] F') (L' : F' →L[ℝ] F) (hL : ∀ y, L' (L y) = y) (X : B.Mat k r) (f : B.Mat k r → F) :
    B.LdV X (fun g => L (f g)) = fun g => L (B.LdV X f g) := by
  funext g
  unfold B.LdV
  exact P.JCTx6.Pos.deriv_cle_comp L L' hL (fun t : ℝ => f (NormedSpace.exp (-((t : ℂ) • X)) * g)) 0

theorem rdV_rl (L : F →L[ℝ] F') (L' : F' →L[ℝ] F) (hL : ∀ y, L' (L y) = y) (X : B.Mat k r) (f : B.Mat k r → F) :
    Formalism.REAL.RdV X (fun g => L (f g)) = fun g => L (Formalism.REAL.RdV X f g) := by
  funext g
  unfold Formalism.REAL.RdV
  exact P.JCTx6.Pos.deriv_cle_comp L L' hL (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) 0

theorem rw_rl (L : F →L[ℝ] F') (L' : F' →L[ℝ] F) (hL : ∀ y, L' (L y) = y) :
    ∀ (v : List (B.Mat k r)) (f : B.Mat k r → F), B.Rw v (fun g => L (f g)) = fun g => L (B.Rw v f g)
  | [], _ => rfl
  | X :: v, f => by
    show Formalism.REAL.RdV X (B.Rw v fun g => L (f g)) = fun g => L (Formalism.REAL.RdV X (B.Rw v f) g)
    rw [rw_rl L L' hL v f, rdV_rl L L' hL X]

theorem dLR_rl (L : F →L[ℝ] F') (L' : F' →L[ℝ] F) (hL : ∀ y, L' (L y) = y) (w : List (B.Mat k r)) :
    ∀ (u : List (B.Mat k r)) (f : B.Mat k r → F), B.dLR u w (fun g => L (f g)) = fun g => L (B.dLR u w f g)
  | [], f => rw_rl L L' hL w f
  | X :: u, f => by
    show B.LdV X (B.dLR u w fun g => L (f g)) = fun g => L (B.LdV X (B.dLR u w f) g)
    rw [dLR_rl L L' hL w u f, ldV_rl L L' hL X]

theorem dLR_conj (u w : List (B.Mat k r)) (f : B.Mat k r → ℂ) :
    B.dLR u w (fun g => conj (f g)) = fun g => conj (B.dLR u w f g) :=
  dLR_rl (Complex.conjCLE : ℂ →L[ℝ] ℂ) (Complex.conjCLE : ℂ →L[ℝ] ℂ) (fun y => by simp) w u f

theorem dLR_smulc (A : F) (u w : List (B.Mat k r)) (f : B.Mat k r → ℂ) :
    B.dLR u w (fun g => f g • A) = fun g => B.dLR u w f g • A := by
  by_cases hA : A = 0
  · subst hA; simp only [smul_zero]; exact Formalism.FourierDecayAlt.P.BetaSesquilinearity.dLR_zero u w
  obtain ⟨ℓ, -, hℓ⟩ := exists_dual_vector ℂ A (norm_ne_zero_iff.2 hA)
  have hn : ((‖A‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hA
  let L : ℂ →L[ℝ] F := ((ContinuousLinearMap.id ℂ ℂ).smulRight A).restrictScalars ℝ
  let L' : F →L[ℝ] ℂ := ((((‖A‖ : ℝ) : ℂ))⁻¹ • ℓ).restrictScalars ℝ
  have hL : ∀ y, L' (L y) = y := fun y => by
    simp only [L, L', ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply, map_smul, hℓ, smul_eq_mul]
    field_simp
    norm_cast
  exact dLR_rl L L' hL w u f

end deriv

theorem scalar_conjugation_transfer : JAScalConj := by
  intro k r Wp Wq _ _ _ _ D Bg φ hφ
  refine ⟨fun g₀ hg₀ => ?_, fun ε hε m => ?_⟩
  · obtain ⟨U, φ', hU, hg, hφ', he⟩ := hφ.1 g₀ hg₀
    refine ⟨U, fun g => conj (φ' g), hU, hg, ?_, fun g hgU hgG => by simp only; rw [he g hgU hgG]⟩
    exact (Complex.conjCLE : ℂ →L[ℝ] ℂ).contDiff.comp_contDiffOn hφ'
  · obtain ⟨C, hC⟩ := hφ.2 ε hε m
    refine ⟨C, fun u w hu hw hl g hg hG => ?_⟩
    rw [dLR_conj, Complex.norm_conj]
    exact hC u w hu hw hl g hg hG

section real

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
  [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
  [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]

theorem scal_real (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (v : Fin S.f) (hPl : Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π')
    (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (hFr : IsFrame S T v e) (Cb : ℝ)
    (φ : B.Mat S.G.k S.G.r → ℂ) (hφ : ScalOK (T v).base (Cb * ((S.G.r : ℝ) + 1)) φ)
    (hinv : ∀ p, (T v).base.inSS p → ∀ g, φ (B.sgs p g) = φ g)
    (β : (DQ (D.parOf S v)).R)
    (hval : ∀ (q : MA.E (D.parOf S v).r) (hq : q ∈ MA.Qset (D.parOf S v).r (D.parOf S v).TT),
      φ (B.gq (T v).base q) = evD (D.parOf S v) ⟨q, hq⟩ β) :
    BddReal S T v e Cb (Matrix.scalar (M.Ty (D.parOf S v)) ((DQ (D.parOf S v)).fnP β (cjD (D.parOf S v) β))) := by
  have hφc := scalar_conjugation_transfer _ _ _ _ (T v).base _ φ hφ
  refine SSn.real_to_bounded_holds E Wp Wq S T v hPl e Cb
    (fun g => φ g • ContinuousLinearMap.id ℂ (Wq (S.pl v) →L[ℂ] Wp (S.pl v)))
    (fun g => conj (φ g) • ContinuousLinearMap.id ℂ (Wq (S.pl v) →L[ℂ] Wp (S.pl v)))
    (fun ρ π q => if ρ = π then evD (D.parOf S v) q β else 0) _ hFr ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ ?_
  · intro x A B'
    simp only [B.hsInner, ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
      P.TBBx2.Tri.hsVec_smul, inner_smul_left, inner_smul_right, Complex.conj_conj]
  · intro g₀ hg₀
    obtain ⟨U, φ', hU, hg, hφ', he⟩ := hφ.1 g₀ hg₀
    exact ⟨U, fun g => φ' g • ContinuousLinearMap.id ℂ (Wq (S.pl v) →L[ℂ] Wp (S.pl v)), hU, hg,
      hφ'.smul contDiffOn_const, fun g hgU hgG => by simp only; rw [he g hgU hgG]⟩
  · intro g₀ hg₀
    obtain ⟨U, φ', hU, hg, hφ', he⟩ := hφc.1 g₀ hg₀
    exact ⟨U, fun g => φ' g • ContinuousLinearMap.id ℂ (Wq (S.pl v) →L[ℂ] Wp (S.pl v)), hU, hg,
      hφ'.smul contDiffOn_const, fun g hgU hgG => by
        show conj (φ g) • _ = φ' g • _
        rw [show conj (φ g) = φ' g from he g hgU hgG]⟩
  · intro p hp g _ X
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, hinv p hp g,
      ContinuousLinearMap.comp_smul, ContinuousLinearMap.smul_comp]
  · intro p hp g _ X
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, hinv p hp g,
      ContinuousLinearMap.comp_smul, ContinuousLinearMap.smul_comp]
  · intro ε hε m
    obtain ⟨C, hC⟩ := hφ.2 ε hε m
    refine ⟨C, fun u w hu hw hl g hg hG => ?_⟩
    rw [dLR_smulc]
    exact (norm_smul_le _ _).trans ((mul_le_of_le_one_right (norm_nonneg _) ContinuousLinearMap.norm_id_le).trans
      (hC u w hu hw hl g hg hG))
  · intro ε hε m
    obtain ⟨C, hC⟩ := hφc.2 ε hε m
    refine ⟨C, fun u w hu hw hl g hg hG => ?_⟩
    rw [dLR_smulc]
    exact (norm_smul_le _ _).trans ((mul_le_of_le_one_right (norm_nonneg _) ContinuousLinearMap.norm_id_le).trans
      (hC u w hu hw hl g hg hG))
  · intro q hq ρ π
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, P.TBBx2.Tri.hsVec_smul,
      inner_smul_right, (hFr.2 q.2 hq.2).2.1 ρ π, hval q hq]
    split_ifs <;> simp
  · intro ρ π
    by_cases h : ρ = π
    · subst h
      exact ⟨β, by rw [Matrix.scalar_apply, Matrix.diagonal_apply_eq], fun q => by simp⟩
    · refine ⟨0, ?_, fun q => by simp [h]⟩
      rw [Matrix.scalar_apply, Matrix.diagonal_apply_ne _ h, cjD_zero, multiplierPair_zero]

end real

section main

theorem phiR_sgs {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) {p : B.SS k r} (hp : D.inSS p)
    (g : B.Mat k r) : phiR k r D.z D.z' (B.sgs p g) = phiR k r D.z D.z' g := by
  unfold phiR; rw [P.BigCellZetaMinors.dmin_sgs D hp, P.BigCellZetaMinors.dmin_sgs D hp]

theorem phiD_sgs {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) {p : B.SS k r} (hp : D.inSS p)
    (g : B.Mat k r) : phiD k r D.z D.z' (B.sgs p g) = phiD k r D.z D.z' g := by
  unfold phiD; rw [P.BigCellZetaMinors.dmin_sgs D hp]

theorem dmin_gq {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) {q : (Fin r → ℂ) × ℂ}
    (hq : q ∈ JF.QDom k r D.z D.z') :
    Dmin k r D.z D.z' (B.gq D q) ⟨r, by omega⟩ = ∏ a, q.1 a ∧
      Dmin k r D.z D.z' (B.gq D q) (Fin.last (r + 1)) = q.2 * ∏ a, q.1 a := by
  have h1 : Dmin k r D.z D.z' (B.gq D q) ⟨r, by omega⟩ = ∏ a, q.1 a := by
    have := (bigCellMinors k r D.z D.z' q.1 (D.μsec q.2) D.z_mem D.z'_mem).1 (Fin.last r)
    simp only [Fin.val_last] at this
    rw [show B.gq D q = bigCell k r q.1 (D.μsec q.2) from rfl, this]
    exact Finset.prod_congr (by ext a; simp) fun _ _ => rfl
  refine ⟨h1, ?_⟩
  have hz := P.BigCellZetaMinors.zeta_gq D hq
  have hne : Dmin k r D.z D.z' (B.gq D q) ⟨r, by omega⟩ ≠ 0 := by
    rw [h1]; exact Finset.prod_ne_zero_iff.2 fun a _ => hq.1 a
  unfold zeta at hz
  rw [← hz, ← h1, div_mul_cancel₀ _ hne]

theorem bounded_scalar_transfer_holds : JABddScal := by
  obtain ⟨K, hK0, hK⟩ := scalar_transfer_bound_holds
  refine ⟨K, hK0, fun Cc Cb _ hCb E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v e L hFr _ hL b hb => ?_⟩
  have hPl : Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' :=
    (hB.1.2.2.2.1.2 v).2.2.2.1
  have hT : Tz S.G.k S.G.r (T v).base.z = S.T := hPl.2.2.2.1
  have hT' : Tz S.G.k S.G.r (T v).base.z' = S.T' := hPl.2.2.2.2.1
  have hTT : Tz S.G.k S.G.r (T v).base.z * Tz S.G.k S.G.r (T v).base.z' = (D.parOf S v).TT := by
    rw [hT, hT']; rfl
  have hTpos : 0 < (D.parOf S v).TT := by
    rw [← hTT]; exact mul_pos (T v).base.T_pos (T v).base.T'_pos
  have hT0 := hTpos.le
  have hQD : ∀ q ∈ MA.Qset (D.parOf S v).r (D.parOf S v).TT, q ∈ JF.QDom S.G.k S.G.r (T v).base.z (T v).base.z' :=
    fun q hq => ⟨hq.1, by rw [hTT]; exact hq.2⟩
  have hBg : K * ((S.G.r : ℝ) + 1) ≤ Cb * ((S.G.r : ℝ) + 1) :=
    mul_le_mul_of_nonneg_right hCb (by positivity)
  obtain ⟨hR, hD⟩ := hK S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)) (T v).base _ hBg
  have hRc := scalar_conjugation_transfer _ _ _ _ (T v).base _ _ hR
  have hDc := scalar_conjugation_transfer _ _ _ _ (T v).base _ _ hD
  obtain ⟨-, -, hc, hci, hcb, hcbi, hz, hzi, hzb, hzbi, -, -, -, -, -⟩ := hL

  have vR : ∀ q (hq : q ∈ MA.Qset (D.parOf S v).r (D.parOf S v).TT),
      phiR S.G.k S.G.r (T v).base.z (T v).base.z' (B.gq (T v).base q) = (q.2)⁻¹ := fun q hq => by
    have hz' := P.BigCellZetaMinors.zeta_gq (T v).base (hQD q hq)
    unfold zeta at hz'
    unfold phiR
    rw [← hz', inv_div]
  have vD : ∀ q (hq : q ∈ MA.Qset (D.parOf S v).r (D.parOf S v).TT),
      phiD S.G.k S.G.r (T v).base.z (T v).base.z' (B.gq (T v).base q) =
        (∏ a, q.1 a) * q.2 * ((conj q.2)⁻¹ * ∏ a, (conj (q.1 a))⁻¹) := fun q hq => by
    have h := (dmin_gq (T v).base (hQD q hq)).2
    have hz0 : q.2 ≠ 0 := BStar.z_ne hT0 ⟨q, hq⟩
    have hc0 : ∀ a, q.1 a ≠ 0 := hq.1
    unfold phiD
    rw [h, map_mul, map_prod, Finset.prod_inv_distrib, div_eq_mul_inv, mul_inv]
    ring
  rcases hb with rfl | rfl | rfl | rfl
  · rw [BStar.rep_zi hzi, ← BStar.cjD_izi hT0]
    refine scal_real S T v hPl e hFr Cb _ hR (fun p hp g => phiR_sgs _ hp g) _ fun q hq => ?_
    rw [vR q hq, BStar.evD_inv _ hT0, coordE_vz]
  · rw [BStar.rep_zbi hzbi, ← BStar.cjD_izbi hT0]
    refine scal_real S T v hPl e hFr Cb _ hRc (fun p hp g => by simp only [phiR_sgs _ hp g]) _ fun q hq => ?_
    simp only
    rw [vR q hq, BStar.evD_inv _ hT0, coordE_vzb, map_inv₀]
  · have e1 : L.D * L.Dbi = Matrix.scalar (M.Ty (D.parOf S v))
        ((DQ (D.parOf S v)).fnP (βD (D.parOf S v)) (βDb (D.parOf S v))) := by
      rw [LevelData.D, LevelData.Dbi, rep_Dr hc, zeta_eq_scalar_matrix hz, rep_zbi hzbi, rep_Drbi hcbi, scalar_mul_fnP,
        scalar_mul_fnP, scalar_mul_fnP]; rfl
    rw [e1, ← BStar.cjD_βD hT0]
    refine scal_real S T v hPl e hFr Cb _ hD (fun p hp g => phiD_sgs _ hp g) _ fun q hq => ?_
    rw [vD q hq]
    simp only [βD, map_mul, map_prod, evaluation_of_coordinate_variable, BStar.evD_inv _ hT0, coordE_vc, coordE_vcb, coordE_vz, coordE_vzb]
  · have e2 : L.Db * L.Di = Matrix.scalar (M.Ty (D.parOf S v))
        ((DQ (D.parOf S v)).fnP (βDb (D.parOf S v)) (βD (D.parOf S v))) := by
      rw [LevelData.Db, LevelData.Di, rep_Drb hcb, rep_zb hzb, rep_zi hzi, rep_Dri hci, scalar_mul_fnP,
        scalar_mul_fnP, scalar_mul_fnP]; rfl
    rw [e2, ← BStar.cjD_βDb hT0]
    refine scal_real S T v hPl e hFr Cb _ hDc (fun p hp g => by simp only [phiD_sgs _ hp g]) _ fun q hq => ?_
    simp only
    rw [vD q hq, ← BStar.cjD_βD hT0, evD_cjD]
    simp only [βD, map_mul, map_prod, evaluation_of_coordinate_variable, BStar.evD_inv _ hT0, coordE_vc, coordE_vcb, coordE_vz, coordE_vzb]

end main

end

end Formalism.FourierDecayAlt.P.CutMP.JA
end

section
namespace Formalism.FourierDecayAlt.P.CutMP

theorem modelPlaceBuilt2_of_bdd (hJ : JfSmoothDS) (hG : Gauge.GC.GenTransfer) (hBdd : JA.JABddOpQQ) :
    Formalism.FourierDecayAlt.JCT.ModelPlaceBuilt2 :=
  modelPlaceBuilt2_of_hat hJ hG hat_quadratic_operator_holds hBdd

end Formalism.FourierDecayAlt.P.CutMP
end

section
namespace Formalism.FourierDecayAlt.P.CutMP.JA

theorem kappa_quadratic_bound_holds : JABddKapQQ :=
  jABddKapQQ_of_shared second_shift_geometry_holds rho_projection_existence gauge_lines_holds SSn.Rep.datum_unit_norm_holds

theorem jABddOpQQ_of_ssnRep (h : SSn.SSnRep) : JABddOpQQ :=
  jABddOpQQ_of_bddLeaves bounded_scalar_transfer_holds kappa_quadratic_bound_holds
    (SSn.jABddSSnQQ_of_leaves SSn.ChainPf.chain_bound_holds second_shift_geometry_holds h)
    (SSn.jABddSSnStarQQ_of_leaves SSn.ChainPf.chain_bound_holds second_shift_geometry_holds h)

end Formalism.FourierDecayAlt.P.CutMP.JA

namespace Formalism.FourierDecayAlt.P.CutMP

theorem modelPlaceBuilt2_of_ssnRep (hJ : JfSmoothDS) (hG : Gauge.GC.GenTransfer) (h : JA.SSn.SSnRep) :
    Formalism.FourierDecayAlt.JCT.ModelPlaceBuilt2 :=
  modelPlaceBuilt2_of_bdd hJ hG (JA.jABddOpQQ_of_ssnRep h)

end Formalism.FourierDecayAlt.P.CutMP
end
