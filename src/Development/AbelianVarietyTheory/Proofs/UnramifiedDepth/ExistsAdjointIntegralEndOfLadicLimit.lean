import Mathlib
import Formalism.LocalToGlobal.CharacterGerms.NondegenerateCharts
import Formalism.LocalToGlobal.CharacterGerms.RowTieSelf
import Formalism.LocalToGlobal.CharacterGerms.BlockAdmissibleChart
import Formalism.LocalToGlobal.CharacterGerms.NegMem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.GermLinearPartCoordinatePointZero
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.FormalGroupActionLimitsIntegralEndomorphismsStatement
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ConstantCoeffEv
import BuildAid.ForwardExisting

section
section
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.ActionLimit

open MvPowerSeries GlobalTheory.GaugeAdjoint

section Bound

variable {C : Type} [Field C] {V : VF C} {σ τ : Type}

def Low (V : VF C) (D : ℕ) (w : ℝ) (g : MvPowerSeries τ C) : Prop :=
  ∀ μ : τ →₀ ℕ, μ.degree ≤ D → V.Ge w (coeff μ g)

theorem Low.mono {D : ℕ} {w w' : ℝ} {g : MvPowerSeries τ C} (h : Low V D w g) (hw : w' ≤ w) :
    Low V D w' g := fun μ hμ => (h μ hμ).mono hw

theorem low_of_int {g : MvPowerSeries τ C} (h : IntS V g) (D : ℕ) : Low V D 0 g := fun μ _ => h μ

theorem low_zero (D : ℕ) (w : ℝ) : Low V D w (0 : MvPowerSeries τ C) := fun μ _ => by
  simpa using VF.Ge.zero (V := V) w

theorem low_one (D : ℕ) : Low V D 0 (1 : MvPowerSeries τ C) := fun μ _ => by
  classical
  rw [coeff_one]
  split_ifs
  exacts [VF.Ge.one, VF.Ge.zero 0]

theorem Low.add {D : ℕ} {w : ℝ} {g h : MvPowerSeries τ C} (hg : Low V D w g) (hh : Low V D w h) :
    Low V D w (g + h) := fun μ hμ => by
  rw [map_add]; exact (hg μ hμ).add (hh μ hμ)

theorem Low.mul {D : ℕ} {w w' : ℝ} {g h : MvPowerSeries τ C} (hg : Low V D w g) (hh : Low V D w' h) :
    Low V D (w + w') (g * h) := fun μ hμ => by
  classical
  rw [coeff_mul]
  refine VF.Ge.sum fun p hp => ?_
  have e : p.1.degree + p.2.degree = μ.degree := by
    rw [← map_add, Finset.HasAntidiagonal.mem_antidiagonal.mp hp]
  exact (hg _ (by omega)).mul (hh _ (by omega))

def Cong (V : VF C) (D : ℕ) (w : ℝ) (g h : MvPowerSeries τ C) : Prop :=
  Low V D 0 g ∧ Low V D 0 h ∧ Low V D w (g - h)

theorem cong_one (D : ℕ) (w : ℝ) : Cong V D w (1 : MvPowerSeries τ C) 1 :=
  ⟨low_one D, low_one D, by simpa using low_zero D w⟩

theorem Cong.mul {D : ℕ} {w : ℝ} {g h g' h' : MvPowerSeries τ C} (h1 : Cong V D w g h)
    (h2 : Cong V D w g' h') : Cong V D w (g * g') (h * h') := by
  refine ⟨by simpa using h1.1.mul h2.1, by simpa using h1.2.1.mul h2.2.1, ?_⟩
  have e : g * g' - h * h' = (g - h) * g' + h * (g' - h') := by ring
  rw [e]
  exact Low.add (by simpa using h1.2.2.mul h2.1) (by simpa using h1.2.1.mul h2.2.2)

theorem Cong.pow {D : ℕ} {w : ℝ} {g h : MvPowerSeries τ C} (h1 : Cong V D w g h) (n : ℕ) :
    Cong V D w (g ^ n) (h ^ n) := by
  induction n with
  | zero => simpa using cong_one D w
  | succ n ih => rw [pow_succ, pow_succ]; exact ih.mul h1

theorem cong_prod {D : ℕ} {w : ℝ} {a b : σ → MvPowerSeries τ C} (h : ∀ s, Cong V D w (a s) (b s))
    (e : σ →₀ ℕ) : Cong V D w (e.prod fun s n => a s ^ n) (e.prod fun s n => b s ^ n) := by
  classical
  unfold Finsupp.prod
  induction e.support using Finset.induction_on with
  | empty => simpa using cong_one D w
  | insert s S hs ih =>
    rw [Finset.prod_insert hs, Finset.prod_insert hs]
    exact ((h s).pow _).mul ih

theorem coeff_prod_high {a : σ → MvPowerSeries τ C} (ha : ∀ s, constantCoeff (a s) = 0)
    (e : σ →₀ ℕ) (μ : τ →₀ ℕ) (h : μ.degree < e.degree) :
    coeff μ (e.prod fun s n => a s ^ n) = 0 := by
  classical
  apply coeff_of_lt_order
  have key : ∀ S : Finset σ, ((∑ s ∈ S, e s : ℕ) : ℕ∞) ≤ (∏ s ∈ S, a s ^ e s).order := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp
    | insert s S hs ih =>
      rw [Finset.prod_insert hs, Finset.sum_insert hs, Nat.cast_add]
      exact le_trans (add_le_add (le_order_pow_of_constantCoeff_eq_zero _ (ha s)) ih) le_order_mul
  refine lt_of_lt_of_le ?_ (key e.support)
  exact_mod_cast h

theorem low_subst_sub [Finite σ] {D : ℕ} {w c : ℝ} {a b : σ → MvPowerSeries τ C}
    (ha : ∀ s, constantCoeff (a s) = 0) (hb : ∀ s, constantCoeff (b s) = 0)
    (h : ∀ s, Cong V D w (a s) (b s)) {f : MvPowerSeries σ C} (hf : Low V D c f) :
    Low V D (c + w) (subst a f - subst b f) := by
  intro μ hμ
  have hs := hasSubst_of_constantCoeff_zero ha
  have hs' := hasSubst_of_constantCoeff_zero hb
  rw [map_sub, coeff_subst hs, coeff_subst hs',
    ← finsum_sub_distrib (coeff_subst_finite hs f μ) (coeff_subst_finite hs' f μ)]
  refine finsum_induction (fun x => V.Ge (c + w) x) (VF.Ge.zero _) (fun _ _ => VF.Ge.add) fun e => ?_
  by_cases he : e.degree ≤ D
  · rw [← smul_sub, ← map_sub, smul_eq_mul]
    exact (hf e he).mul ((cong_prod h e).2.2 μ hμ)
  · rw [coeff_prod_high ha e μ (by omega), coeff_prod_high hb e μ (by omega)]
    simpa using VF.Ge.zero (V := V) (c + w)

theorem exists_ge (V : VF C) (x : C) : ∃ c : ℝ, V.Ge c x := by
  unfold VF.Ge
  induction V.v x using WithTop.recTopCoe with
  | top => exact ⟨0, le_top⟩
  | coe t => exact ⟨t, le_rfl⟩

theorem exists_low (V : VF C) [Finite τ] {ι : Type} [Finite ι] (D : ℕ) (f : ι → MvPowerSeries τ C) :
    ∃ c : ℝ, ∀ i, Low V D c (f i) := by
  have hfin : {μ : τ →₀ ℕ | μ.degree ≤ D}.Finite := Finsupp.finite_of_degree_le D
  haveI := hfin.to_subtype
  choose c hc using fun p : ι × {μ : τ →₀ ℕ | μ.degree ≤ D} => exists_ge V (coeff p.2.1 (f p.1))
  obtain ⟨m, hm⟩ := (Set.finite_range c).bddBelow
  exact ⟨m, fun i μ hμ => (hc (i, ⟨μ, hμ⟩)).mono (hm ⟨_, rfl⟩)⟩

theorem Low.l_pow {D : ℕ} {w : ℝ} {g : MvPowerSeries τ C} (h : Low V D w g) (n : ℕ) :
    Low V D (n + w) (V.l ^ n • g) := by
  induction n with
  | zero => simpa using h
  | succ n ih =>
    intro μ hμ
    have := (ih μ hμ).l_mul
    rw [pow_succ', mul_smul, map_nsmul, nsmul_eq_mul]
    refine this.mono (le_of_eq ?_)
    push_cast; ring

end Bound

section Log

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}
  (Y : FBChart C V O dd)

theorem lg_const (i : Fin dd) : constantCoeff (Y.lg i) = 0 := by
  have := Y.lg_lin i 0 (by simp)
  simpa using this

theorem log_act_add (a b : O) :
    comp1 Y.lg (Y.B.A.act (a + b)) = comp1 Y.lg (Y.B.A.act a) + comp1 Y.lg (Y.B.A.act b) := by
  funext i
  have hab := const_two (Y.B.A.const a) (Y.B.A.const b)
  have h := congrArg (ev (n := 1) ![Y.B.A.act a, Y.B.A.act b]) (Y.lg_add i)
  have hF : ∀ j, constantCoeff (addOf Y.B.G.F (pt C (n := 2) dd 0) (pt C dd 1) j) = 0 := fun j => by
    rw [addOf, constantCoeff_ev (const_two (const_pt 0) (const_pt 1)), Y.B.G.const]
  have e0 : (fun j => ev (n := 1) ![Y.B.A.act a, Y.B.A.act b] (pt C dd (0 : Fin 2) j)) = Y.B.A.act a :=
    funext fun j => ev_pt hab 0 j
  have e1 : (fun j => ev (n := 1) ![Y.B.A.act a, Y.B.A.act b] (pt C dd (1 : Fin 2) j)) = Y.B.A.act b :=
    funext fun j => ev_pt hab 1 j
  have e2 : (fun j => ev (n := 1) ![Y.B.A.act a, Y.B.A.act b]
      (addOf Y.B.G.F (pt C (n := 2) dd 0) (pt C dd 1) j)) = Y.B.A.act (a + b) := by
    funext j
    rw [addOf, ev_ev_two (const_pt 0) (const_pt 1) hab, e0, e1, Y.B.A.add_act]
    rfl
  have hadd : ∀ f g : PS C 2 dd, ev (n := 1) ![Y.B.A.act a, Y.B.A.act b] (f + g) =
      ev (n := 1) ![Y.B.A.act a, Y.B.A.act b] f + ev (n := 1) ![Y.B.A.act a, Y.B.A.act b] g :=
    fun f g => subst_add (hasSubst_pts hab) f g
  rw [hadd, ev_ev_one hF hab, ev_ev_one (const_pt 0) hab, ev_ev_one (const_pt 1) hab, e0, e1, e2] at h
  exact h

noncomputable def logAct : O →+ Pt C 1 dd :=
  AddMonoidHom.mk' (fun a => comp1 Y.lg (Y.B.A.act a)) (log_act_add Y)

theorem logAct_const (a : O) (i : Fin dd) : constantCoeff (logAct Y a i) = 0 :=
  const_comp1 (lg_const Y) (Y.B.A.const a) i

theorem act_eq (a : O) : Y.B.A.act a = comp1 Y.ex (logAct Y a) := by
  funext i
  have ha := const_one (Y.B.A.const a)
  have h := congrArg (ev (n := 1) ![Y.B.A.act a]) (congrFun Y.ex_lg i)
  rw [comp1, ev_ev_one (lg_const Y) ha, ev_pt ha] at h
  exact h.symm

omit [CharZero C] in
theorem low_ev_sub {D m n : ℕ} {w c : ℝ} {x y : Fin m → Pt C n dd} {f : PS C m dd}
    (hx : ∀ j i, constantCoeff (x j i) = 0) (hy : ∀ j i, constantCoeff (y j i) = 0)
    (h : ∀ j i, Cong V D w (x j i) (y j i)) (hf : Low V D c f) :
    Low V D (c + w) (ev x f - ev y f) :=
  low_subst_sub (a := fun p : Fin m × Fin dd => x p.1 p.2) (b := fun p : Fin m × Fin dd => y p.1 p.2)
    (fun s => hx s.1 s.2) (fun s => hy s.1 s.2) (fun s => h s.1 s.2) hf

omit [CharZero C] in
theorem low_comp1_sub {D : ℕ} {w c : ℝ} {x y φ : Pt C 1 dd}
    (hx : ∀ i, constantCoeff (x i) = 0) (hy : ∀ i, constantCoeff (y i) = 0)
    (h : ∀ i, Cong V D w (x i) (y i)) (hφ : ∀ i, Low V D c (φ i)) (i : Fin dd) :
    Low V D (c + w) (comp1 φ x i - comp1 φ y i) := by
  refine low_ev_sub (const_one hx) (const_one hy) (fun j s => ?_) (hφ i)
  fin_cases j
  exact h s

omit [CharZero C] in
theorem cong_zero_of_int {D : ℕ} {τ : Type} {g h : MvPowerSeries τ C} (hg : IntS V g) (hh : IntS V h) :
    Cong V D 0 g h :=
  ⟨low_of_int hg D, low_of_int hh D, fun μ _ => by rw [map_sub]; exact (hg μ).sub (hh μ)⟩

theorem exists_low_logAct (D : ℕ) : ∃ c : ℝ, ∀ y i, Low V D c (logAct Y y i) := by
  obtain ⟨c, hc⟩ := exists_low V D Y.lg
  refine ⟨c, fun y i => ?_⟩
  have h := low_comp1_sub (Y.B.A.const y) (Y.B.A.const 0)
    (fun j => cong_zero_of_int (D := D) (Y.intAct y j) (Y.intAct 0 j)) hc i
  change Low V D (c + 0) (logAct Y y i - logAct Y 0 i) at h
  simpa using h

theorem act_small (D N : ℕ) : ∃ n0 : ℕ, ∀ n ≥ n0, ∀ (y : O) i,
    Low V D N (Y.B.A.act ((V.l : O) ^ n * y) i - Y.B.A.act 0 i) := by
  obtain ⟨c, hc⟩ := exists_low_logAct Y D
  obtain ⟨c', hc'⟩ := exists_low V D Y.ex
  obtain ⟨n0, hn0⟩ := exists_nat_ge (max (-c) (N - c - c'))
  refine ⟨n0, fun n hn y i => ?_⟩
  have hn' : (n0 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 := le_max_left (-c) (N - c - c')
  have h2 := le_max_right (-c) (N - c - c')
  have hL : ∀ j, Low V D (n + c) (logAct Y ((V.l : O) ^ n * y) j) := fun j => by
    rw [← Nat.cast_pow, ← nsmul_eq_mul, map_nsmul]
    exact (hc y j).l_pow n
  rw [act_eq, act_eq Y 0]
  refine (low_comp1_sub (w := n + c) (logAct_const Y _) (logAct_const Y _) (fun j => ?_) hc' i).mono
    (by linarith)
  rw [map_zero]
  exact ⟨(hL j).mono (by linarith), low_zero _ _, by simpa using hL j⟩

theorem actCv (a : ℕ → O) (ha : ∀ n, ∃ y, a (n + 1) - a n = (V.l : O) ^ n * y) : ActCv Y a := by
  intro N i μ
  obtain ⟨n0, hn0⟩ := act_small Y μ.degree N
  refine ⟨n0, fun n hn => ?_⟩
  obtain ⟨y, hy⟩ := ha n
  have e1 : Y.B.A.act (a (n + 1)) = addOf Y.B.G.F (Y.B.A.act (a n)) (Y.B.A.act ((V.l : O) ^ n * y)) := by
    have := Y.B.A.add_act (a n) ((V.l : O) ^ n * y)
    rwa [← hy, add_sub_cancel, hy] at this
  have e0 : Y.B.A.act (a n) = addOf Y.B.G.F (Y.B.A.act (a n)) (Y.B.A.act 0) := by
    have := Y.B.A.add_act (a n) 0
    rwa [add_zero] at this
  have h : Low V μ.degree (0 + N) (addOf Y.B.G.F (Y.B.A.act (a n)) (Y.B.A.act ((V.l : O) ^ n * y)) i -
      addOf Y.B.G.F (Y.B.A.act (a n)) (Y.B.A.act 0) i) := by
    refine low_ev_sub (const_two (Y.B.A.const _) (Y.B.A.const _))
      (const_two (Y.B.A.const _) (Y.B.A.const _)) (fun j s => ?_) (low_of_int (Y.intF i) _)
    fin_cases j
    · exact ⟨low_of_int (Y.intAct _ s) _, low_of_int (Y.intAct _ s) _, by simpa using low_zero _ _⟩
    · exact ⟨low_of_int (Y.intAct _ s) _, low_of_int (Y.intAct _ s) _, hn0 n hn y s⟩
  rw [← e1, ← e0, zero_add] at h
  rw [← map_sub]
  exact h μ le_rfl

end Log

theorem main : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ)
    (Y : FBChart C V O dd) (a : ℕ → O), (∀ n, ∃ y, a (n + 1) - a n = (V.l : O) ^ n * y) →
    ActCv Y a ∧ ActCv Y (fun n => star (a n)) := by
  intro C _ _ V O _ _ dd Y a ha
  refine ⟨actCv Y a ha, actCv Y _ fun n => ?_⟩
  obtain ⟨y, hy⟩ := ha n
  exact ⟨star y, by rw [← star_sub, hy, star_mul', star_pow, star_natCast]⟩

end GlobalTheory.ActionLimit
end

open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.actionConverges_ladic_cauchy_and_star : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ) (Y : FBChart C V O dd) (a : ℕ → O), (∀ n, ∃ y, a (n + 1) - a n = (V.l : O) ^ n * y) → ActCv Y a ∧ ActCv Y (fun n => star (a n)) := by
  atlas_forward_decl GlobalTheory.ActionLimit.main
end

section
noncomputable section

open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing GlobalTheory.GermDerivativeLinearMaps GlobalTheory.IndefiniteRowSideFullHecke

namespace GlobalTheory.ActionLimit

variable {C : Type} [Field C]

theorem eq_zero_of_forall_ge (V : VF C) (x : C) (h : ∀ N : ℕ, V.Ge N x) : x = 0 := by
  by_contra hx
  have ht : V.v x ≠ ⊤ := (AddValuation.ne_top_iff V.v).2 hx
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.1 ht
  obtain ⟨N, hN⟩ := exists_nat_gt r
  have := h N
  rw [VF.Ge, ← hr, WithTop.coe_le_coe] at this
  exact absurd hN (not_lt.2 this)

theorem exists_nat_ge_neg (V : VF C) (x : C) : ∃ K : ℕ, V.Ge (-(K : ℝ)) x := by
  by_cases ht : V.v x = ⊤
  · exact ⟨0, by rw [VF.Ge, ht]; exact le_top⟩
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.1 ht
  obtain ⟨N, hN⟩ := exists_nat_gt (-r)
  refine ⟨N, ?_⟩
  rw [VF.Ge, ← hr, WithTop.coe_le_coe]
  linarith

theorem limit_unique (V : VF C) (s : ℕ → C) (x y : C) (hx : ∀ N : ℕ, ∃ n0 : ℕ, ∀ n ≥ n0, V.Ge N (x - s n))
    (hy : ∀ N : ℕ, ∃ n0 : ℕ, ∀ n ≥ n0, V.Ge N (y - s n)) : x = y := by
  refine sub_eq_zero.1 (eq_zero_of_forall_ge V _ fun N => ?_)
  obtain ⟨a, ha⟩ := hx N
  obtain ⟨b, hb⟩ := hy N
  have := (ha _ (le_max_left a b)).sub (hb _ (le_max_right a b))
  rwa [sub_sub_sub_cancel_right] at this

theorem linear_limit (V : VF C) {dd : ℕ} (e : Pt C 1 dd) (s : ℕ → Pt C 1 dd)
    (h : ∀ (N : ℕ) i μ, ∃ n0 : ℕ, ∀ n ≥ n0,
      V.Ge N (MvPowerSeries.coeff μ (e i) - MvPowerSeries.coeff μ (s n i)))
    (N : ℕ) (v : Fin dd → C) (i : Fin dd) :
    ∃ n0, ∀ n ≥ n0, V.Ge N ((dLin e).mulVec v i - linAct (s n) v i) := by
  choose K hK using fun j => exists_nat_ge_neg V (v j)
  choose m hm using fun j => h (N + K j) i (Finsupp.single ((0 : Fin 1), j) 1)
  refine ⟨Finset.univ.sup m, fun n hn => ?_⟩
  have e1 : (dLin e).mulVec v i - linAct (s n) v i =
      ∑ j, (MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), j) 1) (e i) -
        MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), j) 1) (s n i)) * v j := by
    simp only [sub_mul, Finset.sum_sub_distrib]
    rfl
  rw [e1]
  refine VF.Ge.sum fun j _ => ?_
  have := (hm j n (le_trans (Finset.le_sup (f := m) (Finset.mem_univ j)) hn)).mul (hK j)
  refine this.mono ?_
  push_cast
  linarith

theorem subst_singlePointUncurry {dd : ℕ} {τ : Type} (a : Fin dd → MvPowerSeries τ C)
    (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) (f : PS C 1 dd) :
    MvPowerSeries.subst a (un1 f) = MvPowerSeries.subst (fun p : Fin 1 × Fin dd => a p.2) f := by
  let ι : Fin dd ≃ Fin 1 × Fin dd :=
    { toFun := fun x => (0, x)
      invFun := fun p => p.2
      left_inv := fun _ => rfl
      right_inv := fun p => Prod.ext (Subsingleton.elim _ _) rfl }
  ext μ
  rw [MvPowerSeries.coeff_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero ha),
    MvPowerSeries.coeff_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero fun p : Fin 1 × Fin dd => ha p.2),
    ← finsum_comp_equiv (Finsupp.equivCongrLeft ι)]
  refine finsum_congr fun e => ?_
  rw [Finsupp.equivCongrLeft_apply, Finsupp.prod_equivMapDomain, Finsupp.equivMapDomain_eq_mapDomain]
  rfl

theorem germComp1_eq_subst {dd n : ℕ} (e : Pt C 1 dd) (a : Pt C n dd) (i : Fin dd) :
    comp1 e a i = MvPowerSeries.subst (fun q : Fin 1 × Fin dd => a q.2) (e i) := by
  show MvPowerSeries.subst (fun q : Fin 1 × Fin dd => (![a] : Fin 1 → Pt C n dd) q.1 q.2) (e i) = _
  congr 1
  funext ⟨s, x⟩
  obtain rfl : s = 0 := Subsingleton.elim _ _
  rfl

theorem subst_exp_eq_mvExp [CharZero C] {σ : Type} (f : MvPowerSeries σ C) (hf : MvPowerSeries.constantCoeff f = 0) :
    PowerSeries.subst f (PowerSeries.exp C) = mvExp f := by
  ext m
  rw [PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero hf),
    finsum_eq_sum_of_support_subset (s := Finset.range (m.degree + 1))]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [PowerSeries.coeff_exp, smul_eq_mul]
    simp [div_eq_inv_mul]
  · intro k hk
    by_contra hc
    apply hk
    have hlt : m.degree < k := by simpa using hc
    have : MvPowerSeries.coeff m (f ^ k) = 0 := by
      apply MvPowerSeries.coeff_of_lt_order
      refine lt_of_lt_of_le ?_ (MvPowerSeries.le_order_pow_of_constantCoeff_eq_zero k hf)
      exact_mod_cast hlt
    simp [this]

section Chart

variable [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} (Y : FBChart C V O dd)

theorem gp_lg : GP Y.lg := fun i => by
  have := Y.lg_lin i 0 (by simp)
  simpa using this

theorem dLin_lg : dLin Y.lg = 1 := by
  rw [← germLinearPart_coordinatePoint_zero]
  ext i j
  exact Y.lg_lin i _ (by simp)

theorem eq_exp_lin_log (e : Pt C 1 dd) (he : GP e)
    (hhom : comp1 e (addOf Y.B.G.F (pt C (n := 2) dd 0) (pt C (n := 2) dd 1)) =
      addOf Y.B.G.F (comp1 e (pt C (n := 2) dd 0)) (comp1 e (pt C (n := 2) dd 1))) :
    e = comp1 Y.ex (comp1 (LogExpAdaptedGauge.linMap (dLin e)) Y.lg) := by
  have h0 := gp_lg Y
  have hF := Y.B.G.const
  have hi : IsInvPair Y.lg Y.ex := ⟨h0, Y.ex_const, Y.lg_ex, Y.ex_lg⟩
  have p0 : GP (pt C (n := 2) dd 0) := gp_pt 0
  have p1 : GP (pt C (n := 2) dd 1) := gp_pt 1
  have hl : comp1 Y.lg (addOf Y.B.G.F (pt C (n := 2) dd 0) (pt C (n := 2) dd 1)) =
      comp1 Y.lg (pt C (n := 2) dd 0) + comp1 Y.lg (pt C (n := 2) dd 1) := funext Y.lg_add
  have e1 := additive_eq_lin _ hF Y.lg Y.ex (comp1 Y.lg e) (dLin_lg Y) hl hi (gp_comp1 _ _ h0 he) (by
    rw [gt_comp1_comp1 _ _ he _ (gp_addOf _ hF _ _ p0 p1), hhom,
      additive_at _ hF _ hl _ _ (gp_comp1 _ _ he p0) (gp_comp1 _ _ he p1),
      gt_comp1_comp1 _ _ he _ p0, gt_comp1_comp1 _ _ he _ p1])
  rw [dLin_comp _ _ he, dLin_lg, one_mul] at e1
  rw [← e1, gt_comp_inv' hi _ he]

variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] (p : PairData Y d I)

omit [CharZero C] in
theorem subst_linMap (M : Matrix (Fin dd) (Fin dd) C) (L : Pt C 1 dd) (h0 : GP L)
    {τ : Type} (a : Fin dd → MvPowerSeries τ C) (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) (x : Fin dd) :
    ∑ y, M x y • MvPowerSeries.subst a (un1 (L y)) =
      MvPowerSeries.subst (fun q : Fin 1 × Fin dd => a q.2) (comp1 (LogExpAdaptedGauge.linMap M) L x) := by
  have hs : MvPowerSeries.HasSubst (fun q : Fin 1 × Fin dd => a q.2) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun q => ha q.2
  rw [germComp_matrixLinearMap_apply _ _ h0, ← MvPowerSeries.coe_substAlgHom hs, map_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [subst_singlePointUncurry a ha, ← MvPowerSeries.smul_eq_C_mul, MvPowerSeries.coe_substAlgHom hs,
    MvPowerSeries.subst_smul hs]

theorem matrixEnd_linearMap (M : Matrix (Fin dd) (Fin dd) C)
    {τ : Type} (a : Fin dd → MvPowerSeries τ C) (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) (i : Fin dd) :
    endP (Y.raw p) M a i =
      MvPowerSeries.subst (fun q : Fin 1 × Fin dd => a q.2) (comp1 Y.ex (comp1 (LogExpAdaptedGauge.linMap M) Y.lg) i) := by
  have h0 := gp_lg Y
  have hs : MvPowerSeries.HasSubst (fun q : Fin 1 × Fin dd => a q.2) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun q => ha q.2
  have hL : GP (comp1 (LogExpAdaptedGauge.linMap M) Y.lg) := gp_comp1 _ _ (gp_linMap _) h0
  have e0 : endP (Y.raw p) M a i =
    MvPowerSeries.subst (fun x => ∑ y, M x y • MvPowerSeries.subst a (un1 (Y.lg y))) (un1 (Y.ex i)) := rfl
  rw [e0, funext (subst_linMap M Y.lg h0 a ha)]
  generalize comp1 (LogExpAdaptedGauge.linMap M) Y.lg = L at hL ⊢
  have hz : ∀ x, MvPowerSeries.constantCoeff
      (MvPowerSeries.subst (fun q : Fin 1 × Fin dd => a q.2) (L x)) = 0 :=
    fun x => Formalism.L2.FormalSeriesBounds.constantCoeff_subst_zero (fun q : Fin 1 × Fin dd => ha q.2) (hL x)
  rw [subst_singlePointUncurry _ hz, germComp1_eq_subst, MvPowerSeries.subst_comp_subst_apply
    (MvPowerSeries.hasSubst_of_constantCoeff_zero fun q : Fin 1 × Fin dd => hL q.2) hs]

theorem matrixEnd_eq_subst (e : Pt C 1 dd) (he : GP e)
    (hhom : comp1 e (addOf Y.B.G.F (pt C (n := 2) dd 0) (pt C (n := 2) dd 1)) =
      addOf Y.B.G.F (comp1 e (pt C (n := 2) dd 0)) (comp1 e (pt C (n := 2) dd 1)))
    {τ : Type} (a : Fin dd → MvPowerSeries τ C) (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) (i : Fin dd) :
    endP (Y.raw p) (dLin e) a i = MvPowerSeries.subst (fun q : Fin 1 × Fin dd => a q.2) (e i) := by
  rw [matrixEnd_linearMap Y p _ a ha, ← eq_exp_lin_log Y e he hhom]

theorem matrixEnd_eq_comp (e : Pt C 1 dd) (he : GP e)
    (hhom : comp1 e (addOf Y.B.G.F (pt C (n := 2) dd 0) (pt C (n := 2) dd 1)) =
      addOf Y.B.G.F (comp1 e (pt C (n := 2) dd 0)) (comp1 e (pt C (n := 2) dd 1)))
    {n : ℕ} (a : Pt C n dd) (ha : GP a) : endP (Y.raw p) (dLin e) a = comp1 e a := by
  funext i
  rw [matrixEnd_eq_subst Y p e he hhom a ha, germComp1_eq_subst]

theorem hAt_eq_ev {n : ℕ} (a b : Pt C n dd) : hAt (Y.raw p) a b = ev ![a, b] Y.h := by
  show MvPowerSeries.subst _ Y.h = MvPowerSeries.subst _ Y.h
  congr 1
  funext ⟨s, x⟩
  fin_cases s <;> rfl

theorem isEnd_of_hom (e e' : Pt C 1 dd) (he : GP e) (he' : GP e')
    (hhom : comp1 e (addOf Y.B.G.F (pt C (n := 2) dd 0) (pt C (n := 2) dd 1)) =
      addOf Y.B.G.F (comp1 e (pt C (n := 2) dd 0)) (comp1 e (pt C (n := 2) dd 1)))
    (hhom' : comp1 e' (addOf Y.B.G.F (pt C (n := 2) dd 0) (pt C (n := 2) dd 1)) =
      addOf Y.B.G.F (comp1 e' (pt C (n := 2) dd 0)) (comp1 e' (pt C (n := 2) dd 1)))
    (hi : ∀ i, IntS V (e i)) (hi' : ∀ i, IntS V (e' i))
    (hx : IntS V (FB.expS C (ev (n := 2) ![comp1 e (pt C dd 0), pt C dd 1] Y.h -
        ev (n := 2) ![pt C dd 0, comp1 e' (pt C dd 1)] Y.h))) :
    IsEnd (Y.raw p) V (dLin e) (dLin e') := by
  have hX : ∀ i : Fin dd, MvPowerSeries.constantCoeff (MvPowerSeries.X i : MvPowerSeries (Fin dd) C) = 0 :=
    fun i => by simp
  have hc : MvPowerSeries.constantCoeff Y.h = 0 := by
    rw [← gt_const_ev_eq _ (pair_points_zero_constant gp_zero₂ (gp_pt (0 : Fin 1))) Y.h, Y.gauge.ax0, map_zero]
  refine ⟨fun i => ?_, fun i => ?_, ?_⟩
  · rw [matrixEnd_eq_subst Y p e he hhom _ hX, ← subst_singlePointUncurry _ hX, MvPowerSeries.subst_self]
    exact fun μ => hi i _
  · rw [matrixEnd_eq_subst Y p e' he' hhom' _ hX, ← subst_singlePointUncurry _ hX, MvPowerSeries.subst_self]
    exact fun μ => hi' i _
  · have g0 : gp C (Fin dd) (0 : Fin 2) = pt C dd 0 := rfl
    have g1 : gp C (Fin dd) (1 : Fin 2) = pt C dd 1 := rfl
    rw [g0, g1, matrixEnd_eq_comp Y p e he hhom _ (gp_pt 0), matrixEnd_eq_comp Y p e' he' hhom' _ (gp_pt 1),
      hAt_eq_ev, hAt_eq_ev, ← subst_exp_eq_mvExp]
    · exact hx
    · rw [map_sub, gt_const_ev _ (pair_points_zero_constant (gp_comp1 _ _ he (gp_pt 0)) (gp_pt 1)) _ hc,
        gt_const_ev _ (pair_points_zero_constant (gp_pt 0) (gp_comp1 _ _ he' (gp_pt 1))) _ hc, sub_zero]

end Chart

theorem exists_isEnd_of_limit : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ) (Y : FBChart C V O dd) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (p : PairData Y d I), ∀ a : ℕ → O, (∀ n, ∃ y, a (n + 1) - a n = (V.l : O) ^ n * y) → ∃ M M' : Matrix (Fin dd) (Fin dd) C, IsEnd (Y.raw p) V M M' ∧ IsEnd (Y.raw p) V M' M ∧ (∀ (N : ℕ) (v : Fin dd → C) i, ∃ n0, ∀ n ≥ n0, V.Ge N (M.mulVec v i - linAct (Y.B.A.act (a n)) v i)) ∧ (∀ (N : ℕ) (v : Fin dd → C) i, ∃ n0, ∀ n ≥ n0, V.Ge N (M'.mulVec v i - linAct (Y.B.A.act (star (a n))) v i)) := by
  intro C _ _ V O _ _ dd Y d _ I _ p a ha
  obtain ⟨c1, c2⟩ := GlobalTheory.T.actionConverges_ladic_cauchy_and_star C V O dd Y a ha
  obtain ⟨e, eb, i1, i2, l1, l2, h1, x1⟩ := GlobalTheory.T.formalGroupAction_limits_integral_endomorphisms C V O dd Y a c1 c2
  obtain ⟨f, fb, -, -, l3, l4, h2, x2⟩ := GlobalTheory.T.formalGroupAction_limits_integral_endomorphisms C V O dd Y (fun n => star (a n)) c2
    (by simpa only [star_star] using c1)
  simp only [star_star] at l4
  obtain rfl : f = eb := funext fun i => MvPowerSeries.ext fun μ =>
    limit_unique V _ _ _ (fun N => l3 N i μ) (fun N => l2 N i μ)
  obtain rfl : fb = e := funext fun i => MvPowerSeries.ext fun μ =>
    limit_unique V _ _ _ (fun N => l4 N i μ) (fun N => l1 N i μ)
  have hz : ∀ (g : Pt C 1 dd) (s : ℕ → O), (∀ (N : ℕ) i μ, ∃ n0 : ℕ, ∀ n ≥ n0,
      V.Ge N (MvPowerSeries.coeff μ (g i) - MvPowerSeries.coeff μ (Y.B.A.act (s n) i))) → GP g := by
    intro g s hg i
    refine limit_unique V (fun n => MvPowerSeries.coeff 0 (Y.B.A.act (s n) i)) _ _ (fun N => hg N i 0)
      fun N => ⟨0, fun n _ => ?_⟩
    simp only [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, Y.B.A.const, sub_zero]
    exact VF.Ge.zero _
  have g1 := hz fb a l1
  have g2 := hz f (fun n => star (a n)) l2
  exact ⟨dLin fb, dLin f, isEnd_of_hom Y p fb f g1 g2 h1 h2 i1 i2 x1, isEnd_of_hom Y p f fb g2 g1 h2 h1 i2 i1 x2,
    linear_limit V fb _ l1, linear_limit V f _ l2⟩

end GlobalTheory.ActionLimit
end
end
