import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwoChartAtlas.AdditionLawSecondIdentity
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsFormalBiextMap
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.GermExpAddAndEvConst
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.MvPowerSeriesJetEqCalculus
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.JetEqFormalExpIffAndExistsLog
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ConstantCoeffDmonNCongr
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.AxisPderivComp
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SumSupportRename
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FormalChartJetRelUnitOneOnAxes
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FormalCompApplyEqMvPowerSeriesSubst
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.PderivSecondEvFirstPointEqZero
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.EqZeroOfAdditiveOfPderiv
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.CoeffSingleLawAdd
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.HarmonicValueCopiesGaugeIndependent

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mvPowerSeriesJetEq_calculus : ∀ (R : Type) [CommRing R] (m : ℕ), (∀ (σ : Type) (f f' g g' : MvPowerSeries σ R), JEq m f f' → JEq m g g' → JEq m (f + g) (f' + g') ∧ JEq m (f - g) (f' - g') ∧ JEq m (f * g) (f' * g')) ∧ (∀ (σ : Type) (f g u : MvPowerSeries σ R), IsUnit (MvPowerSeries.constantCoeff u) → JEq m (f * u) (g * u) → JEq m f g) ∧ (∀ (σ R' : Type) [CommRing R'] (β : R →+* R') (f g : MvPowerSeries σ R), JEq m f g → JEq m (MvPowerSeries.map β f) (MvPowerSeries.map β g)) ∧ (∀ (d n n' : ℕ) (a a' : Fin n → Pt R n' d) (f g : PS R n d), (∀ i j, MvPowerSeries.constantCoeff (a i j) = 0) → (∀ i j, MvPowerSeries.constantCoeff (a' i j) = 0) → (∀ i j, JEq m (a i j) (a' i j)) → JEq m f g → JEq m (ev a f) (ev a' g)) ∧ (∀ (σ : Type) [Fintype σ] [DecidableEq σ] (f g : MvPowerSeries σ R), JEq m f g ↔ psJet m f = psJet m g) ∧ (∀ (σ : Type) (f g : MvPowerSeries σ R), (∀ m', JEq m' f g) → f = g) := by
  first | exact @GlobalTheory.ChartCmp.JCalc.jeq_calculus | exact GlobalTheory.ChartCmp.JCalc.jeq_calculus | (intros; apply GlobalTheory.ChartCmp.JCalc.jeq_calculus <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jetEq_formalExp_iff_and_exists_log : ∀ (k : Type) [CommRing k] [Algebra ℚ k] (n d m : ℕ), (∀ f g : PS k n d, MvPowerSeries.constantCoeff f = 0 → MvPowerSeries.constantCoeff g = 0 → (JEq m f g ↔ JEq m (FB.expS k f) (FB.expS k g))) ∧ ∀ u : PS k n d, MvPowerSeries.constantCoeff u = 1 → ∃ lam : PS k n d, MvPowerSeries.constantCoeff lam = 0 ∧ FB.expS k lam = u := by
  first | exact @GlobalTheory.ChartCmp.jeq_expS_iff_and_exists_log | exact GlobalTheory.ChartCmp.jeq_expS_iff_and_exists_log | (intros; apply GlobalTheory.ChartCmp.jeq_expS_iff_and_exists_log <;> assumption)
end

section
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp

namespace GlobalTheory.ChartCmp

theorem constantCoeff_DpolyN_jEq : ∀ (k : Type) [CommRing k] (d n : ℕ) (F : Fin d → PS k 2 d) (Ix : Type) [Fintype Ix] (cp : Ix → Fin n) (u : Ix → Fin d → k) (P : MvPolynomial Ix k) (m : ℕ) (f g : PS k n d), P.totalDegree ≤ m → JEq m f g → MvPowerSeries.constantCoeff (DpolyN F cp u P f) = MvPowerSeries.constantCoeff (DpolyN F cp u P g) := by
  intro k _ d n F Ix _ cp u P m f g hP hfg
  classical
  rw [GlobalTheory.PowGerm.NabJet.constantCoeff_DpolyN_eq F cp u P f _ subset_rfl,
    GlobalTheory.PowGerm.NabJet.constantCoeff_DpolyN_eq F cp u P g _ subset_rfl]
  refine Finset.sum_congr rfl fun e he => ?_
  congr 1
  refine GlobalTheory.PowGerm.NabJet.constantCoeff_DmonN_congr F cp u e f g fun mo hmo => ?_
  refine hfg mo (hmo.trans (le_trans ?_ hP))
  have := MvPolynomial.le_totalDegree he
  rwa [Finsupp.degree_apply]

end GlobalTheory.ChartCmp
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constantCoeff_invariantPolyOperator_jetEq : ∀ (k : Type) [CommRing k] (d n : ℕ) (F : Fin d → PS k 2 d) (Ix : Type) [Fintype Ix] (cp : Ix → Fin n) (u : Ix → Fin d → k) (P : MvPolynomial Ix k) (m : ℕ) (f g : PS k n d), P.totalDegree ≤ m → JEq m f g → MvPowerSeries.constantCoeff (DpolyN F cp u P f) = MvPowerSeries.constantCoeff (DpolyN F cp u P g) := by
  atlas_forward_decl GlobalTheory.ChartCmp.constantCoeff_DpolyN_jEq
end

section
section
set_option autoImplicit false

noncomputable section

open MvPowerSeries Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open ReciprocityTheory.ChartRestriction.G.TB.WickVanishing GlobalTheory.ChartTrans GlobalTheory.NabCol

namespace GlobalTheory.ChartTransN

variable {k : Type} [CommRing k] {d n : ℕ}

theorem dofN_ev {m : ℕ} (F : Fin d → PS k 2 d) (b : Fin n) (u : Fin d → k) (V : Fin m → Pt k n d)
    (hV : ∀ j, GP (V j)) (g : PS k m d) :
    DofN F b u (ev V g) = ∑ c : Fin m, ∑ l : Fin d, ev V (pderiv k (c, l) g) * DofN F b u (V c l) := by
  unfold DofN
  simp only [pderiv_ev V hV]
  simp only [Finset.mul_sum (s := (Finset.univ : Finset (Fin m))), Finset.mul_sum (f := fun l => ev V _ * _)]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem dofN_inCol_ne (F : Fin d → PS k 2 d) {b c : Fin n} (h : c ≠ b) (u : Fin d → k) (f : PS k 1 d) :
    DofN F b u (inCol c f) = 0 := by
  unfold DofN
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [pderiv_inCol, if_neg h, mul_zero]

theorem dofN_eq_sum (F : Fin d → PS k 2 d) (b : Fin n) (u : Fin d → k) (g : PS k n d) :
    DofN F b u g = ∑ l, inCol b (Dof F u (X ((0 : Fin 1), l))) * pderiv k (b, l) g := by
  have hX : ∀ l, inCol b (X ((0 : Fin 1), l) : PS k 1 d) = X (b, l) := fun l => gt_ev_X _ (gp b) 0 l
  simp only [← dofN_inCol, hX]
  conv_lhs => unfold DofN
  refine Finset.sum_congr rfl fun l _ => ?_
  congr 1
  unfold DofN
  symm
  rw [Finset.sum_eq_single l]
  · rw [pderiv_X_self, mul_one]
  · intro j _ hj
    rw [pderiv_X_of_ne (fun h => hj (congrArg Prod.snd h).symm), mul_zero]
  · simp

theorem unit_right (G : FGLaw k d) (i : Fin d) :
    ev (n := 1) ![pt k (n := 1) d 0, 0] (G.F i) = (X ((0 : Fin 1), i) : PS k 1 d) := by
  conv_lhs => rw [← G.comm i]
  rw [gt_ev_ev' _ _ axis_GP (pair_points_zero_constant (gp_pt 1) (gp_pt 0)), eval_pair_points, evP_pt _ axis_GP,
    evP_pt _ axis_GP]
  exact G.unit i

theorem dofN_transF (G : FGLaw k d) (φ φi : Pt k 1 d) (hinv : IsInvPair φ φi) (b : Fin n) (u : Fin d → k)
    (g : PS k n d) :
    DofN (transF G.F φ φi) b u (ev (n := n) (fun c => comp1 φ (pt k (n := n) d c)) g) =
      ev (n := n) (fun c => comp1 φ (pt k (n := n) d c)) (DofN G.F b ((dLin φ).mulVec u) g) := by
  have hφ : GP φ := hinv.1
  have hΦ : ∀ c : Fin n, GP (comp1 φ (pt k (n := n) d c)) := fun c => gp_comp1 φ _ hφ (gp_pt c)
  have hc : ∀ (c : Fin n) l, comp1 φ (pt k (n := n) d c) l = inCol c (φ l) := fun _ _ => rfl
  have hcol : ∀ f : PS k 1 d, ev (n := n) (fun c => comp1 φ (pt k (n := n) d c)) (inCol b f) =
      inCol b (ev (n := 1) ![φ] f) := by
    intro f
    unfold inCol
    rw [gt_ev_ev' _ _ hΦ (gp b), gt_ev_ev' _ _ (gp b) (single_point_zero_constant hφ), vec1, vec1, evP_pt _ hΦ]
    rfl
  rw [dofN_ev _ _ _ _ hΦ, dofN_eq_sum G.F, ev_sum _ hΦ, Finset.sum_eq_single b]
  · refine Finset.sum_congr rfl fun l _ => ?_
    rw [gt_ev_mul _ hΦ, hcol, ← dof_transF G.F G.const (unit_right G) φ φi hinv, gt_ev_X _ (single_point_zero_constant hφ), hc,
      dofN_inCol, mul_comm]
    rfl
  · intro c _ hcb
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [hc, dofN_inCol_ne _ hcb, mul_zero]
  · simp

theorem dpolyN_transF : ∀ (k : Type) [CommRing k] (d n : ℕ) (G : FGLaw k d) (φ φi : Pt k 1 d), IsInvPair φ φi → ∀ (Ix : Type) [Fintype Ix] (cp : Ix → Fin n) (u : Ix → Fin d → k) (P : MvPolynomial Ix k) (g : PS k n d), DpolyN (transF G.F φ φi) cp u P (ev (n := n) (fun b => comp1 φ (pt k (n := n) d b)) g) = ev (n := n) (fun b => comp1 φ (pt k (n := n) d b)) (DpolyN G.F cp (fun l => (dLin φ).mulVec (u l)) P g) := by
  intro k _ d n G φ φi hinv Ix _ cp u P g
  have hΦ : ∀ c : Fin n, GP (comp1 φ (pt k (n := n) d c)) := fun c => gp_comp1 φ _ hinv.1 (gp_pt c)
  have hit : ∀ (b : Fin n) (v : Fin d → k) (r : ℕ) (g : PS k n d),
      (DofN (transF G.F φ φi) b v)^[r] (ev (n := n) (fun c => comp1 φ (pt k (n := n) d c)) g) =
        ev (n := n) (fun c => comp1 φ (pt k (n := n) d c)) ((DofN G.F b ((dLin φ).mulVec v))^[r] g) := by
    intro b v r
    induction r with
    | zero => intro g; rfl
    | succ r ih =>
      intro g
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, dofN_transF G φ φi hinv, ih]
  have hmon : ∀ m : Ix →₀ ℕ,
      DmonN (transF G.F φ φi) cp u m (ev (n := n) (fun c => comp1 φ (pt k (n := n) d c)) g) =
        ev (n := n) (fun c => comp1 φ (pt k (n := n) d c))
          (DmonN G.F cp (fun l => (dLin φ).mulVec (u l)) m g) := by
    intro m
    unfold DmonN
    induction (Finset.univ : Finset Ix).toList with
    | nil => rfl
    | cons a L ih => rw [List.foldr_cons, List.foldr_cons, ih, hit]
  unfold DpolyN
  rw [ev_sum _ hΦ]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [ev_C_mul _ hΦ, hmon]

end GlobalTheory.ChartTransN
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.invariantPolyOperatorCopies_transportedLaw : ∀ (k : Type) [CommRing k] (d n : ℕ) (G : FGLaw k d) (φ φi : Pt k 1 d), IsInvPair φ φi → ∀ (Ix : Type) [Fintype Ix] (cp : Ix → Fin n) (u : Ix → Fin d → k) (P : MvPolynomial Ix k) (g : PS k n d), DpolyN (transF G.F φ φi) cp u P (ev (n := n) (fun b => comp1 φ (pt k (n := n) d b)) g) = ev (n := n) (fun b => comp1 φ (pt k (n := n) d b)) (DpolyN G.F cp (fun l => (dLin φ).mulVec (u l)) P g) := by
  atlas_forward_decl GlobalTheory.ChartTransN.dpolyN_transF
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formalChartJetRel_unit_one_on_axes : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (m : ℕ) (B B' : FB R d O) (φ φi : Pt R 1 d) (ε : PS R 2 d), JRel m B B' φ φi ε → MvPowerSeries.constantCoeff ε = 1 ∧ JEq m (ev (n := 1) ![0, pt R (n := 1) d 0] ε) 1 ∧ JEq m (ev (n := 1) ![pt R (n := 1) d 0, 0] ε) 1 := by
  first | exact @GlobalTheory.ChartCmp.jRel_axes | exact GlobalTheory.ChartCmp.jRel_axes | (intros; apply GlobalTheory.ChartCmp.jRel_axes <;> assumption)
end

section
section
set_option autoImplicit false
noncomputable section
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (transF IsInvPair)
open ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
open MvPowerSeries

namespace GlobalTheory.ChartCmp.GaugeDiff

section Map
variable {R k : Type} [CommRing R] [CommRing k] {d : ℕ} (β : R →+* k)

def mapPt {n : ℕ} (a : Pt R n d) : Pt k n d := fun i => MvPowerSeries.map β (a i)

theorem map_ev {m n : ℕ} (a : Fin m → Pt R n d) (ha : ∀ j, GP (a j)) (f : PS R m d) :
    MvPowerSeries.map β (ev a f) = ev (fun j => mapPt β (a j)) (MvPowerSeries.map β f) :=
  MvPowerSeries.map_subst (gt_hasSubst a ha) f

theorem map_ev1 {n : ℕ} (a : Pt R n d) (ha : GP a) (f : PS R 1 d) :
    MvPowerSeries.map β (ev ![a] f) = ev ![mapPt β a] (MvPowerSeries.map β f) := by
  rw [map_ev β _ (single_point_zero_constant ha)]
  congr 1
  funext j; fin_cases j; rfl

theorem map_ev2 {n : ℕ} (a b : Pt R n d) (ha : GP a) (hb : GP b) (f : PS R 2 d) :
    MvPowerSeries.map β (ev ![a, b] f) = ev ![mapPt β a, mapPt β b] (MvPowerSeries.map β f) := by
  rw [map_ev β _ (pair_points_zero_constant ha hb)]
  congr 1
  funext j; fin_cases j <;> rfl

theorem map_ev3 {n : ℕ} (a b c : Pt R n d) (ha : GP a) (hb : GP b) (hc : GP c) (f : PS R 3 d) :
    MvPowerSeries.map β (ev ![a, b, c] f) = ev ![mapPt β a, mapPt β b, mapPt β c] (MvPowerSeries.map β f) := by
  rw [map_ev β _ (triple_points_zero_constant ha hb hc)]
  congr 1
  funext j; fin_cases j <;> rfl

theorem constantCoeff_mapPt_eq_zero {n : ℕ} (a : Pt R n d) (ha : GP a) : GP (mapPt β a) := fun i => by
  simp [mapPt, MvPowerSeries.constantCoeff_map, ha i]

theorem mapPt_pt {n : ℕ} (j : Fin n) : mapPt β (pt R d j) = pt k d j := by
  funext i; simp [mapPt, pt]

theorem mapPt_zero {n : ℕ} : mapPt β (0 : Pt R n d) = 0 := by
  funext i; simp [mapPt]

theorem mapPt_comp1 {n : ℕ} (φ : Pt R 1 d) (a : Pt R n d) (ha : GP a) :
    mapPt β (comp1 φ a) = comp1 (mapPt β φ) (mapPt β a) :=
  funext fun i => map_ev1 β a ha (φ i)

theorem mapPt_addOf {n : ℕ} (F : Fin d → PS R 2 d) (a b : Pt R n d) (ha : GP a) (hb : GP b) :
    mapPt β (addOf F a b) = addOf (mapPt β F) (mapPt β a) (mapPt β b) :=
  funext fun i => map_ev2 β a b ha hb (F i)

theorem jeq_map {σ : Type} {m : ℕ} {f g : MvPowerSeries σ R} (h : JEq m f g) :
    JEq m (MvPowerSeries.map β f) (MvPowerSeries.map β g) := fun e he => by
  rw [MvPowerSeries.coeff_map, MvPowerSeries.coeff_map, h e he]

end Map

section Ring
variable {k : Type} [CommRing k] {d : ℕ}

theorem jeq_of_sub {σ : Type} {m : ℕ} {f g u v : MvPowerSeries σ k} (h : JEq m f g) (e : u - v = f - g) :
    JEq m u v := fun x hx => by
  have := congrArg (MvPowerSeries.coeff x) e
  rw [map_sub, map_sub, h x hx, sub_self] at this
  exact sub_eq_zero.1 this

theorem jeq_of_sub' {σ : Type} {m : ℕ} {f g u v : MvPowerSeries σ k} (h : JEq m f g) (e : u - v = g - f) :
    JEq m u v :=
  jeq_of_sub (f := g) (g := f) (fun x hx => (h x hx).symm) e

theorem coordinateChange_comp1_transported_addOf {n : ℕ} {φ φi : Pt k 1 d} (hinv : IsInvPair φ φi) (F F' : Fin d → PS k 2 d) (hBF : GP F)
    (hF : ∀ i, F' i = transF F φ φi i) (a b : Pt k n d) (ha : GP a) (hb : GP b) :
    comp1 φ (addOf F' a b) = addOf F (comp1 φ a) (comp1 φ b) := by
  have hφ : GP φ := hinv.1
  have hp : ∀ {n : ℕ} (j : Fin n), GP (pt k (n := n) d j) := fun j => gp_pt j
  have hcφ : ∀ {n : ℕ} (a : Pt k n d), GP a → GP (comp1 φ a) := fun a ha => gp_comp1 φ a hφ ha
  have hAd : GP (addOf F (comp1 φ (pt k (n := 2) d 0)) (comp1 φ (pt k (n := 2) d 1))) :=
    gp_addOf _ hBF _ _ (hcφ _ (hp 0)) (hcφ _ (hp 1))
  have e : addOf F' a b = comp1 φi (addOf F (comp1 φ a) (comp1 φ b)) := by
    funext i
    change ev ![a, b] (F' i) = ev ![addOf F (comp1 φ a) (comp1 φ b)] (φi i)
    rw [hF i]
    change ev ![a, b] (ev ![addOf F (comp1 φ (pt k (n := 2) d 0)) (comp1 φ (pt k (n := 2) d 1))]
      (φi i)) = _
    rw [gt_ev_ev' ![a, b] _ (pair_points_zero_constant ha hb) (single_point_zero_constant hAd)]
    congr 1
    funext j
    fin_cases j
    change evP ![a, b] (addOf F (comp1 φ (pt k d 0)) (comp1 φ (pt k d 1))) = _
    rw [evP_addOf _ (pair_points_zero_constant ha hb) _ _ _ (hcφ _ (hp 0)) (hcφ _ (hp 1)),
      evP_comp1 _ (pair_points_zero_constant ha hb) φ _ (hp 0), evP_comp1 _ (pair_points_zero_constant ha hb) φ _ (hp 1),
      evP_pt _ (pair_points_zero_constant ha hb), evP_pt _ (pair_points_zero_constant ha hb)]
    rfl
  rw [e, gt_comp_inv hinv _ (gp_addOf _ hBF _ _ (hcφ _ ha) (hcφ _ hb))]

theorem coordinateChange_comp1_intertwines_action {n : ℕ} {φ φi : Pt k 1 d} (hinv : IsInvPair φ φi) (A A' : Pt k 1 d) (hAa : GP A)
    (hA : A' = comp1 φi (comp1 A φ)) (x : Pt k n d) (hx : GP x) :
    comp1 φ (comp1 A' x) = comp1 A (comp1 φ x) := by
  have hφ : GP φ := hinv.1
  rw [hA, gt_comp1_comp1 φi _ (gp_comp1 _ φ hAa hφ) x hx, gt_comp1_comp1 A φ hφ x hx,
    gt_comp_inv hinv _ (gp_comp1 _ _ hAa (gp_comp1 _ _ hφ hx))]

theorem germEv_germEv_two_points {m n : ℕ} (V : Fin m → Pt k n d) (hV : ∀ j, GP (V j)) (a b : Pt k m d) (ha : GP a) (hb : GP b)
    (f : PS k 2 d) : ev V (ev ![a, b] f) = ev ![evP V a, evP V b] f := by
  rw [gt_ev_ev' V _ hV (pair_points_zero_constant ha hb), eval_pair_points]

theorem ev_trans {n : ℕ} (φ : Pt k 1 d) (hφ : GP φ) (h : PS k 2 d) (a b : Pt k n d) (ha : GP a) (hb : GP b) :
    ev ![a, b] (ev ![comp1 φ (pt k (n := 2) d 0), comp1 φ (pt k (n := 2) d 1)] h) =
      ev ![comp1 φ a, comp1 φ b] h := by
  rw [germEv_germEv_two_points _ (pair_points_zero_constant ha hb) _ _ (gp_comp1 _ _ hφ (gp_pt 0)) (gp_comp1 _ _ hφ (gp_pt 1)),
    evP_comp1 _ (pair_points_zero_constant ha hb) φ _ (gp_pt 0),
    evP_comp1 _ (pair_points_zero_constant ha hb) φ _ (gp_pt 1), evP_pt _ (pair_points_zero_constant ha hb), evP_pt _ (pair_points_zero_constant ha hb)]
  rfl

theorem ev_diff {n : ℕ} (φ : Pt k 1 d) (hφ : GP φ) (h h' lam : PS k 2 d) (a b : Pt k n d) (ha : GP a) (hb : GP b) :
    ev ![a, b] (h' - ev ![comp1 φ (pt k (n := 2) d 0), comp1 φ (pt k (n := 2) d 1)] h - lam) =
      ev ![a, b] h' - ev ![comp1 φ a, comp1 φ b] h - ev ![a, b] lam := by
  rw [gt_ev_sub _ (pair_points_zero_constant ha hb), gt_ev_sub _ (pair_points_zero_constant ha hb), ev_trans φ hφ h a b ha hb]

variable [Algebra ℚ k]

theorem expS_zero {n : ℕ} : FB.expS k (0 : PS k n d) = 1 := by
  unfold FB.expS
  ext e
  rw [PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero (by simp)), finsum_eq_single _ 0]
  · simp
  · intro n hn
    simp [hn]

theorem jeq_log {n m : ℕ} {A B C D : PS k n d} (hA : constantCoeff A = 0) (hB : constantCoeff B = 0)
    (hC : constantCoeff C = 0) (hD : constantCoeff D = 0)
    (h : JEq m (FB.expS k A * FB.expS k B) (FB.expS k C * FB.expS k D)) : JEq m (A + B) (C + D) := by
  rw [← gt_expS_add _ _ hA hB, ← gt_expS_add _ _ hC hD] at h
  exact ((GlobalTheory.ChartCmp.jeq_expS_iff_and_exists_log k n d m).1 _ _ (by simp [hA, hB]) (by simp [hC, hD])).2 h

end Ring

theorem biadd_gauge_diff (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (m : ℕ)
    (B B' : FB R d O) (φ φi : Pt R 1 d) (ε : PS R 2 d) (J : JRel m B B' φ φi ε)
    (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (h h' lam : PS k 2 d)
    (hh : B.IsCanonGauge k h) (hh' : B'.IsCanonGauge k h') (hlam0 : MvPowerSeries.constantCoeff lam = 0)
    (hε : FB.expS k lam = FB.toK k ε) :
    Biadd m B' k (h' - ev (n := 2) ![comp1 (fun i => FB.toK k (φ i)) (pt k (n := 2) d 0),
      comp1 (fun i => FB.toK k (φ i)) (pt k (n := 2) d 1)] h - lam) := by
  set β := algebraMap R k with hβ
  change Biadd m B' k (h' - ev (n := 2) ![comp1 (mapPt β φ) (pt k (n := 2) d 0),
      comp1 (mapPt β φ) (pt k (n := 2) d 1)] h - lam)
  have hε' : MvPowerSeries.map β ε = FB.expS k lam := hε.symm
  have hφ : GP φ := J.inv.1
  have hψ : GP (mapPt β φ) := constantCoeff_mapPt_eq_zero β φ hφ
  have fk : B.FK k = mapPt β B.G.F := rfl
  have fk' : B'.FK k = mapPt β B'.G.F := rfl
  have ak : ∀ a, B.actK k a = mapPt β (B.A.act a) := fun a => rfl
  have ak' : ∀ a, B'.actK k a = mapPt β (B'.A.act a) := fun a => rfl
  have hF : GP B.G.F := B.G.const
  have hF' : GP B'.G.F := B'.G.const
  have hFk := constantCoeff_mapPt_eq_zero β _ hF
  have hFk' := constantCoeff_mapPt_eq_zero β _ hF'
  have hr : ∀ {n : ℕ} (j : Fin n), GP (pt R (n := n) d j) := fun j => gp_pt j
  have hp : ∀ {n : ℕ} (j : Fin n), GP (pt k (n := n) d j) := fun j => gp_pt j
  have hcr : ∀ {n : ℕ} (a : Pt R n d), GP a → GP (comp1 φ a) := fun a ha => gp_comp1 φ a hφ ha
  have hc : ∀ {n : ℕ} (a : Pt k n d), GP a → GP (comp1 (mapPt β φ) a) := fun a ha => gp_comp1 _ a hψ ha
  have hz0 : ∀ {n : ℕ}, GP (0 : Pt k n d) := gp_zero₂
  have hh0 : constantCoeff h = 0 := by
    have := congrArg constantCoeff hh.ax0
    rwa [gt_const_ev_eq _ (pair_points_zero_constant hz0 (hp 0)), map_zero] at this
  have hh0' : constantCoeff h' = 0 := by
    have := congrArg constantCoeff hh'.ax0
    rwa [gt_const_ev_eq _ (pair_points_zero_constant hz0 (hp 0)), map_zero] at this
  have cW : ∀ {n : ℕ} (a b : Pt k n d), GP a → GP b → ∀ f : PS k 2 d, constantCoeff f = 0 →
      constantCoeff (ev ![a, b] f) = 0 := fun a b ha hb f hf => gt_const_ev _ (pair_points_zero_constant ha hb) f hf
  have Gl : ∀ i j : Fin 3, comp1 (mapPt β φ) (addOf (mapPt β B'.G.F) (pt k d i) (pt k d j)) =
      addOf (mapPt β B.G.F) (comp1 (mapPt β φ) (pt k d i)) (comp1 (mapPt β φ) (pt k d j)) := by
    intro i j
    have := congrArg (mapPt β) (coordinateChange_comp1_transported_addOf J.inv B.G.F B'.G.F hF J.law (pt R d i) (pt R d j) (hr i) (hr j))
    rwa [mapPt_comp1 β _ _ (gp_addOf _ hF' _ _ (hr i) (hr j)), mapPt_addOf β _ _ _ (hr i) (hr j),
      mapPt_addOf β _ _ _ (hcr _ (hr i)) (hcr _ (hr j)), mapPt_comp1 β _ _ (hr i), mapPt_comp1 β _ _ (hr j),
      mapPt_pt, mapPt_pt] at this
  have Ha : ∀ (a : O) (i : Fin 2), comp1 (mapPt β φ) (comp1 (mapPt β (B'.A.act a)) (pt k d i)) =
      comp1 (mapPt β (B.A.act a)) (comp1 (mapPt β φ) (pt k d i)) := by
    intro a i
    have := congrArg (mapPt β) (coordinateChange_comp1_intertwines_action J.inv (B.A.act a) (B'.A.act a) (B.A.const a) (J.act a) (pt R d i) (hr i))
    rwa [mapPt_comp1 β _ _ (gp_comp1 _ _ (B'.A.const a) (hr i)), mapPt_comp1 β _ _ (hr i),
      mapPt_comp1 β _ _ (hcr _ (hr i)), mapPt_comp1 β _ _ (hr i), mapPt_pt] at this
  obtain ⟨-, hx0, hx1⟩ := GlobalTheory.ChartCmp.jRel_axes R d O m B B' φ φi ε J
  refine ⟨?ax0, ?ax1, ?ph1, ?ph2, ?sy, ?ad⟩
  · have e := jeq_map β hx0
    rw [map_ev2 β _ _ gp_zero₂ (hr 0), mapPt_zero, mapPt_pt, hε', map_one,
      gt_ev_expS _ (pair_points_zero_constant hz0 (hp 0)) _ hlam0, ← expS_zero] at e
    have e' := ((GlobalTheory.ChartCmp.jeq_expS_iff_and_exists_log k 1 d m).1 _ _ (cW _ _ hz0 (hp 0) _ hlam0) (map_zero _)).2 e
    have t := congrArg (ev ![mapPt β φ]) hh.ax0
    rw [germEv_germEv_two_points _ (single_point_zero_constant hψ) _ _ hz0 (hp 0), evP_zero _ (single_point_zero_constant hψ),
      evP_pt _ (single_point_zero_constant hψ), gt_ev_zero _ (single_point_zero_constant hψ)] at t
    rw [ev_diff _ hψ _ _ _ _ _ hz0 (hp 0), hh'.ax0, gt_comp1_zero _ hψ, gt_comp1_pt_right]
    refine jeq_of_sub' e' ?_
    erw [t]
    ring
  · have e := jeq_map β hx1
    rw [map_ev2 β _ _ (hr 0) gp_zero₂, mapPt_zero, mapPt_pt, hε', map_one,
      gt_ev_expS _ (pair_points_zero_constant (hp 0) hz0) _ hlam0, ← expS_zero] at e
    have e' := ((GlobalTheory.ChartCmp.jeq_expS_iff_and_exists_log k 1 d m).1 _ _ (cW _ _ (hp 0) hz0 _ hlam0) (map_zero _)).2 e
    have t := congrArg (ev ![mapPt β φ]) hh.ax1
    rw [germEv_germEv_two_points _ (single_point_zero_constant hψ) _ _ (hp 0) hz0, evP_zero _ (single_point_zero_constant hψ),
      evP_pt _ (single_point_zero_constant hψ), gt_ev_zero _ (single_point_zero_constant hψ)] at t
    rw [ev_diff _ hψ _ _ _ _ _ (hp 0) hz0, hh'.ax1, gt_comp1_zero _ hψ, gt_comp1_pt_right]
    refine jeq_of_sub' e' ?_
    erw [t]
    ring
  · have hq0 := hp (n := 3) 0
    have hq1 := hp (n := 3) 1
    have hq2 := hp (n := 3) 2
    have hV := triple_points_zero_constant (hc _ hq0) (hc _ hq1) (hc _ hq2)
    have hA := gp_addOf _ hFk _ _ hq0 hq1
    have hA' := gp_addOf _ hFk' _ _ hq0 hq1
    have hA'' := gp_addOf _ hFk _ _ (hc _ hq0) (hc _ hq1)
    have e1 : MvPowerSeries.map β B.ph1 = _ := hh.ph1
    have e2 : MvPowerSeries.map β B'.ph1 = _ := hh'.ph1
    rw [fk] at e1
    rw [fk'] at e2
    have e := jeq_map β J.ph1
    rw [map_mul, map_mul, map_mul, map_ev2 β _ _ (gp_addOf _ hF' _ _ (hr 0) (hr 1)) (hr 2),
      map_ev2 β _ _ (hr 0) (hr 2), map_ev2 β _ _ (hr 1) (hr 2),
      map_ev3 β _ _ _ (hcr _ (hr 0)) (hcr _ (hr 1)) (hcr _ (hr 2)), mapPt_addOf β _ _ _ (hr 0) (hr 1),
      mapPt_comp1 β _ _ (hr 0), mapPt_comp1 β _ _ (hr 1), mapPt_comp1 β _ _ (hr 2), mapPt_pt, mapPt_pt, mapPt_pt,
      hε', e1, e2, gt_ev_expS _ (pair_points_zero_constant hA' hq2) _ hlam0, gt_ev_expS _ (pair_points_zero_constant hq0 hq2) _ hlam0,
      gt_ev_expS _ (pair_points_zero_constant hq1 hq2) _ hlam0, ← gt_expS_add _ _ (cW _ _ hq0 hq2 _ hlam0) (cW _ _ hq1 hq2 _ hlam0),
      gt_ev_expS _ hV _ (by simp [cW _ _ hq0 hq2 _ hh0, cW _ _ hq1 hq2 _ hh0, cW _ _ hA hq2 _ hh0]),
      gt_ev_sub _ hV, gt_ev_add _ hV, germEv_germEv_two_points _ hV _ _ hq0 hq2, germEv_germEv_two_points _ hV _ _ hq1 hq2, germEv_germEv_two_points _ hV _ _ hA hq2,
      evP_addOf _ hV _ _ _ hq0 hq1, evP_pt _ hV, evP_pt _ hV, evP_pt _ hV] at e
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons] at e
    have e' := jeq_log
      (by simp [cW _ _ hq0 hq2 _ hh0', cW _ _ hq1 hq2 _ hh0', cW _ _ hA' hq2 _ hh0'])
      (cW _ _ hA' hq2 _ hlam0)
      (by simp [cW _ _ (hc _ hq0) (hc _ hq2) _ hh0, cW _ _ (hc _ hq1) (hc _ hq2) _ hh0,
        cW _ _ hA'' (hc _ hq2) _ hh0])
      (by simp [cW _ _ hq0 hq2 _ hlam0, cW _ _ hq1 hq2 _ hlam0]) e
    rw [fk', ev_diff _ hψ _ _ _ _ _ hA' hq2, ev_diff _ hψ _ _ _ _ _ hq0 hq2, ev_diff _ hψ _ _ _ _ _ hq1 hq2, Gl]
    refine jeq_of_sub' e' ?_
    ring
  · have hq0 := hp (n := 3) 0
    have hq1 := hp (n := 3) 1
    have hq2 := hp (n := 3) 2
    have hV := triple_points_zero_constant (hc _ hq0) (hc _ hq1) (hc _ hq2)
    have hA := gp_addOf _ hFk _ _ hq1 hq2
    have hA' := gp_addOf _ hFk' _ _ hq1 hq2
    have hA'' := gp_addOf _ hFk _ _ (hc _ hq1) (hc _ hq2)
    have e1 : MvPowerSeries.map β B.ph2 = _ := hh.ph2
    have e2 : MvPowerSeries.map β B'.ph2 = _ := hh'.ph2
    rw [fk] at e1
    rw [fk'] at e2
    have e := jeq_map β J.ph2
    rw [map_mul, map_mul, map_mul, map_ev2 β _ _ (hr 0) (gp_addOf _ hF' _ _ (hr 1) (hr 2)),
      map_ev2 β _ _ (hr 0) (hr 1), map_ev2 β _ _ (hr 0) (hr 2),
      map_ev3 β _ _ _ (hcr _ (hr 0)) (hcr _ (hr 1)) (hcr _ (hr 2)), mapPt_addOf β _ _ _ (hr 1) (hr 2),
      mapPt_comp1 β _ _ (hr 0), mapPt_comp1 β _ _ (hr 1), mapPt_comp1 β _ _ (hr 2), mapPt_pt, mapPt_pt, mapPt_pt,
      hε', e1, e2, gt_ev_expS _ (pair_points_zero_constant hq0 hA') _ hlam0, gt_ev_expS _ (pair_points_zero_constant hq0 hq1) _ hlam0,
      gt_ev_expS _ (pair_points_zero_constant hq0 hq2) _ hlam0, ← gt_expS_add _ _ (cW _ _ hq0 hq1 _ hlam0) (cW _ _ hq0 hq2 _ hlam0),
      gt_ev_expS _ hV _ (by simp [cW _ _ hq0 hq1 _ hh0, cW _ _ hq0 hq2 _ hh0, cW _ _ hq0 hA _ hh0]),
      gt_ev_sub _ hV, gt_ev_add _ hV, germEv_germEv_two_points _ hV _ _ hq0 hq1, germEv_germEv_two_points _ hV _ _ hq0 hq2, germEv_germEv_two_points _ hV _ _ hq0 hA,
      evP_addOf _ hV _ _ _ hq1 hq2, evP_pt _ hV, evP_pt _ hV, evP_pt _ hV] at e
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons] at e
    have e' := jeq_log
      (by simp [cW _ _ hq0 hq1 _ hh0', cW _ _ hq0 hq2 _ hh0', cW _ _ hq0 hA' _ hh0'])
      (cW _ _ hq0 hA' _ hlam0)
      (by simp [cW _ _ (hc _ hq0) (hc _ hq1) _ hh0, cW _ _ (hc _ hq0) (hc _ hq2) _ hh0,
        cW _ _ (hc _ hq0) hA'' _ hh0])
      (by simp [cW _ _ hq0 hq1 _ hlam0, cW _ _ hq0 hq2 _ hlam0]) e
    rw [fk', ev_diff _ hψ _ _ _ _ _ hq0 hA', ev_diff _ hψ _ _ _ _ _ hq0 hq1, ev_diff _ hψ _ _ _ _ _ hq0 hq2, Gl]
    refine jeq_of_sub' e' ?_
    ring
  · have hq0 := hp (n := 2) 0
    have hq1 := hp (n := 2) 1
    have hV := pair_points_zero_constant (hc _ hq0) (hc _ hq1)
    have e1 : MvPowerSeries.map β B.sy = _ := hh.sy
    have e2 : MvPowerSeries.map β B'.sy = _ := hh'.sy
    have e := jeq_map β J.sy
    rw [map_mul, map_mul, map_ev2 β _ _ (hr 1) (hr 0), map_ev2 β _ _ (hcr _ (hr 0)) (hcr _ (hr 1)),
      mapPt_comp1 β _ _ (hr 0), mapPt_comp1 β _ _ (hr 1), mapPt_pt, mapPt_pt,
      hε', e1, e2, gt_ev_expS _ (pair_points_zero_constant hq1 hq0) _ hlam0,
      gt_ev_expS _ hV _ (by simp [cW _ _ hq1 hq0 _ hh0, hh0]),
      gt_ev_sub _ hV, germEv_germEv_two_points _ hV _ _ hq1 hq0, evP_pt _ hV, evP_pt _ hV] at e
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at e
    have e' := jeq_log
      (by simp [cW _ _ hq1 hq0 _ hh0', hh0']) hlam0
      (by simp [cW _ _ (hc _ hq0) (hc _ hq1) _ hh0, cW _ _ (hc _ hq1) (hc _ hq0) _ hh0])
      (cW _ _ hq1 hq0 _ hlam0) e
    rw [ev_diff _ hψ _ _ _ _ _ hq1 hq0]
    refine jeq_of_sub e' ?_
    ring
  · intro a
    have hq0 := hp (n := 2) 0
    have hq1 := hp (n := 2) 1
    have hV := pair_points_zero_constant (hc _ hq0) (hc _ hq1)
    have hB'a : GP (B'.A.act a) := B'.A.const a
    have hB's : GP (B'.A.act (star a)) := B'.A.const (star a)
    have hBa := constantCoeff_mapPt_eq_zero β _ (show GP (B.A.act a) from B.A.const a)
    have hBs := constantCoeff_mapPt_eq_zero β _ (show GP (B.A.act (star a)) from B.A.const (star a))
    have hx0 := gp_comp1 _ _ (constantCoeff_mapPt_eq_zero β _ hB'a) hq0
    have hx1 := gp_comp1 _ _ (constantCoeff_mapPt_eq_zero β _ hB's) hq1
    have hy0 := gp_comp1 _ _ hBa hq0
    have hy1 := gp_comp1 _ _ hBs hq1
    have hw0 := gp_comp1 _ _ hBa (hc _ hq0)
    have hw1 := gp_comp1 _ _ hBs (hc _ hq1)
    have e1 : MvPowerSeries.map β (B.ad a) = _ := hh.ad a
    have e2 : MvPowerSeries.map β (B'.ad a) = _ := hh'.ad a
    rw [ak, ak] at e1
    rw [ak', ak'] at e2
    have e := jeq_map β (J.ad a)
    rw [map_mul, map_mul, map_ev2 β _ _ (hr 0) (gp_comp1 _ _ hB's (hr 1)),
      map_ev2 β _ _ (gp_comp1 _ _ hB'a (hr 0)) (hr 1), map_ev2 β _ _ (hcr _ (hr 0)) (hcr _ (hr 1)),
      mapPt_comp1 β φ _ (hr 0), mapPt_comp1 β φ _ (hr 1), mapPt_comp1 β _ _ (hr 0), mapPt_comp1 β _ _ (hr 1),
      mapPt_pt, mapPt_pt,
      hε', e1, e2, gt_ev_expS _ (pair_points_zero_constant hq0 hx1) _ hlam0, gt_ev_expS _ (pair_points_zero_constant hx0 hq1) _ hlam0,
      gt_ev_expS _ hV _ (by simp [cW _ _ hy0 hq1 _ hh0, cW _ _ hq0 hy1 _ hh0]),
      gt_ev_sub _ hV, germEv_germEv_two_points _ hV _ _ hy0 hq1, germEv_germEv_two_points _ hV _ _ hq0 hy1, evP_comp1 _ hV _ _ hq0,
      evP_comp1 _ hV _ _ hq1, evP_pt _ hV, evP_pt _ hV] at e
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at e
    have e' := jeq_log
      (by simp [cW _ _ hx0 hq1 _ hh0', cW _ _ hq0 hx1 _ hh0']) (cW _ _ hq0 hx1 _ hlam0)
      (by simp [cW _ _ hw0 (hc _ hq1) _ hh0, cW _ _ (hc _ hq0) hw1 _ hh0])
      (cW _ _ hx0 hq1 _ hlam0) e
    rw [ak', ak', ev_diff _ hψ _ _ _ _ _ hx0 hq1, ev_diff _ hψ _ _ _ _ _ hq0 hx1, Ha, Ha]
    refine jeq_of_sub e' ?_
    ring

end GlobalTheory.ChartCmp.GaugeDiff
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.canonicalGauge_difference_biadditive_jet : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (m : ℕ) (B B' : FB R d O) (φ φi : Pt R 1 d) (ε : PS R 2 d), JRel m B B' φ φi ε → ∀ (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (h h' lam : PS k 2 d), B.IsCanonGauge k h → B'.IsCanonGauge k h' → MvPowerSeries.constantCoeff lam = 0 → FB.expS k lam = FB.toK k ε → Biadd m B' k (h' - ev (n := 2) ![comp1 (fun i => FB.toK k (φ i)) (pt k (n := 2) d 0), comp1 (fun i => FB.toK k (φ i)) (pt k (n := 2) d 1)] h - lam) := by
  atlas_forward_decl GlobalTheory.ChartCmp.GaugeDiff.biadd_gauge_diff
end

section
section
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp
namespace GlobalTheory.ChartCmp.BilAdd

variable {k : Type} [CommRing k] {d : ℕ}

theorem hasSubst_pts {n l : ℕ} (a : Fin l → Pt k n d) (h : ∀ j i, MvPowerSeries.constantCoeff (a j i) = 0) :
    MvPowerSeries.HasSubst (fun p : Fin l × Fin d => a p.1 p.2) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero fun p => h p.1 p.2

theorem ev_add {n l : ℕ} (a : Fin l → Pt k n d) (h : ∀ j i, MvPowerSeries.constantCoeff (a j i) = 0) (f g : PS k l d) :
    ev a (f + g) = ev a f + ev a g :=
  MvPowerSeries.subst_add (hasSubst_pts a h) f g

theorem ev_pt {n l : ℕ} (a : Fin l → Pt k n d) (h : ∀ j i, MvPowerSeries.constantCoeff (a j i) = 0) (j : Fin l) (i : Fin d) :
    ev a (pt k d j i) = a j i :=
  MvPowerSeries.subst_X (hasSubst_pts a h) (j, i)

theorem ev_ev {n l r : ℕ} (a : Fin l → Pt k n d) (b : Fin n → Pt k r d)
    (ha : ∀ j i, MvPowerSeries.constantCoeff (a j i) = 0) (hb : ∀ j i, MvPowerSeries.constantCoeff (b j i) = 0)
    (f : PS k l d) : ev b (ev a f) = ev (fun j i => ev b (a j i)) f :=
  MvPowerSeries.subst_comp_subst_apply (hasSubst_pts a ha) (hasSubst_pts b hb) f

theorem const_pt {n : ℕ} (j : Fin n) (i : Fin d) : MvPowerSeries.constantCoeff (pt k d j i) = 0 :=
  MvPowerSeries.constantCoeff_X _

theorem ev_id {n : ℕ} (f : PS k n d) : ev (fun j => pt k d j) f = f := by
  have := MvPowerSeries.subst_self (σ := Fin n × Fin d) (R := k)
  exact congrFun this f

def degIn (j : Fin 2) (e : Fin 2 × Fin d →₀ ℕ) : ℕ := ∑ i, e (j, i)

theorem coeff_double (j : Fin 2) (g : PS k 2 d) (e : Fin 2 × Fin d →₀ ℕ) :
    MvPowerSeries.coeff e (ev (n := 2) (fun l => if l = j then pt k d l + pt k d l else pt k d l) g) =
      2 ^ degIn j e * MvPowerSeries.coeff e g := by
  have h : ev (n := 2) (fun l => if l = j then pt k d l + pt k d l else pt k d l) g =
      MvPowerSeries.rescale (fun p : Fin 2 × Fin d => if p.1 = j then (2 : k) else 1) g := by
    rw [MvPowerSeries.rescale_eq_subst]
    unfold ev
    congr 1
    funext p
    by_cases hp : p.1 = j
    · subst hp
      simp [pt, two_smul]
    · simp [hp, pt]
  rw [h, MvPowerSeries.coeff_rescale]
  congr 1
  rw [Finsupp.prod_fintype _ _ (by simp), Fintype.prod_prod_type, degIn, ← Finset.prod_pow_eq_pow_sum,
    Finset.prod_eq_single j]
  · simp
  · intro b _ hb; simp [hb]
  · simp

theorem eq_zero_of_double [Algebra ℚ k] {a : ℕ} (ha : a ≠ 1) {c : k} (h : 2 ^ a * c = c + c) : c = 0 := by
  have h0 : ((2 : ℚ) ^ a - 2) ≠ 0 := by
    intro h
    apply ha
    have : (2 : ℚ) ^ a = 2 ^ 1 := by linarith
    exact (pow_right_injective₀ (by norm_num) (by norm_num)) this
  have hu : IsUnit ((2 : k) ^ a - 2) := by
    have := (IsUnit.mk0 _ h0).map (algebraMap ℚ k)
    simpa [map_ofNat] using this
  apply hu.mul_right_eq_zero.mp
  linear_combination h

theorem exists_single {e : Fin 2 × Fin d →₀ ℕ} (h0 : degIn 0 e = 1) (h1 : degIn 1 e = 1) :
    ∃ i j, e = Finsupp.single ((0 : Fin 2), i) 1 + Finsupp.single ((1 : Fin 2), j) 1 := by
  have key : ∀ f : Fin d → ℕ, ∑ i, f i = 1 → ∃ i, ∀ i', f i' = if i = i' then 1 else 0 := by
    intro f hf
    obtain ⟨i, hi⟩ : ∃ i, f i ≠ 0 := by
      by_contra hc
      push Not at hc
      simp [hc] at hf
    refine ⟨i, fun i' => ?_⟩
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at hf
    split_ifs with h
    · subst h
      omega
    · have := Finset.single_le_sum (f := f) (fun _ _ => Nat.zero_le _)
        (Finset.mem_erase.mpr ⟨fun hh => h hh.symm, Finset.mem_univ i'⟩ : i' ∈ Finset.univ.erase i)
      omega
  obtain ⟨i, hi⟩ := key _ h0
  obtain ⟨j, hj⟩ := key _ h1
  refine ⟨i, j, ?_⟩
  ext ⟨l, p⟩
  fin_cases l
  · simp [hi, Finsupp.single_apply]
  · simp [hj, Finsupp.single_apply]

theorem coeff_bilSer (β : Matrix (Fin d) (Fin d) k) (e : Fin 2 × Fin d →₀ ℕ) :
    MvPowerSeries.coeff e (bilSer β (pt k (n := 2) d 0) (pt k (n := 2) d 1)) =
      ∑ i, ∑ j, if e = Finsupp.single ((0 : Fin 2), i) 1 + Finsupp.single ((1 : Fin 2), j) 1 then β i j else 0 := by
  simp only [bilSer, map_sum, pt, MvPowerSeries.coeff_C_mul, MvPowerSeries.X, MvPowerSeries.monomial_mul_monomial,
    MvPowerSeries.coeff_monomial]
  simp

theorem single_inj {i j i' j' : Fin d}
    (h : (Finsupp.single ((0 : Fin 2), i) 1 + Finsupp.single ((1 : Fin 2), j) 1 : Fin 2 × Fin d →₀ ℕ) =
      Finsupp.single ((0 : Fin 2), i') 1 + Finsupp.single ((1 : Fin 2), j') 1) : i = i' ∧ j = j' := by
  have h0 := DFunLike.congr_fun h (0, i)
  have h1 := DFunLike.congr_fun h (1, j)
  simp [Finsupp.single_apply] at h0 h1
  exact ⟨h0.symm, h1.symm⟩

theorem jeq_bil_of_double [Algebra ℚ k] (m : ℕ) (g : PS k 2 d)
    (h : ∀ j : Fin 2, JEq m (ev (n := 2) (fun l => if l = j then pt k d l + pt k d l else pt k d l) g) (g + g)) :
    JEq m g (bilSer (fun i j => MvPowerSeries.coeff (Finsupp.single ((0 : Fin 2), i) 1 + Finsupp.single ((1 : Fin 2), j) 1) g)
      (pt k (n := 2) d 0) (pt k (n := 2) d 1)) := by
  intro e he
  refine Eq.trans ?_ (coeff_bilSer _ e).symm
  by_cases hex : ∃ i j, e = Finsupp.single ((0 : Fin 2), i) 1 + Finsupp.single ((1 : Fin 2), j) 1
  · obtain ⟨i, j, rfl⟩ := hex
    rw [Finset.sum_eq_single i, Finset.sum_eq_single j, if_pos rfl]
    · intro b _ hb
      exact if_neg fun hh => hb (single_inj hh).2.symm
    · simp
    · intro b _ hb
      exact Finset.sum_eq_zero fun c _ => if_neg fun hh => hb (single_inj hh).1.symm
    · simp
  · have hz : MvPowerSeries.coeff e g = 0 := by
      have : ∃ j, degIn j e ≠ 1 := by
        by_contra hc
        push Not at hc
        exact hex (exists_single (hc 0) (hc 1))
      obtain ⟨j, hj⟩ := this
      have := h j e he
      rw [coeff_double, map_add] at this
      exact eq_zero_of_double hj this
    rw [hz]
    symm
    exact Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => if_neg fun hh => hex ⟨i, j, hh⟩

theorem ev_pair (b : Fin 3 → Pt k 2 d) (hb : ∀ j i, MvPowerSeries.constantCoeff (b j i) = 0) (g : PS k 2 d)
    (u v : Pt k 3 d) (hu : ∀ i, MvPowerSeries.constantCoeff (u i) = 0) (hv : ∀ i, MvPowerSeries.constantCoeff (v i) = 0) :
    ev b (ev ![u, v] g) = ev ![fun i => ev b (u i), fun i => ev b (v i)] g := by
  rw [ev_ev _ _ _ hb]
  · congr 1
    funext j
    fin_cases j <;> rfl
  · intro j i
    fin_cases j
    · exact hu i
    · exact hv i

theorem jeq_bilSer_of_biadditive : ∀ (k : Type) [CommRing k] [Algebra ℚ k] (d m : ℕ) (g : PS k 2 d), JEq m (ev (n := 3) ![pt k (n := 3) d 0 + pt k (n := 3) d 1, pt k (n := 3) d 2] g) (ev (n := 3) ![pt k (n := 3) d 0, pt k (n := 3) d 2] g + ev (n := 3) ![pt k (n := 3) d 1, pt k (n := 3) d 2] g) → JEq m (ev (n := 3) ![pt k (n := 3) d 0, pt k (n := 3) d 1 + pt k (n := 3) d 2] g) (ev (n := 3) ![pt k (n := 3) d 0, pt k (n := 3) d 1] g + ev (n := 3) ![pt k (n := 3) d 0, pt k (n := 3) d 2] g) → JEq m g (bilSer (fun i j => MvPowerSeries.coeff (Finsupp.single ((0 : Fin 2), i) 1 + Finsupp.single ((1 : Fin 2), j) 1) g) (pt k (n := 2) d 0) (pt k (n := 2) d 1)) := by
  intro k _ _ d m g h1 h2
  have hsub := (GlobalTheory.ChartCmp.JCalc.jeq_calculus k m).2.2.2.1
  have hid : ev (n := 2) ![pt k (n := 2) d 0, pt k (n := 2) d 1] g = g := by
    refine Eq.trans ?_ (ev_id g)
    congr 1
    funext j
    fin_cases j <;> rfl
  have hc : ∀ (s : Fin 3) i, MvPowerSeries.constantCoeff (pt k (n := 3) d s i) = 0 := fun s i => const_pt s i
  have hc2 : ∀ (s t : Fin 3) i, MvPowerSeries.constantCoeff ((pt k (n := 3) d s + pt k (n := 3) d t) i) = 0 := by
    intro s t i
    simp [hc]
  apply jeq_bil_of_double
  intro j
  fin_cases j
  · have hb : ∀ (s : Fin 3) i, MvPowerSeries.constantCoeff
        ((![pt k (n := 2) d 0, pt k (n := 2) d 0, pt k (n := 2) d 1] : Fin 3 → Pt k 2 d) s i) = 0 := by
      intro s i
      fin_cases s <;> exact const_pt _ _
    have := hsub d 3 2 _ _ _ _ hb hb (fun _ _ => JEq.refl _ _) h1
    rw [ev_add _ hb, ev_pair _ hb _ _ _ (hc2 _ _) (hc _), ev_pair _ hb _ _ _ (hc _) (hc _),
      ev_pair _ hb _ _ _ (hc _) (hc _)] at this
    simp only [Pi.add_apply, ev_add _ hb, ev_pt _ hb] at this
    convert this using 2
    · funext l
      fin_cases l <;> rfl
    · exact hid.symm
    · exact hid.symm
  · have hb : ∀ (s : Fin 3) i, MvPowerSeries.constantCoeff
        ((![pt k (n := 2) d 0, pt k (n := 2) d 1, pt k (n := 2) d 1] : Fin 3 → Pt k 2 d) s i) = 0 := by
      intro s i
      fin_cases s <;> exact const_pt _ _
    have := hsub d 3 2 _ _ _ _ hb hb (fun _ _ => JEq.refl _ _) h2
    rw [ev_add _ hb, ev_pair _ hb _ _ _ (hc _) (hc2 _ _), ev_pair _ hb _ _ _ (hc _) (hc _),
      ev_pair _ hb _ _ _ (hc _) (hc _)] at this
    simp only [Pi.add_apply, ev_add _ hb, ev_pt _ hb] at this
    convert this using 2
    · funext l
      fin_cases l <;> rfl
    · exact hid.symm
    · exact hid.symm

end GlobalTheory.ChartCmp.BilAdd
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jetEq_bilinearSeries_of_biadditive : ∀ (k : Type) [CommRing k] [Algebra ℚ k] (d m : ℕ) (g : PS k 2 d), JEq m (ev (n := 3) ![pt k (n := 3) d 0 + pt k (n := 3) d 1, pt k (n := 3) d 2] g) (ev (n := 3) ![pt k (n := 3) d 0, pt k (n := 3) d 2] g + ev (n := 3) ![pt k (n := 3) d 1, pt k (n := 3) d 2] g) → JEq m (ev (n := 3) ![pt k (n := 3) d 0, pt k (n := 3) d 1 + pt k (n := 3) d 2] g) (ev (n := 3) ![pt k (n := 3) d 0, pt k (n := 3) d 1] g + ev (n := 3) ![pt k (n := 3) d 0, pt k (n := 3) d 2] g) → JEq m g (bilSer (fun i j => MvPowerSeries.coeff (Finsupp.single ((0 : Fin 2), i) 1 + Finsupp.single ((1 : Fin 2), j) 1) g) (pt k (n := 2) d 0) (pt k (n := 2) d 1)) := by
  atlas_forward_decl GlobalTheory.ChartCmp.BilAdd.jeq_bilSer_of_biadditive
end

section
set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing

namespace GlobalTheory.LogLinear

variable {k : Type} [CommRing k] {d : ℕ}

theorem eq_zero_of_additive [Algebra ℚ k] (G : FGLaw k d) (g : PS k 1 d)
    (hadd : ev (n := 2) ![G.add (pt k d 0) (pt k d 1)] g =
      ev (n := 2) ![pt k d 0] g + ev (n := 2) ![pt k d 1] g)
    (hlin : ∀ i, coeff (Finsupp.single ((0 : Fin 1), i) 1) g = 0) : g = 0 := by
  have hc {n : ℕ} (x : Pt k n d) (y : Fin 0 → Pt k n d) :
      (Fin.cons x y : Fin (0 + 1) → Pt k n d) = ![x] := by
    funext j
    fin_cases j
    rfl
  refine GlobalTheory.AdditiveSeries.eq_zero_of_additive_of_pderiv k d G 0 g ?_ fun i => ?_
  · rw [hc, hc, hc]
    exact hadd
  · rw [hc]
    ext m
    obtain rfl : m = 0 := Subsingleton.elim _ _
    rw [coeff_zero_eq_constantCoeff_apply, gt_const_ev_eq _ (single_point_zero_constant gp_zero₂),
      ← coeff_zero_eq_constantCoeff_apply, coeff_pderiv, zero_add]
    simp [hlin i]

theorem ev_sum_C_mul {m n : ℕ} (V : Fin m → Pt k n d) (hV : ∀ j, GP (V j)) (c : Fin d → k)
    (f : Fin d → PS k m d) : ev V (∑ j, C (c j) * f j) = ∑ j, C (c j) * ev V (f j) := by
  unfold ev
  rw [← coe_substAlgHom (gt_hasSubst V hV), map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, coe_substAlgHom, subst_C]

theorem dLin_comp1 (φ ψ : Pt k 1 d) (hψ : GP ψ) : dLin (comp1 φ ψ) = dLin φ * dLin ψ := by
  ext i j
  refine (FormalCalc.coeff_single_subst
    (a := fun p : Fin 1 × Fin d => (![ψ] : Fin 1 → Pt k 1 d) p.1 p.2)
    (fun p => single_point_zero_constant hψ p.1 p.2) (φ i) _).trans ?_
  rw [Fintype.sum_prod_type, Fin.sum_univ_one, Matrix.mul_apply]
  rfl

theorem germ_comp_additive_at_points {n : ℕ} (G : FGLaw k d) (ψ : Pt k 1 d)
    (hψ : comp1 ψ (G.add (pt k (n := 2) d 0) (pt k (n := 2) d 1)) =
      comp1 ψ (pt k (n := 2) d 0) + comp1 ψ (pt k (n := 2) d 1))
    (a b : Pt k n d) (ha : GP a) (hb : GP b) :
    comp1 ψ (G.add a b) = comp1 ψ a + comp1 ψ b := by
  have hV := pair_points_zero_constant ha hb
  have e := congrArg (evP ![a, b]) hψ
  have e2 : ∀ u v : Pt k 2 d, evP ![a, b] (u + v) = evP ![a, b] u + evP ![a, b] v := fun u v =>
    funext fun i => gt_ev_add _ hV _ _
  rw [e2, evP_comp1 _ hV _ _ (gp_addOf _ G.const _ _ (gp_pt 0) (gp_pt 1)),
    evP_addOf _ hV _ _ _ (gp_pt 0) (gp_pt 1), evP_comp1 _ hV _ _ (gp_pt 0),
    evP_comp1 _ hV _ _ (gp_pt 1), evP_pt _ hV, evP_pt _ hV] at e
  exact e

theorem formalGroup_log_endomorphism_linear :
    ∀ (k : Type) [CommRing k] [Algebra ℚ k] (d : ℕ) (G : FGLaw k d) (ℓ α : Pt k 1 d),
      (∀ i, MvPowerSeries.constantCoeff (ℓ i) = 0) → dLin ℓ = 1 →
      comp1 ℓ (G.add (pt k (n := 2) d 0) (pt k (n := 2) d 1)) =
        comp1 ℓ (pt k (n := 2) d 0) + comp1 ℓ (pt k (n := 2) d 1) →
      (∀ i, MvPowerSeries.constantCoeff (α i) = 0) →
      comp1 α (G.add (pt k (n := 2) d 0) (pt k (n := 2) d 1)) =
        G.add (comp1 α (pt k (n := 2) d 0)) (comp1 α (pt k (n := 2) d 1)) →
      ∀ i, comp1 ℓ α i = ∑ j, MvPowerSeries.C (dLin α i j) * ℓ j := by
  intro k _ _ d G ℓ α _ h1 hadd hα hhom i
  have hS : GP (G.add (pt k (n := 2) d 0) (pt k (n := 2) d 1)) :=
    gp_addOf _ G.const _ _ (gp_pt _) (gp_pt _)
  have hev (a : Pt k 2 d) (ha : GP a) :
      ev ![a] (comp1 ℓ α i - ∑ j, C (dLin α i j) * ℓ j) =
        comp1 ℓ (comp1 α a) i - ∑ j, C (dLin α i j) * comp1 ℓ a j := by
    rw [gt_ev_sub _ (single_point_zero_constant ha), ev_sum_C_mul _ (single_point_zero_constant ha), ← gt_comp1_comp1 ℓ α hα a ha]
    rfl
  rw [← sub_eq_zero]
  refine eq_zero_of_additive G _ ?_ fun l => ?_
  · rw [hev _ hS, hev _ (gp_pt _), hev _ (gp_pt _), hhom, hadd,
      germ_comp_additive_at_points G ℓ hadd _ _ (gp_comp1 α _ hα (gp_pt _)) (gp_comp1 α _ hα (gp_pt _))]
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
    ring
  · have h2 : dLin (comp1 ℓ α) i l = (dLin α * dLin ℓ) i l := by
      rw [dLin_comp1 ℓ α hα, h1, one_mul, mul_one]
    rw [map_sub, map_sum, sub_eq_zero]
    simp only [coeff_C_mul]
    exact h2

end GlobalTheory.LogLinear
end
end

section
section
set_option autoImplicit false
noncomputable section
open MvPowerSeries
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin IsInvPair)
open GlobalTheory.ChartCmp GlobalTheory.FBMap

namespace GlobalTheory.ChartBilin

variable {k : Type} [CommRing k] {d : ℕ}

def evP {m n : ℕ} (b : Fin m → Pt k n d) (u : Pt k m d) : Pt k n d := fun i => ev b (u i)

def lin {n : ℕ} (A : Matrix (Fin d) (Fin d) k) (u : Pt k n d) : Pt k n d := fun i => ∑ j, C (A i j) * u j

theorem nc1 {n : ℕ} {u : Pt k n d} (hu : NoConst u) : ∀ j, NoConst (![u] j) := by
  intro j; fin_cases j; exact hu

theorem nc2 {n : ℕ} {u v : Pt k n d} (hu : NoConst u) (hv : NoConst v) : ∀ j, NoConst (![u, v] j) := by
  intro j; fin_cases j; exacts [hu, hv]

theorem nc3 {n : ℕ} {u v w : Pt k n d} (hu : NoConst u) (hv : NoConst v) (hw : NoConst w) :
    ∀ j, NoConst (![u, v, w] j) := by
  intro j; fin_cases j; exacts [hu, hv, hw]

theorem nc_add {n : ℕ} {u v : Pt k n d} (hu : NoConst u) (hv : NoConst v) : NoConst (u + v) :=
  fun i => by simp [hu i, hv i]

theorem ev_ev {l m n : ℕ} {b : Fin m → Pt k n d} (hb : ∀ j, NoConst (b j)) {a : Fin l → Pt k m d}
    (ha : ∀ j, NoConst (a j)) (f : PS k l d) : ev b (ev a f) = ev (fun j => evP b (a j)) f :=
  subst_comp_subst_apply (hasSubst_of ha) (hasSubst_of hb) f

theorem germEv_germEv_two_points {m n : ℕ} {b : Fin m → Pt k n d} (hb : ∀ j, NoConst (b j)) {u v : Pt k m d}
    (hu : NoConst u) (hv : NoConst v) (f : PS k 2 d) : ev b (ev ![u, v] f) = ev ![evP b u, evP b v] f := by
  rw [ev_ev hb (nc2 hu hv)]
  congr 1; funext j; fin_cases j <;> rfl

theorem evalPoints_comp {m n : ℕ} {b : Fin m → Pt k n d} (hb : ∀ j, NoConst (b j)) (φ : Pt k 1 d) {u : Pt k m d}
    (hu : NoConst u) : evP b (comp1 φ u) = comp1 φ (evP b u) := by
  funext i
  change ev b (ev ![u] (φ i)) = ev ![evP b u] (φ i)
  rw [ev_ev hb (nc1 hu)]
  congr 1; funext j; fin_cases j; rfl

theorem evalPoints_formalGroupAdd {m n : ℕ} {b : Fin m → Pt k n d} (hb : ∀ j, NoConst (b j)) (F : Pt k 2 d) {u v : Pt k m d}
    (hu : NoConst u) (hv : NoConst v) : evP b (addOf F u v) = addOf F (evP b u) (evP b v) :=
  funext fun i => germEv_germEv_two_points hb hu hv (F i)

theorem evalPoints_coordinatePoint {m n : ℕ} {b : Fin m → Pt k n d} (hb : ∀ j, NoConst (b j)) (j : Fin m) :
    evP b (pt k d j) = b j :=
  funext fun i => subst_X (hasSubst_of hb) (j, i)

theorem ev_add' {m n : ℕ} {b : Fin m → Pt k n d} (hb : ∀ j, NoConst (b j)) (f g : PS k m d) :
    ev b (f + g) = ev b f + ev b g := subst_add (hasSubst_of hb) f g

theorem evalPoints_add {m n : ℕ} {b : Fin m → Pt k n d} (hb : ∀ j, NoConst (b j)) (u v : Pt k m d) :
    evP b (u + v) = evP b u + evP b v := funext fun i => ev_add' hb (u i) (v i)

theorem evalPoints_linear {m n : ℕ} {b : Fin m → Pt k n d} (hb : ∀ j, NoConst (b j)) (A : Matrix (Fin d) (Fin d) k)
    (u : Pt k m d) : evP b (lin A u) = lin A (evP b u) := by
  funext i
  simp only [evP, lin, ev]
  rw [← coe_substAlgHom (hasSubst_of hb), map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, coe_substAlgHom, subst_C]

theorem ev_bilSer {m n : ℕ} {b : Fin m → Pt k n d} (hb : ∀ j, NoConst (b j)) (β : Matrix (Fin d) (Fin d) k)
    (u v : Pt k m d) : ev b (bilSer β u v) = bilSer β (evP b u) (evP b v) := by
  simp only [evP, bilSer, ev]
  rw [← coe_substAlgHom (hasSubst_of hb), map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, map_mul, coe_substAlgHom, subst_C]

theorem ev_self2 (f : PS k 2 d) : ev (n := 2) ![pt k d 0, pt k d 1] f = f := by
  have e : (fun p : Fin 2 × Fin d => (![pt k (n := 2) d 0, pt k d 1] p.1) p.2) = X := by
    funext p
    obtain ⟨j, i⟩ := p
    fin_cases j <;> rfl
  rw [ev, e, subst_self]
  rfl

theorem germComp1_germComp1_eq_substitute {n : ℕ} (φ : Pt k 1 d) {ψ : Pt k 1 d} (hψ : NoConst ψ) {u : Pt k n d} (hu : NoConst u) :
    comp1 φ (comp1 ψ u) = evP ![u] (comp1 φ ψ) := (evalPoints_comp (nc1 hu) φ hψ).symm

theorem germComp1_cancel_of_inverse {n : ℕ} {φ ψ : Pt k 1 d} (hψ : NoConst ψ) (h : comp1 φ ψ = pt k (n := 1) d 0) {u : Pt k n d}
    (hu : NoConst u) : comp1 φ (comp1 ψ u) = u := by
  rw [germComp1_germComp1_eq_substitute φ hψ hu, h, evalPoints_coordinatePoint (nc1 hu)]
  rfl

theorem germComp1_zero_of_noConstantCoeff {n : ℕ} {φ : Pt k 1 d} (hφ : NoConst φ) : comp1 φ (0 : Pt k n d) = 0 := by
  funext i
  change subst (fun p : Fin 1 × Fin d => (![(0 : Pt k n d)] p.1) p.2) (φ i) = 0
  have e : (fun p : Fin 1 × Fin d => (![(0 : Pt k n d)] p.1) p.2) = 0 := by
    funext p; simp
  rw [e]
  exact subst_zero_of_constantCoeff_zero (hφ i)

theorem bilSer_zero_left {n : ℕ} (β : Matrix (Fin d) (Fin d) k) (v : Pt k n d) : bilSer β 0 v = 0 := by
  simp [bilSer]

theorem bilSer_zero_right {n : ℕ} (β : Matrix (Fin d) (Fin d) k) (u : Pt k n d) : bilSer β u 0 = 0 := by
  simp [bilSer]

theorem bilSer_add_left {n : ℕ} (β : Matrix (Fin d) (Fin d) k) (u u' v : Pt k n d) :
    bilSer β (u + u') v = bilSer β u v + bilSer β u' v := by
  simp only [bilSer, Pi.add_apply, add_mul, mul_add, Finset.sum_add_distrib]

theorem bilSer_add_right {n : ℕ} (β : Matrix (Fin d) (Fin d) k) (u v v' : Pt k n d) :
    bilSer β u (v + v') = bilSer β u v + bilSer β u v' := by
  simp only [bilSer, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem bilSer_swap {n : ℕ} (β : Matrix (Fin d) (Fin d) k) (u v : Pt k n d) :
    bilSer β v u = bilSer β.transpose u v := by
  simp only [bilSer, Matrix.transpose_apply]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem bilSer_lin_right {n : ℕ} (β A : Matrix (Fin d) (Fin d) k) (u v : Pt k n d) :
    bilSer β u (lin A v) = bilSer (β * A) u v := by
  simp only [bilSer, lin, Matrix.mul_apply, map_sum, map_mul, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => by ring

theorem bilSer_lin_left {n : ℕ} (β A : Matrix (Fin d) (Fin d) k) (u v : Pt k n d) :
    bilSer β (lin A u) v = bilSer (A.transpose * β) u v := by
  rw [bilSer_swap, bilSer_lin_right, bilSer_swap, Matrix.transpose_mul, Matrix.transpose_transpose]

theorem coeff_bilSer (β : Matrix (Fin d) (Fin d) k) (i j : Fin d) :
    coeff (Finsupp.single ((0 : Fin 2), i) 1 + Finsupp.single ((1 : Fin 2), j) 1)
      (bilSer β (pt k (n := 2) d 0) (pt k d 1)) = β i j := by
  classical
  have key : ∀ i' j' : Fin d, (Finsupp.single ((0 : Fin 2), i) 1 + Finsupp.single ((1 : Fin 2), j) 1 : Fin 2 × Fin d →₀ ℕ) =
      Finsupp.single ((0 : Fin 2), i') 1 + Finsupp.single ((1 : Fin 2), j') 1 ↔ i = i' ∧ j = j' := by
    intro i' j'
    refine ⟨fun h => ⟨?_, ?_⟩, by rintro ⟨rfl, rfl⟩; rfl⟩
    · have := DFunLike.congr_fun h (0, i)
      by_contra hne
      simp [Finsupp.single_apply, Ne.symm hne] at this
    · have := DFunLike.congr_fun h (1, j)
      by_contra hne
      simp [Finsupp.single_apply, Ne.symm hne] at this
  simp only [bilSer, pt, map_sum, coeff_C_mul, X_def, monomial_mul_monomial, coeff_monomial, key]
  rw [Finset.sum_eq_single i, Finset.sum_eq_single j]
  · simp
  · intro b _ hb; simp [Ne.symm hb]
  · simp
  · intro b _ hb; simp [Ne.symm hb]
  · simp

theorem eq_of_jEq_bilSer {m : ℕ} (hm : 2 ≤ m) {β γ : Matrix (Fin d) (Fin d) k}
    (h : JEq m (bilSer β (pt k (n := 2) d 0) (pt k d 1)) (bilSer γ (pt k (n := 2) d 0) (pt k d 1))) : β = γ := by
  ext i j
  rw [← coeff_bilSer β i j, ← coeff_bilSer γ i j]
  exact h _ (by simpa using hm)

theorem jEq_symm {σ : Type} {m : ℕ} {f g : MvPowerSeries σ k} (h : JEq m f g) : JEq m g f :=
  fun e he => (h e he).symm

theorem jEq_trans {σ : Type} {m : ℕ} {f g h : MvPowerSeries σ k} (h1 : JEq m f g) (h2 : JEq m g h) : JEq m f h :=
  fun e he => (h1 e he).trans (h2 e he)

theorem jEq_of_eq {σ : Type} {m : ℕ} {f g : MvPowerSeries σ k} (h : f = g) : JEq m f g := h ▸ JEq.refl m f

theorem jEq_ev {m l n : ℕ} {b : Fin l → Pt k n d} (hb : ∀ j, NoConst (b j)) {f g : PS k l d} (h : JEq m f g) :
    JEq m (ev b f) (ev b g) :=
  (GlobalTheory.ChartCmp.JCalc.jeq_calculus k m).2.2.2.1 d l n b b f g hb hb (fun _ _ => JEq.refl _ _) h

theorem exists_biadd_jEq : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB R d O) (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (m : ℕ), 2 ≤ m → ∀ g : PS k 2 d, Biadd m B k g → ∃ g' : PS k 2 d, (∀ m', Biadd m' B k g') ∧ JEq m g g' := by
  intro R _ d O _ _ B k _ _ _ m hm g hg
  set G : FGLaw k d := mapLaw (algebraMap R k) B.G with hG
  set A : OAct O G := mapAct (algebraMap R k) B.A with hA
  obtain ⟨ℓ, hℓ, hlin, hadd⟩ := GlobalTheory.FormalLog.logSt k d G
  obtain ⟨e, -, he, hle, hel⟩ := GlobalTheory.ChartInv.exists_isInvPair k d ℓ hℓ
    (by rw [hlin, Matrix.det_one]; exact isUnit_one)
  replace hℓ : NoConst ℓ := hℓ
  replace he : NoConst e := he
  have hF : NoConst (B.FK k) := G.const
  have hα : ∀ a, NoConst (B.actK k a) := A.const
  have hp : ∀ {n : ℕ} (j : Fin n), NoConst (pt k d j) := nc_pt
  have hlog : ∀ {n : ℕ} {u v : Pt k n d}, NoConst u → NoConst v →
      comp1 ℓ (addOf (B.FK k) u v) = comp1 ℓ u + comp1 ℓ v := by
    intro n u v hu hv
    have h0 : comp1 ℓ (addOf (B.FK k) (pt k (n := 2) d 0) (pt k (n := 2) d 1)) =
      comp1 ℓ (pt k (n := 2) d 0) + comp1 ℓ (pt k (n := 2) d 1) := hadd
    have hb := nc2 hu hv
    have h1 := congrArg (evP ![u, v]) h0
    rw [evalPoints_add hb, evalPoints_comp hb ℓ (nc_addOf hF (hp 0) (hp 1)), evalPoints_formalGroupAdd hb _ (hp 0) (hp 1),
      evalPoints_comp hb ℓ (hp 0), evalPoints_comp hb ℓ (hp 1), evalPoints_coordinatePoint hb, evalPoints_coordinatePoint hb] at h1
    exact h1
  have hexp : ∀ {n : ℕ} {u v : Pt k n d}, NoConst u → NoConst v →
      addOf (B.FK k) (comp1 e u) (comp1 e v) = comp1 e (u + v) := by
    intro n u v hu hv
    have h1 := hlog (nc_comp1 he hu) (nc_comp1 he hv)
    rw [germComp1_cancel_of_inverse he hle hu, germComp1_cancel_of_inverse he hle hv] at h1
    rw [← h1, germComp1_cancel_of_inverse hℓ hel (nc_addOf hF (nc_comp1 he hu) (nc_comp1 he hv))]
  have hact : ∀ (a : O) {n : ℕ} {u : Pt k n d}, NoConst u →
      comp1 ℓ (comp1 (B.actK k a) u) = lin (dLin (B.actK k a)) (comp1 ℓ u) := by
    intro a n u hu
    have h0 : comp1 ℓ (B.actK k a) = lin (dLin (B.actK k a)) ℓ :=
      funext (GlobalTheory.LogLinear.formalGroup_log_endomorphism_linear k d G ℓ (B.actK k a) hℓ hlin hadd (hα a) (A.hom a))
    rw [germComp1_germComp1_eq_substitute ℓ (hα a) hu, h0, evalPoints_linear (nc1 hu)]
    rfl
  obtain ⟨g₀, hg₀⟩ : ∃ g₀ : PS k 2 d, ∀ {n : ℕ} {u v : Pt k n d}, NoConst u → NoConst v →
      ev ![u, v] g₀ = ev ![comp1 e u, comp1 e v] g := by
    refine ⟨ev (n := 2) ![comp1 e (pt k d 0), comp1 e (pt k d 1)] g, ?_⟩
    intro n u v hu hv
    have hb := nc2 hu hv
    rw [germEv_germEv_two_points hb (nc_comp1 he (hp 0)) (nc_comp1 he (hp 1)), evalPoints_comp hb e (hp 0), evalPoints_comp hb e (hp 1),
      evalPoints_coordinatePoint hb, evalPoints_coordinatePoint hb]
    rfl
  have hb3 := nc3 (nc_comp1 he (hp (n := 3) 0)) (nc_comp1 he (hp (n := 3) 1)) (nc_comp1 he (hp (n := 3) 2))
  obtain ⟨β, hβ⟩ : ∃ β : Matrix (Fin d) (Fin d) k, JEq m g₀ (bilSer β (pt k (n := 2) d 0) (pt k d 1)) := by
    refine ⟨_, GlobalTheory.T.jetEq_bilinearSeries_of_biadditive k d m g₀ ?_ ?_⟩
    · have h1 := jEq_ev hb3 hg.add1
      rw [ev_add' hb3, germEv_germEv_two_points hb3 (nc_addOf hF (hp 0) (hp 1)) (hp 2), germEv_germEv_two_points hb3 (hp 0) (hp 2),
        germEv_germEv_two_points hb3 (hp 1) (hp 2), evalPoints_formalGroupAdd hb3 _ (hp 0) (hp 1), evalPoints_coordinatePoint hb3, evalPoints_coordinatePoint hb3, evalPoints_coordinatePoint hb3] at h1
      rw [hg₀ (nc_add (hp 0) (hp 1)) (hp 2), hg₀ (hp 0) (hp 2), hg₀ (hp 1) (hp 2), ← hexp (hp 0) (hp 1)]
      exact h1
    · have h1 := jEq_ev hb3 hg.add2
      rw [ev_add' hb3, germEv_germEv_two_points hb3 (hp 0) (nc_addOf hF (hp 1) (hp 2)), germEv_germEv_two_points hb3 (hp 0) (hp 1),
        germEv_germEv_two_points hb3 (hp 0) (hp 2), evalPoints_formalGroupAdd hb3 _ (hp 1) (hp 2), evalPoints_coordinatePoint hb3, evalPoints_coordinatePoint hb3, evalPoints_coordinatePoint hb3] at h1
      rw [hg₀ (hp 0) (nc_add (hp 1) (hp 2)), hg₀ (hp 0) (hp 1), hg₀ (hp 0) (hp 2), ← hexp (hp 1) (hp 2)]
      exact h1
  have hmain : ∀ {n : ℕ} {u v : Pt k n d}, NoConst u → NoConst v →
      JEq m (ev ![u, v] g) (bilSer β (comp1 ℓ u) (comp1 ℓ v)) := by
    intro n u v hu hv
    have hb := nc2 (nc_comp1 hℓ hu) (nc_comp1 hℓ hv)
    have h1 := jEq_ev hb hβ
    rw [hg₀ (nc_comp1 hℓ hu) (nc_comp1 hℓ hv), germComp1_cancel_of_inverse hℓ hel hu, germComp1_cancel_of_inverse hℓ hel hv,
      ev_bilSer hb, evalPoints_coordinatePoint hb, evalPoints_coordinatePoint hb] at h1
    exact h1
  have he0 := nc_comp1 he (hp (n := 2) 0)
  have he1 := nc_comp1 he (hp (n := 2) 1)
  have hb2 := nc2 he0 he1
  have hsym : β.transpose = β := by
    have h1 := jEq_ev hb2 hg.sym
    rw [germEv_germEv_two_points hb2 (hp 1) (hp 0), evalPoints_coordinatePoint hb2, evalPoints_coordinatePoint hb2] at h1
    have h2 := jEq_trans (jEq_symm (hmain he1 he0)) (jEq_trans h1 (hmain he0 he1))
    rw [germComp1_cancel_of_inverse he hle (hp 0), germComp1_cancel_of_inverse he hle (hp 1), bilSer_swap] at h2
    exact eq_of_jEq_bilSer hm h2
  have hbal : ∀ a : O, (dLin (B.actK k a)).transpose * β = β * dLin (B.actK k (star a)) := by
    intro a
    have h1 := jEq_ev hb2 (hg.bal a)
    rw [germEv_germEv_two_points hb2 (nc_comp1 (hα a) (hp 0)) (hp 1), germEv_germEv_two_points hb2 (hp 0) (nc_comp1 (hα _) (hp 1)),
      evalPoints_comp hb2 _ (hp 0), evalPoints_comp hb2 _ (hp 1), evalPoints_coordinatePoint hb2, evalPoints_coordinatePoint hb2] at h1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h1
    have h2 := jEq_trans (jEq_symm (hmain (nc_comp1 (hα a) he0) he1))
      (jEq_trans h1 (hmain he0 (nc_comp1 (hα (star a)) he1)))
    rw [hact a he0, hact _ he1, germComp1_cancel_of_inverse he hle (hp 0), germComp1_cancel_of_inverse he hle (hp 1), bilSer_lin_left,
      bilSer_lin_right] at h2
    exact eq_of_jEq_bilSer hm h2
  have hg' : ∀ {n : ℕ} {u v : Pt k n d}, NoConst u → NoConst v →
      ev ![u, v] (bilSer β (comp1 ℓ (pt k (n := 2) d 0)) (comp1 ℓ (pt k d 1))) = bilSer β (comp1 ℓ u) (comp1 ℓ v) := by
    intro n u v hu hv
    have hb := nc2 hu hv
    rw [ev_bilSer hb, evalPoints_comp hb ℓ (hp 0), evalPoints_comp hb ℓ (hp 1), evalPoints_coordinatePoint hb, evalPoints_coordinatePoint hb]
    rfl
  refine ⟨bilSer β (comp1 ℓ (pt k (n := 2) d 0)) (comp1 ℓ (pt k d 1)), fun m' => ⟨jEq_of_eq ?_, jEq_of_eq ?_,
    jEq_of_eq ?_, jEq_of_eq ?_, jEq_of_eq ?_, fun a => jEq_of_eq ?_⟩, ?_⟩
  · rw [hg' nc_zero (hp 0), germComp1_zero_of_noConstantCoeff hℓ, bilSer_zero_left]
  · rw [hg' (hp 0) nc_zero, germComp1_zero_of_noConstantCoeff hℓ, bilSer_zero_right]
  · rw [hg' (nc_addOf hF (hp 0) (hp 1)) (hp 2), hg' (hp 0) (hp 2), hg' (hp 1) (hp 2), hlog (hp 0) (hp 1),
      bilSer_add_left]
  · rw [hg' (hp 0) (nc_addOf hF (hp 1) (hp 2)), hg' (hp 0) (hp 1), hg' (hp 0) (hp 2), hlog (hp 1) (hp 2),
      bilSer_add_right]
  · rw [hg' (hp 1) (hp 0), bilSer_swap, hsym]
  · rw [hg' (nc_comp1 (hα a) (hp 0)) (hp 1), hg' (hp 0) (nc_comp1 (hα _) (hp 1)), hact a (hp 0), hact _ (hp 1),
      bilSer_lin_left, bilSer_lin_right, hbal]
  · have h1 := hmain (hp (n := 2) 0) (hp 1)
    rwa [ev_self2] at h1

end GlobalTheory.ChartBilin
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_biadditive_series_jetEq_of_biadditiveJet : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB R d O) (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (m : ℕ), 2 ≤ m → ∀ g : PS k 2 d, Biadd m B k g → ∃ g' : PS k 2 d, (∀ m', Biadd m' B k g') ∧ JEq m g g' := by
  atlas_forward_decl GlobalTheory.ChartBilin.exists_biadd_jEq
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp

namespace GlobalTheory.ChartCmp.Regauge
open ReciprocityTheory.ChartRestriction.G.TB.WickVanishing

theorem eq_of_forall_jeq {R σ : Type} [CommRing R] {f g : MvPowerSeries σ R} (h : ∀ m, JEq m f g) : f = g :=
  MvPowerSeries.ext fun e => h e.degree e le_rfl

theorem isCanonGauge_sub : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB R d O) (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (h g : PS k 2 d), B.IsCanonGauge k h → (∀ m, Biadd m B k g) → B.IsCanonGauge k (h - g) := by
  intro R _ d O _ _ B k _ _ _ h g hc hg
  have hF : ∀ i, MvPowerSeries.constantCoeff (B.FK k i) = 0 := fun i => by
    simp [FB.FK, FGLaw.mapF, B.G.const]
  have hA : ∀ a, GP (B.actK k a) := fun a i => by simp [FB.actK, B.A.const]
  have gA : ∀ {n : ℕ} (i j : Fin n), GP (addOf (B.FK k) (pt k d i) (pt k d j)) :=
    fun i j => gp_addOf _ hF _ _ (gp_pt i) (gp_pt j)
  have gC : ∀ {n : ℕ} (a : O) (i : Fin n), GP (comp1 (B.actK k a) (pt k d i)) :=
    fun a i => gp_comp1 _ _ (hA a) (gp_pt i)
  have a0 := eq_of_forall_jeq fun m => (hg m).ax0
  have a1 := eq_of_forall_jeq fun m => (hg m).ax1
  have d1 := eq_of_forall_jeq fun m => (hg m).add1
  have d2 := eq_of_forall_jeq fun m => (hg m).add2
  have sy := eq_of_forall_jeq fun m => (hg m).sym
  have bal := fun a => eq_of_forall_jeq fun m => (hg m).bal a
  refine ⟨?_, ?_, ?_, ?_, ?_, fun a => ?_⟩
  · rw [gt_ev_sub _ (pair_points_zero_constant gp_zero₂ (gp_pt _)), hc.ax0, a0, sub_zero]
  · rw [gt_ev_sub _ (pair_points_zero_constant (gp_pt _) gp_zero₂), hc.ax1, a1, sub_zero]
  · rw [hc.ph1, gt_ev_sub _ (pair_points_zero_constant (gp_pt _) (gp_pt _)), gt_ev_sub _ (pair_points_zero_constant (gp_pt _) (gp_pt _)),
      gt_ev_sub _ (pair_points_zero_constant (gA _ _) (gp_pt _)), d1]
    congr 1; ring
  · rw [hc.ph2, gt_ev_sub _ (pair_points_zero_constant (gp_pt _) (gp_pt _)), gt_ev_sub _ (pair_points_zero_constant (gp_pt _) (gp_pt _)),
      gt_ev_sub _ (pair_points_zero_constant (gp_pt _) (gA _ _)), d2]
    congr 1; ring
  · rw [hc.sy, gt_ev_sub _ (pair_points_zero_constant (gp_pt _) (gp_pt _)), sy]
    congr 1; ring
  · rw [hc.ad a, gt_ev_sub _ (pair_points_zero_constant (gC _ _) (gp_pt _)), gt_ev_sub _ (pair_points_zero_constant (gp_pt _) (gC _ _)), bal a]
    congr 1; ring

end GlobalTheory.ChartCmp.Regauge
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCanonicalGauge_sub_biadditive : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB R d O) (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (h g : PS k 2 d), B.IsCanonGauge k h → (∀ m, Biadd m B k g) → B.IsCanonGauge k (h - g) := by
  atlas_forward_decl GlobalTheory.ChartCmp.Regauge.isCanonGauge_sub
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harmonicValueCopies_gauge_independent : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] [Module.Free ℤ O] [Module.Finite ℤ O] [IsReduced O] (k : Type) [Field k] [Algebra ℚ k] [Algebra R k] (B : FB R d O) (h h' : PS k 2 d), B.IsCanonGauge k h → B.IsCanonGauge k h' → ∀ (T : Type) [Fintype T] (r : T → ℕ) (cc : T → T) (isX : T → Prop) (σ : T → O →+* k), (∀ τ, cc (cc τ) = τ) → (∀ τ, isX τ ∨ isX (cc τ)) → (∀ τ a, σ (cc τ) a = σ τ (star a)) → (∀ τ τ', τ ≠ τ' → ∃ a, IsUnit (σ τ a - σ τ' a)) → ∀ u : (Σ τ : T, Fin (r τ)) → Fin d → k, (∀ l a, (dAct k B a).mulVec (u l) = σ l.1 a • u l) → ∀ (n : ℕ) (P : MvPolynomial (Letter T r n) k), P ∈ harmK r n k cc isX (fun _ => 1) → ∀ (w0 : O) (q : ℕ) (f : PS k n d), nabValN B k h w0 q f (fun ℓ : Letter T r n => ℓ.2.2) (fun ℓ : Letter T r n => u ⟨ℓ.1, ℓ.2.1⟩) P = nabValN B k h' w0 q f (fun ℓ : Letter T r n => ℓ.2.2) (fun ℓ : Letter T r n => u ⟨ℓ.1, ℓ.2.1⟩) P := by
  first | exact @GlobalTheory.nabValN_harmonic_gauge_independent | exact GlobalTheory.nabValN_harmonic_gauge_independent | (intros; apply GlobalTheory.nabValN_harmonic_gauge_independent <;> assumption)
end

section
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp
open ReciprocityTheory.ChartRestriction.G.TB.WickVanishing

namespace GlobalTheory.ChartVal

section SlopeTestRemainingChoices
variable {k : Type} [CommRing k] {d : ℕ}

theorem jeq_sum {σ J : Type} {m : ℕ} (s : Finset J) {f g : J → MvPowerSeries σ k} (h : ∀ i, JEq m (f i) (g i)) :
    JEq m (∑ i ∈ s, f i) (∑ i ∈ s, g i) := by
  intro e he
  rw [map_sum, map_sum]
  exact Finset.sum_congr rfl fun i _ => h i e he

theorem jeq_smul {σ : Type} {m : ℕ} (c : k) {f g : MvPowerSeries σ k} (h : JEq m f g) : JEq m (c • f) (c • g) := by
  intro e he
  rw [MvPowerSeries.coeff_smul, MvPowerSeries.coeff_smul, h e he]

theorem expS_zero [Algebra ℚ k] {n : ℕ} : FB.expS k (0 : PS k n d) = 1 := by
  unfold FB.expS
  have hs : PowerSeries.HasSubst (0 : PS k n d) := PowerSeries.HasSubst.of_constantCoeff_zero (by simp)
  ext e
  rw [PowerSeries.coeff_subst hs, finsum_eq_single _ 0]
  · simp
  · intro j hj
    simp [hj]

theorem expS_sum [Algebra ℚ k] {n : ℕ} {J : Type} (s : Finset J) (f : J → PS k n d)
    (hf : ∀ i, MvPowerSeries.constantCoeff (f i) = 0) : FB.expS k (∑ i ∈ s, f i) = ∏ i ∈ s, FB.expS k (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [expS_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha, gt_expS_add _ _ (hf a) (by simp [map_sum, hf]), ih]

theorem expS_natSmul [Algebra ℚ k] {n : ℕ} (q : ℕ) (f : PS k n d)
    (hf : MvPowerSeries.constantCoeff f = 0) : FB.expS k ((q : k) • f) = FB.expS k f ^ q := by
  have h := expS_sum (Finset.range q) (fun _ => f) (fun _ => hf)
  rw [Finset.sum_const, Finset.prod_const, Finset.card_range] at h
  rw [← h, Nat.cast_smul_eq_nsmul]

theorem ev_sum {m n : ℕ} (a : Fin m → Pt k n d) (ha : ∀ j, GP (a j)) {J : Type} (s : Finset J) (f : J → PS k m d) :
    ev a (∑ i ∈ s, f i) = ∑ i ∈ s, ev a (f i) := by
  unfold ev
  rw [← MvPowerSeries.coe_substAlgHom (gt_hasSubst a ha), map_sum]

theorem ev_smul {m n : ℕ} (a : Fin m → Pt k n d) (ha : ∀ j, GP (a j)) (c : k) (f : PS k m d) :
    ev a (c • f) = c • ev a f := by
  unfold ev
  rw [← MvPowerSeries.coe_substAlgHom (gt_hasSubst a ha), map_smul]

theorem ev_pt_self {n : ℕ} (f : PS k n d) : ev (fun b => pt k (n := n) d b) f = f := by
  change MvPowerSeries.subst (MvPowerSeries.X) f = f
  rw [MvPowerSeries.subst_self]
  rfl

theorem ev_diag {n : ℕ} (a : Pt k 1 d) (x : Pt k n d) (ha : GP a) (hx : GP x) (g : PS k 2 d) :
    ev ![x] (ev (n := 1) ![pt k d 0, comp1 a (pt k d 0)] g) = ev ![x, comp1 a x] g := by
  rw [gt_ev_ev' _ _ (single_point_zero_constant hx) (pair_points_zero_constant (gp_pt 0) (gp_comp1 _ _ ha (gp_pt 0))), eval_pair_points,
    evP_comp1 _ (single_point_zero_constant hx) _ _ (gp_pt 0), evP_pt _ (single_point_zero_constant hx)]
  rfl

theorem ev_pair {n : ℕ} (φ : Pt k 1 d) (hφ : GP φ) (a b : Pt k n d) (ha : GP a) (hb : GP b) (h : PS k 2 d) :
    ev ![a, b] (ev ![comp1 φ (pt k (n := 2) d 0), comp1 φ (pt k (n := 2) d 1)] h) =
      ev ![comp1 φ a, comp1 φ b] h := by
  rw [gt_ev_ev' ![a, b] _ (pair_points_zero_constant ha hb)
      (pair_points_zero_constant (gp_comp1 _ _ hφ (gp_pt 0)) (gp_comp1 _ _ hφ (gp_pt 1))), eval_pair_points,
    evP_comp1 _ (pair_points_zero_constant ha hb) φ _ (gp_pt 0),
    evP_comp1 _ (pair_points_zero_constant ha hb) φ _ (gp_pt 1), evP_pt _ (pair_points_zero_constant ha hb), evP_pt _ (pair_points_zero_constant ha hb)]
  rfl

theorem jeq_main [Algebra ℚ k] {n : ℕ} (m q : ℕ) (φ φi a : Pt k 1 d) (hinv : IsInvPair φ φi) (ha : GP a)
    (h h' lam : PS k 2 d) (hh : MvPowerSeries.constantCoeff h = 0) (hh' : MvPowerSeries.constantCoeff h' = 0)
    (hl : MvPowerSeries.constantCoeff lam = 0)
    (hj : JEq m h' (ev ![comp1 φ (pt k (n := 2) d 0), comp1 φ (pt k (n := 2) d 1)] h + lam)) (f' : PS k n d) :
    JEq m (f' * FB.expS k ((q : k) • ∑ b : Fin n, ev (n := n) ![pt k d b]
        (ev (n := 1) ![pt k d 0, comp1 (comp1 φi (comp1 a φ)) (pt k d 0)] h')))
      (ev (n := n) (fun b => comp1 φ (pt k (n := n) d b))
        (ev (n := n) (fun b => comp1 φi (pt k (n := n) d b))
          (f' * ∏ b : Fin n, (ev ![pt k (n := n) d b, comp1 (comp1 φi (comp1 a φ)) (pt k (n := n) d b)]
            (FB.expS k lam)) ^ q) *
        FB.expS k ((q : k) • ∑ b : Fin n, ev (n := n) ![pt k d b]
          (ev (n := 1) ![pt k d 0, comp1 a (pt k d 0)] h)))) := by
  have hφ : GP φ := hinv.1
  have hφi : GP φi := hinv.2.1
  have ha' : GP (comp1 φi (comp1 a φ)) := gp_comp1 _ _ hφi (gp_comp1 _ _ ha hφ)
  have hp : ∀ b : Fin n, GP (pt k (n := n) d b) := fun b => gp_pt b
  have hΦ : ∀ b : Fin n, GP (comp1 φ (pt k (n := n) d b)) := fun b => gp_comp1 _ _ hφ (hp b)
  have hΦi : ∀ b : Fin n, GP (comp1 φi (pt k (n := n) d b)) := fun b => gp_comp1 _ _ hφi (hp b)
  set a' := comp1 φi (comp1 a φ) with ha'def
  have hL : ∀ b : Fin n, ∀ j, GP (![pt k (n := n) d b, comp1 a' (pt k (n := n) d b)] j) :=
    fun b => pair_points_zero_constant (hp b) (gp_comp1 _ _ ha' (hp b))
  have hLa : ∀ b : Fin n, ∀ j, GP (![pt k (n := n) d b, comp1 a (pt k (n := n) d b)] j) :=
    fun b => pair_points_zero_constant (hp b) (gp_comp1 _ _ ha (hp b))
  have hcomp : ∀ g : PS k n d, ev (n := n) (fun b => comp1 φ (pt k (n := n) d b))
      (ev (n := n) (fun b => comp1 φi (pt k (n := n) d b)) g) = g := by
    intro g
    rw [gt_ev_ev' _ _ hΦ hΦi]
    have : (fun j => evP (fun b => comp1 φ (pt k (n := n) d b)) (comp1 φi (pt k (n := n) d j))) =
        fun b => pt k (n := n) d b := by
      funext j
      rw [evP_comp1 _ hΦ _ _ (hp j), evP_pt _ hΦ, gt_comp_inv' hinv _ (hp j)]
    rw [this, ev_pt_self]
  have hφa : ∀ b : Fin n, comp1 φ (comp1 a' (pt k (n := n) d b)) = comp1 a (comp1 φ (pt k (n := n) d b)) := by
    intro b
    rw [ha'def, gt_comp1_comp1 φi _ (gp_comp1 _ φ ha hφ) _ (hp b), gt_comp1_comp1 a φ hφ _ (hp b),
      gt_comp_inv hinv _ (gp_comp1 _ _ ha (hΦ b))]
  have hterm : ∀ b : Fin n, ev (n := n) (fun b => comp1 φ (pt k (n := n) d b))
      (ev ![pt k (n := n) d b, comp1 a (pt k (n := n) d b)] h) =
      ev ![pt k (n := n) d b, comp1 a' (pt k (n := n) d b)]
        (ev ![comp1 φ (pt k (n := 2) d 0), comp1 φ (pt k (n := 2) d 1)] h) := by
    intro b
    rw [ev_pair φ hφ _ _ (hp b) (gp_comp1 _ _ ha' (hp b)), hφa, gt_ev_ev' _ _ hΦ (hLa b), eval_pair_points,
      evP_comp1 _ hΦ _ _ (hp b), evP_pt _ hΦ]
  set h0 := ev ![comp1 φ (pt k (n := 2) d 0), comp1 φ (pt k (n := 2) d 1)] h with h0def
  have hh0 : MvPowerSeries.constantCoeff h0 = 0 :=
    gt_const_ev _ (pair_points_zero_constant (gp_comp1 _ _ hφ (gp_pt 0)) (gp_comp1 _ _ hφ (gp_pt 1))) _ hh
  have cS : ∀ (V : Fin n → Fin 2 → Pt k n d), (∀ b j, GP (V b j)) → ∀ g : PS k 2 d,
      MvPowerSeries.constantCoeff g = 0 → MvPowerSeries.constantCoeff (∑ b, ev (V b) g) = 0 := by
    intro V hV g hg
    rw [map_sum]
    exact Finset.sum_eq_zero fun b _ => gt_const_ev _ (hV b) _ hg
  have cS' : ∀ (V : Fin n → Fin 2 → Pt k n d), (∀ b j, GP (V b j)) → ∀ g : PS k 2 d,
      MvPowerSeries.constantCoeff g = 0 → MvPowerSeries.constantCoeff ((q : k) • ∑ b, ev (V b) g) = 0 := by
    intro V hV g hg
    rw [MvPowerSeries.constantCoeff_smul, cS V hV g hg, smul_zero]
  simp only [ev_diag _ _ ha' (hp _), ev_diag _ _ ha (hp _)]
  rw [gt_ev_mul _ hΦ, hcomp, gt_ev_expS _ hΦ _ (cS' _ hLa h hh), ev_smul _ hΦ, ev_sum _ hΦ]
  simp only [hterm]
  have hE : ∏ b : Fin n, (ev ![pt k (n := n) d b, comp1 a' (pt k (n := n) d b)] (FB.expS k lam)) ^ q =
      FB.expS k ((q : k) • ∑ b : Fin n, ev ![pt k (n := n) d b, comp1 a' (pt k (n := n) d b)] lam) := by
    rw [expS_natSmul _ _ (cS _ hL lam hl), expS_sum _ _ (fun b => gt_const_ev _ (hL b) _ hl), Finset.prod_pow]
    congr 1
    exact Finset.prod_congr rfl fun b _ => gt_ev_expS _ (hL b) _ hl
  rw [hE, _root_.mul_assoc, ← gt_expS_add _ _ (cS' _ hL lam hl) (cS' _ hL h0 hh0), ← smul_add, ← Finset.sum_add_distrib]
  refine ((GlobalTheory.T.mvPowerSeriesJetEq_calculus k m).1 _ _ _ _ _ (JEq.refl m f') ?_).2.2
  have hsum : (∑ b : Fin n, (ev ![pt k (n := n) d b, comp1 a' (pt k (n := n) d b)] lam +
      ev ![pt k (n := n) d b, comp1 a' (pt k (n := n) d b)] h0)) =
      ∑ b : Fin n, ev ![pt k (n := n) d b, comp1 a' (pt k (n := n) d b)] (h0 + lam) :=
    Finset.sum_congr rfl fun b _ => by rw [gt_ev_add _ (hL b), add_comm]
  rw [hsum]
  refine ((GlobalTheory.T.jetEq_formalExp_iff_and_exists_log k n d m).1 _ _ (cS' _ hL h' hh') (cS' _ hL _ (by rw [map_add, hh0, hl, add_zero]))).1 ?_
  exact jeq_smul _ (jeq_sum _ fun b => (GlobalTheory.T.mvPowerSeriesJetEq_calculus k m).2.2.2.1 d 2 n _ _ _ _ (hL b) (hL b)
    (fun _ _ => JEq.refl _ _) hj)

end SlopeTestRemainingChoices

open GlobalTheory.FBMap in

theorem exists_nabValN_eq : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] [Module.Free ℤ O] [Module.Finite ℤ O] [IsReduced O] (k : Type) [Field k] [Algebra ℚ k] [Algebra R k] (B B' : FB R d O) (φ φi : Pt R 1 d), (∀ m, ∃ ε : PS R 2 d, JRel m B B' φ φi ε) → ∀ h h' : PS k 2 d, B.IsCanonGauge k h → B'.IsCanonGauge k h' → ∀ (T : Type) [Fintype T] (r : T → ℕ) (cc : T → T) (isX : T → Prop) (σ : T → O →+* k), (∀ τ, cc (cc τ) = τ) → (∀ τ, isX τ ∨ isX (cc τ)) → (∀ τ a, σ (cc τ) a = σ τ (star a)) → (∀ τ τ', τ ≠ τ' → ∃ a, IsUnit (σ τ a - σ τ' a)) → ∀ u u' : (Σ τ : T, Fin (r τ)) → Fin d → k, (∀ l a, (dAct k B' a).mulVec (u' l) = σ l.1 a • u' l) → (∀ l, u l = ((dLin φ).map (algebraMap R k)).mulVec (u' l)) → ∀ (n : ℕ) (P : MvPolynomial (Letter T r n) k), P ∈ harmK r n k cc isX (fun _ => 1) → ∀ (w0 : O) (q : ℕ) (f' : PS R n d), ∃ f : PS R n d, nabValN B k h w0 q (MvPowerSeries.map (algebraMap R k) f) (fun ℓ : Letter T r n => ℓ.2.2) (fun ℓ : Letter T r n => u ⟨ℓ.1, ℓ.2.1⟩) P = nabValN B' k h' w0 q (MvPowerSeries.map (algebraMap R k) f') (fun ℓ : Letter T r n => ℓ.2.2) (fun ℓ : Letter T r n => u' ⟨ℓ.1, ℓ.2.1⟩) P := by
  intro R _ d O _ _ _ _ _ k _ _ _ B B' φ φi hrel h h' hh hh' T _ r cc isX σ h1 h2 h3 h4 u u' hu' hu n P hP w0 q f'
  obtain ⟨ε, hε⟩ := hrel (P.totalDegree + 2)
  set m := P.totalDegree + 2 with hm
  have hε1 := (GlobalTheory.T.formalChartJetRel_unit_one_on_axes R d O m B B' φ φi ε hε).1
  obtain ⟨lam, hl0, hle⟩ := (GlobalTheory.T.jetEq_formalExp_iff_and_exists_log k 2 d m).2 (FB.toK k ε) (by simp [FB.toK, hε1])
  have hbi := GlobalTheory.T.canonicalGauge_difference_biadditive_jet R d O m B B' φ φi ε hε k h h' lam hh hh' hl0 hle
  obtain ⟨g', hg', hgg⟩ := GlobalTheory.T.exists_biadditive_series_jetEq_of_biadditiveJet R d O B' k m (by omega) _ hbi
  have hcan := GlobalTheory.T.isCanonicalGauge_sub_biadditive R d O B' k h' g' hh' hg'
  have c0 : ∀ {C : FB R d O} {g : PS k 2 d}, C.IsCanonGauge k g → MvPowerSeries.constantCoeff g = 0 := by
    intro C g hg
    have := congrArg MvPowerSeries.constantCoeff hg.ax0
    rwa [gt_const_ev_eq _ (pair_points_zero_constant gp_zero₂ (gp_pt 0)), map_zero] at this
  have hφ : NoConst φ := hε.inv.1
  have hφi : NoConst φi := hε.inv.2.1
  have hinv : IsInvPair (mapPt (algebraMap R k) φ) (mapPt (algebraMap R k) φi) := by
    refine ⟨fun i => by simp [mapPt, hφ i], fun i => by simp [mapPt, hφi i], ?_, ?_⟩
    · rw [← mapPt_comp1 _ _ hφi, hε.inv.2.2.1, mapPt_pt]
    · rw [← mapPt_comp1 _ _ hφ, hε.inv.2.2.2, mapPt_pt]
  have hact : B'.actK k w0 = comp1 (mapPt (algebraMap R k) φi) (comp1 (B.actK k w0) (mapPt (algebraMap R k) φ)) := by
    change mapPt (algebraMap R k) (B'.A.act w0) = comp1 _ (comp1 (mapPt (algebraMap R k) (B.A.act w0)) _)
    rw [hε.act w0, mapPt_comp1 _ _ (nc_comp1 (nc_act _ _) hφ), mapPt_comp1 _ _ hφ]
  have hF : B'.FK k = transF (mapLaw (algebraMap R k) B.G).F (mapPt (algebraMap R k) φ) (mapPt (algebraMap R k) φi) := by
    funext i
    change MvPowerSeries.map (algebraMap R k) (B'.G.F i) = _
    rw [hε.law i]
    unfold transF
    rw [map_ev1 _ (nc_addOf (nc_law _) (nc_comp1 hφ (nc_pt _)) (nc_comp1 hφ (nc_pt _))),
      mapPt_addOf _ _ (nc_comp1 hφ (nc_pt _)) (nc_comp1 hφ (nc_pt _)), mapPt_comp1 _ _ (nc_pt _),
      mapPt_comp1 _ _ (nc_pt _), mapPt_pt, mapPt_pt]
    rfl
  have hd : dLin (mapPt (algebraMap R k) φ) = (dLin φ).map (algebraMap R k) := by
    ext i j
    simp [dLin, mapPt]
  have hj : JEq m (h' - g') (ev ![comp1 (mapPt (algebraMap R k) φ) (pt k (n := 2) d 0),
      comp1 (mapPt (algebraMap R k) φ) (pt k (n := 2) d 1)] h + lam) := by
    intro e he
    have := hgg e he
    rw [map_sub, map_sub] at this
    rw [map_sub, map_add, ← this]
    change _ - (_ - MvPowerSeries.coeff e (ev ![comp1 (mapPt (algebraMap R k) φ) (pt k (n := 2) d 0),
      comp1 (mapPt (algebraMap R k) φ) (pt k (n := 2) d 1)] h) - _) = _
    ring
  have haK : GP (B.actK k w0) := fun i => by simp [FB.actK, B.A.const w0 i]
  have key := jeq_main (n := n) m q _ _ (B.actK k w0) hinv haK h (h' - g') lam (c0 hh) (c0 hcan) hl0 hj
    (MvPowerSeries.map (algebraMap R k) f')
  refine ⟨ev (n := n) (fun b => comp1 φi (pt R (n := n) d b))
    (f' * ∏ b : Fin n, (ev ![pt R (n := n) d b, comp1 (B'.A.act w0) (pt R (n := n) d b)] ε) ^ q), ?_⟩
  rw [GlobalTheory.T.harmonicValueCopies_gauge_independent R d O k B' h' (h' - g') hh' hcan T r cc isX σ h1 h2 h3 h4 u' hu' n P hP w0 q]
  have hmap : MvPowerSeries.map (algebraMap R k) (ev (n := n) (fun b => comp1 φi (pt R (n := n) d b))
      (f' * ∏ b : Fin n, (ev ![pt R (n := n) d b, comp1 (B'.A.act w0) (pt R (n := n) d b)] ε) ^ q)) =
      ev (n := n) (fun b => comp1 (mapPt (algebraMap R k) φi) (pt k (n := n) d b))
        (MvPowerSeries.map (algebraMap R k) f' * ∏ b : Fin n, (ev ![pt k (n := n) d b,
          comp1 (B'.actK k w0) (pt k (n := n) d b)] (FB.expS k lam)) ^ q) := by
    rw [map_ev _ (fun b => nc_comp1 hφi (nc_pt b)), map_mul, map_prod]
    congr 1
    · funext b
      rw [mapPt_comp1 _ _ (nc_pt _), mapPt_pt]
    · congr 1
      refine Finset.prod_congr rfl fun b _ => ?_
      rw [map_pow, map_ev2 _ (nc_pt _) (nc_comp1 (nc_act _ _) (nc_pt _)), mapPt_comp1 _ _ (nc_pt _), mapPt_pt, hle]
      rfl
  unfold nabValN FB.hL
  rw [hmap, hF, hact, GlobalTheory.T.constantCoeff_invariantPolyOperator_jetEq k d n _ _ _ _ P m _ _ (by omega) key,
    GlobalTheory.T.invariantPolyOperatorCopies_transportedLaw k d n (mapLaw (algebraMap R k) B.G) _ _ hinv,
    gt_const_ev_eq _ (fun b => gp_comp1 _ _ hinv.1 (gp_pt b)), hd]
  simp only [hu]
  rfl

end GlobalTheory.ChartVal
end
end
