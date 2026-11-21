import Mathlib
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.LogChain
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.CoeffEqZeroOfMemSpanPow
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsPowSpanXLeSpanFormalModuleMatrix
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsFiniteBasisPowerSeriesSubstFiniteColength
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.InvariantsAndTraceFiniteFreeDomainEndomorphisms
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.JacobianSmulKaehlerEqZero
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.MapMaximalIdealEqKerMapResidue
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.MvPowerSeriesExistsPolynomialTotalDegreeLeSubMemStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CardAlgHomReducedTraceSum
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.MvPowerSeriesSubstConstTermsLocalAlgHomSpec
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.FormalGroupLawCompMulNZero
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.GermPointsNoConstantTermFirstZero
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.FormalGroupTranslateAutomorphismAndMatrixKernel
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsUnitDetOfProductMapNeZero

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_basis_powerSeries_subst_finite_colength : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [CharZero V] (σ : Type) [Fintype σ] (φ : σ → MvPowerSeries σ V), (∀ j, MvPowerSeries.constantCoeff (φ j) = 0) → (∃ M : ℕ, Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ (ResidueField V))) ^ M ≤ Ideal.span (Set.range fun j => MvPowerSeries.map (residue V) (φ j))) → ∃ (r : ℕ) (b : Fin r → MvPowerSeries σ V), Module.finrank V (MvPowerSeries σ V ⧸ Ideal.span (Set.range φ)) = r ∧ ∀ f, ∃! cf : Fin r → MvPowerSeries σ V, f = ∑ i, MvPowerSeries.subst φ (cf i) * b i := by
  first | exact @GlobalTheory.FiniteColength.exists_basis_subst_finrank_quotient | exact GlobalTheory.FiniteColength.exists_basis_subst_finrank_quotient | (intros; apply GlobalTheory.FiniteColength.exists_basis_subst_finrank_quotient <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.invariants_and_trace_finite_free_domain_endomorphisms : ∀ (A R : Type) [CommRing A] [IsDomain A] [CommRing R] [IsDomain R] [Algebra A R] [Module.Free A R] [Module.Finite A R] (G : Finset (R →ₐ[A] R)), G.card = Module.finrank A R → (∀ x : R, (∀ g ∈ G, g x = x) → x ∈ (algebraMap A R).range) ∧ ∀ x : R, algebraMap A R (Algebra.trace A R x) = ∑ g ∈ G, g x := by
  first | exact @GlobalTheory.PlaceInt.invariants_and_trace_of_card_eq_finrank | exact GlobalTheory.PlaceInt.invariants_and_trace_of_card_eq_finrank | (intros; apply GlobalTheory.PlaceInt.invariants_and_trace_of_card_eq_finrank <;> assumption)
end

section
section
set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB IsLocalRing

namespace GlobalTheory.PlaceInt.MatJac

open GlobalTheory.GaugeAdjoint

section General

variable {R : Type} [CommRing R] {d n : ℕ} (G : FGLaw R d)

def invJ (z : Pt R n d) (a l : Fin d) : PS R n d := ev ![z, 0] (pderiv R ((1 : Fin 2), l) (G.F a))

def invD (q : Fin n × Fin d) (f : PS R n d) : PS R n d :=
  ∑ c, pderiv R (q.1, c) f * invJ G (pt R d q.1) c q.2

theorem const_invJ {z : Pt R n d} (hz : ∀ i, constantCoeff (z i) = 0) (a l : Fin d) :
    constantCoeff (invJ G z a l) = if a = l then 1 else 0 := by
  have hz0 : ∀ i, constantCoeff ((0 : Pt R n d) i) = 0 := fun i => by simp
  unfold invJ
  rw [GlobalTheory.DerivEndo.cc_ev (GlobalTheory.DerivEndo.noConst_two hz hz0), ← GlobalTheory.FormalMulN.coeff_single_one]
  exact GlobalTheory.FormalMulN.lin_F_right G a l

theorem invD_ev {m : ℕ} {a : Fin m → Pt R n d} (ha : ∀ j i, constantCoeff (a j i) = 0)
    (f : PS R m d) (q : Fin n × Fin d) :
    invD G q (ev a f) = ∑ j, ∑ l, ev a (pderiv R (j, l) f) * invD G q (a j l) := by
  unfold invD
  calc _ = ∑ c, ∑ j, ∑ l, ev a (pderiv R (j, l) f) * pderiv R (q.1, c) (a j l) *
        invJ G (pt R d q.1) c q.2 := by
        simp_rw [GlobalTheory.DerivEndo.pderiv_ev ha, Finset.sum_mul]
    _ = _ := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      ring

private theorem pderiv_pt_eq_ite {k : ℕ} (j j' : Fin k) (l c : Fin d) :
    pderiv R (j', c) (pt R d j l) = if (j, l) = (j', c) then 1 else 0 := by
  show pderiv R (j', c) (X (j, l)) = _
  split_ifs with h
  · rw [h, pderiv_X_self]
  · exact pderiv_X_of_ne h

private theorem formalGroup_add_apply_eq_ev {k : ℕ} (x y : Pt R k d) (a : Fin d) :
    G.add x y a = ev ![x, y] (G.F a) := rfl

private theorem ev_ev_pair_eq_ev_pair_ev {k m : ℕ} (b : Fin m → Pt R k d) (hb : ∀ j i, constantCoeff (b j i) = 0)
    (x y : Pt R m d) (hx : ∀ i, constantCoeff (x i) = 0) (hy : ∀ i, constantCoeff (y i) = 0)
    (g : PS R 2 d) :
    ev b (ev ![x, y] g) = ev ![fun i => ev b (x i), fun i => ev b (y i)] g := by
  rw [GlobalTheory.DerivEndo.ev_ev hb (GlobalTheory.DerivEndo.noConst_two hx hy)]
  congr 1
  funext j i
  fin_cases j <;> rfl

theorem right_invJ {z w : Pt R n d} (hz : ∀ i, constantCoeff (z i) = 0)
    (hw : ∀ i, constantCoeff (w i) = 0) (a i : Fin d) :
    ∑ c, ev ![z, w] (pderiv R ((1 : Fin 2), c) (G.F a)) * invJ G w c i = invJ G (G.add z w) a i := by
  have hz0 : ∀ i, constantCoeff ((0 : Pt R n d) i) = 0 := fun i => by simp
  have c0 := GlobalTheory.DerivEndo.cc_pt (R := R) (n := 3) (d := d) 0
  have c1 := GlobalTheory.DerivEndo.cc_pt (R := R) (n := 3) (d := d) 1
  have c2 := GlobalTheory.DerivEndo.cc_pt (R := R) (n := 3) (d := d) 2
  have c01 := GlobalTheory.FormalMulN.const_add G c0 c1
  have c12 := GlobalTheory.FormalMulN.const_add G c1 c2
  have e3 : ∀ j i, constantCoeff ((![z, w, 0] : Fin 3 → Pt R n d) j i) = 0 :=
    GlobalTheory.FormalMulN.const_three hz hw hz0
  have hL0 : ∀ l, pderiv R ((2 : Fin 3), i) (G.add (pt R d 0) (pt R d 1) l) = 0 := by
    intro l
    rw [formalGroup_add_apply_eq_ev, GlobalTheory.DerivEndo.pderiv_ev (GlobalTheory.DerivEndo.noConst_two c0 c1)]
    simp [pderiv_pt_eq_ite, Fin.sum_univ_two]
  have hR : ∀ l, pderiv R ((2 : Fin 3), i) (G.add (pt R d 1) (pt R d 2) l) =
      ev ![pt R (n := 3) d 1, pt R d 2] (pderiv R ((1 : Fin 2), i) (G.F l)) := by
    intro l
    rw [formalGroup_add_apply_eq_ev, GlobalTheory.DerivEndo.pderiv_ev (GlobalTheory.DerivEndo.noConst_two c1 c2)]
    simp [pderiv_pt_eq_ite, Fin.sum_univ_two]
  have hA := congrArg (fun P : Pt R 3 d => pderiv R ((2 : Fin 3), i) (P a))
    (GlobalTheory.FormalMulN.add_assoc_pt G c0 c1 c2)
  rw [formalGroup_add_apply_eq_ev G (G.add _ _) _ a, formalGroup_add_apply_eq_ev G (pt R d 0) _ a,
    GlobalTheory.DerivEndo.pderiv_ev (GlobalTheory.DerivEndo.noConst_two c01 c2),
    GlobalTheory.DerivEndo.pderiv_ev (GlobalTheory.DerivEndo.noConst_two c0 c12)] at hA
  simp [Fin.sum_univ_two, hL0, hR, pderiv_pt_eq_ite] at hA
  have f0 : (fun i => ev ![z, w, 0] (pt R (n := 3) d 0 i)) = z := GlobalTheory.FormalMulN.ev_pt_fun e3 0
  have f1 : (fun i => ev ![z, w, 0] (pt R (n := 3) d 1 i)) = w := GlobalTheory.FormalMulN.ev_pt_fun e3 1
  have f2 : (fun i => ev ![z, w, 0] (pt R (n := 3) d 2 i)) = 0 := GlobalTheory.FormalMulN.ev_pt_fun e3 2
  have fa0 : (fun i => ev ![z, w, 0] (G.add (pt R (n := 3) d 0) (pt R d 1) i)) = G.add z w := by
    rw [GlobalTheory.FormalMulN.ev_add_pts G c0 c1 e3, f0, f1]
  have fa1 : (fun i => ev ![z, w, 0] (G.add (pt R (n := 3) d 1) (pt R d 2) i)) = w := by
    rw [GlobalTheory.FormalMulN.ev_add_pts G c1 c2 e3, f1, f2, GlobalTheory.FormalMulN.add_zero_pt G hw]
  have hB := congrArg (ev ![z, w, 0]) hA
  rw [ev_ev_pair_eq_ev_pair_ev _ e3 _ _ c01 c2, fa0, f2, GlobalTheory.DerivEndo.ev_sum e3] at hB
  simp only [GlobalTheory.DerivEndo.ev_mul e3, ev_ev_pair_eq_ev_pair_ev _ e3 _ _ c0 c12, ev_ev_pair_eq_ev_pair_ev _ e3 _ _ c1 c2,
    f0, f1, f2, fa1] at hB
  exact hB.symm

theorem ev_left_eq {z w : Pt R n d} (hz : ∀ i, constantCoeff (z i) = 0)
    (hw : ∀ i, constantCoeff (w i) = 0) (a c : Fin d) :
    ev ![z, w] (pderiv R ((0 : Fin 2), c) (G.F a)) = ev ![w, z] (pderiv R ((1 : Fin 2), c) (G.F a)) := by
  have h2 : ∀ j i, constantCoeff ((![pt R (n := 2) d 1, pt R (n := 2) d 0] : Fin 2 → Pt R 2 d) j i) = 0 :=
    GlobalTheory.DerivEndo.noConst_two (GlobalTheory.DerivEndo.cc_pt 1) (GlobalTheory.DerivEndo.cc_pt 0)
  have hzw := GlobalTheory.DerivEndo.noConst_two hz hw
  have hc : G.F a = ev ![pt R (n := 2) d 1, pt R (n := 2) d 0] (G.F a) := by
    have h := GlobalTheory.FormalMulN.add_comm_pt G (GlobalTheory.DerivEndo.cc_pt (R := R) (n := 2) (d := d) 0)
      (GlobalTheory.DerivEndo.cc_pt 1)
    rw [GlobalTheory.DerivEndo.add_pt] at h
    exact congrFun h a
  have hd : pderiv R ((0 : Fin 2), c) (G.F a) =
      ev ![pt R (n := 2) d 1, pt R (n := 2) d 0] (pderiv R ((1 : Fin 2), c) (G.F a)) := by
    conv_lhs => rw [hc]
    rw [GlobalTheory.DerivEndo.pderiv_ev h2]
    simp [Fin.sum_univ_two, pderiv_pt_eq_ite]
  rw [hd, ev_ev_pair_eq_ev_pair_ev _ hzw _ _ (GlobalTheory.DerivEndo.cc_pt 1) (GlobalTheory.DerivEndo.cc_pt 0),
    GlobalTheory.FormalMulN.ev_pt_fun hzw 0, GlobalTheory.FormalMulN.ev_pt_fun hzw 1]
  rfl

def Inv (z : Pt R n d) : Prop :=
  (∀ i, constantCoeff (z i) = 0) ∧
    ∀ q : Fin n × Fin d, ∃ u : Fin d → R, ∀ a, invD G q (z a) = ∑ l, invJ G z a l * C (u l)

theorem inv_zero : Inv G (0 : Pt R n d) := by
  refine ⟨fun i => by simp, fun q => ⟨0, fun a => ?_⟩⟩
  simp [invD]

theorem inv_pt (j : Fin n) : Inv G (pt R d j) := by
  refine ⟨GlobalTheory.DerivEndo.cc_pt j, fun q => ⟨fun l => if j = q.1 ∧ l = q.2 then 1 else 0, fun a => ?_⟩⟩
  unfold invD
  simp only [pderiv_pt_eq_ite]
  by_cases h : j = q.1
  · subst h
    simp [Prod.mk.injEq, apply_ite (C (σ := Fin n × Fin d) (R := R)), mul_ite, ite_mul]
  · simp [h]

theorem inv_add {z w : Pt R n d} (hz : Inv G z) (hw : Inv G w) : Inv G (G.add z w) := by
  obtain ⟨hz0, hzu⟩ := hz
  obtain ⟨hw0, hwu⟩ := hw
  refine ⟨GlobalTheory.FormalMulN.const_add G hz0 hw0, fun q => ?_⟩
  obtain ⟨u, hu⟩ := hzu q
  obtain ⟨v, hv⟩ := hwu q
  refine ⟨u + v, fun a => ?_⟩
  have hZ : ∀ m, ∑ l, ev ![z, w] (pderiv R ((0 : Fin 2), l) (G.F a)) * invJ G z l m =
      invJ G (G.add z w) a m := by
    intro m
    simp_rw [ev_left_eq G hz0 hw0]
    rw [right_invJ G hw0 hz0, GlobalTheory.FormalMulN.add_comm_pt G hw0 hz0]
  have hW : ∀ m, ∑ l, ev ![z, w] (pderiv R ((1 : Fin 2), l) (G.F a)) * invJ G w l m =
      invJ G (G.add z w) a m := fun m => right_invJ G hz0 hw0 a m
  rw [formalGroup_add_apply_eq_ev, invD_ev G (GlobalTheory.DerivEndo.noConst_two hz0 hw0), Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, hu, hv]
  simp only [Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]
  congr 1
  · simp_rw [← hZ, Finset.sum_mul, Finset.mul_sum, mul_assoc]
    exact Finset.sum_comm
  · simp_rw [← hW, Finset.sum_mul, Finset.mul_sum, mul_assoc]
    exact Finset.sum_comm

private theorem comp1_apply_eq_ev_single {k : ℕ} (φ : Pt R 1 d) (z : Pt R k d) (a : Fin d) :
    comp1 φ z a = ev ![z] (φ a) := rfl

private theorem ev_single_ev_restrict_first_axis {k : ℕ} (z : Pt R k d) (hz : ∀ i, constantCoeff (z i) = 0) (g : PS R 2 d) :
    ev ![z] (ev (n := 1) ![pt R d 0, 0] g) = ev ![z, 0] g := by
  have h1 := GlobalTheory.DerivEndo.noConst_one hz
  rw [ev_ev_pair_eq_ev_pair_ev ![z] h1 (pt R d 0) 0 (GlobalTheory.DerivEndo.cc_pt 0) (fun i => by simp),
    GlobalTheory.FormalMulN.ev_pt_fun h1 0, GlobalTheory.FormalMulN.ev_zero_fun h1]
  rfl

theorem inv_comp (φ : Pt R 1 d) (hφ : ∀ i, constantCoeff (φ i) = 0)
    (hom : comp1 φ (G.add (pt R (n := 2) d 0) (pt R (n := 2) d 1)) =
      G.add (comp1 φ (pt R (n := 2) d 0)) (comp1 φ (pt R (n := 2) d 1)))
    {z : Pt R n d} (hz : Inv G z) : Inv G (comp1 φ z) := by
  obtain ⟨hz0, hzu⟩ := hz
  have h1 := GlobalTheory.DerivEndo.noConst_one hz0
  have hc : ∀ i, constantCoeff (comp1 φ z i) = 0 := fun i => by
    rw [comp1_apply_eq_ev_single, GlobalTheory.DerivEndo.cc_ev h1]
    exact hφ i
  refine ⟨hc, fun q => ?_⟩
  obtain ⟨u, hu⟩ := hzu q
  refine ⟨(dLin φ).mulVec u, fun a => ?_⟩
  have hB : ∀ g : PS R 2 d, ev ![z] (ev (n := 1) ![φ] (ev (n := 1) ![pt R d 0, 0] g)) =
      ev ![comp1 φ z, 0] g := by
    intro g
    rw [GlobalTheory.DerivEndo.ev_ev h1 (GlobalTheory.DerivEndo.noConst_one hφ)]
    have e : (fun j i => ev ![z] ((![φ] : Fin 1 → Pt R 1 d) j i)) = ![comp1 φ z] := by
      funext j i
      fin_cases j
      rfl
    rw [e, ev_single_ev_restrict_first_axis (comp1 φ z) hc]
  have K : ∀ m, ∑ l, ev ![z] (pderiv R ((0 : Fin 1), l) (φ a)) * invJ G z l m =
      ∑ b, invJ G (comp1 φ z) a b * C (dLin φ b m) := by
    intro m
    have hj := congrArg (ev ![z]) (GlobalTheory.DerivEndo.jac_endo G φ hφ hom a m)
    simp only [GlobalTheory.DerivEndo.ev_sum h1, GlobalTheory.DerivEndo.ev_mul h1, GlobalTheory.DerivEndo.ev_C, hB,
      ev_single_ev_restrict_first_axis z hz0] at hj
    exact hj
  rw [comp1_apply_eq_ev_single, invD_ev G h1]
  simp only [Fin.sum_univ_one, Matrix.cons_val_zero, hu]
  simp only [Finset.mul_sum, ← mul_assoc]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_mul, K]
  simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

theorem isUnit_det_of_const {σ ι : Type} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι (MvPowerSeries σ R))
    (h : (constantCoeff (σ := σ) (R := R)).mapMatrix M = 1) : IsUnit M.det := by
  rw [MvPowerSeries.isUnit_iff_constantCoeff, RingHom.map_det, h, Matrix.det_one]
  exact isUnit_one

def blockJ (z : Fin n → Pt R n d) : Matrix (Fin n × Fin d) (Fin n × Fin d) (PS R n d) :=
  Matrix.of fun p q => if p.1 = q.1 then invJ G (z p.1) p.2 q.2 else 0

theorem const_blockJ {z : Fin n → Pt R n d} (hz : ∀ b i, constantCoeff (z b i) = 0) :
    (constantCoeff (σ := Fin n × Fin d) (R := R)).mapMatrix (blockJ G z) = 1 := by
  ext p q
  rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.one_apply]
  unfold blockJ
  rw [Matrix.of_apply]
  by_cases h : p.1 = q.1
  · rw [if_pos h, const_invJ G (hz p.1)]
    simp [Prod.ext_iff, h]
  · rw [if_neg h, map_zero, if_neg (fun e => h (congrArg Prod.fst e))]

theorem det_jac_of_inv (ψ : Fin n → Pt R n d) (hψ : ∀ b, Inv G (ψ b)) :
    ∃ U : (PS R n d)ˣ, Matrix.det (Matrix.of fun i j : Fin n × Fin d => pderiv R j (ψ i.1 i.2)) =
      C (Matrix.det (Matrix.of fun p q : Fin n × Fin d =>
        coeff (Finsupp.single q 1) (ψ p.1 p.2))) * (U : PS R n d) := by
  have hψ' : ∀ b, (∀ i, constantCoeff (ψ b i) = 0) ∧ ∀ q : Fin n × Fin d, ∃ u : Fin d → R,
      ∀ a, invD G q (ψ b a) = ∑ l, invJ G (ψ b) a l * C (u l) := hψ
  choose hψ0 u hu using hψ'
  set Jac := Matrix.of fun i j : Fin n × Fin d => pderiv R j (ψ i.1 i.2) with hJac
  set Lm := Matrix.of fun p q : Fin n × Fin d => coeff (Finsupp.single q 1) (ψ p.1 p.2) with hLm
  set Um : Matrix (Fin n × Fin d) (Fin n × Fin d) R := Matrix.of fun p q => u p.1 q p.2 with hUm
  have hpt0 : ∀ b i, constantCoeff ((fun b => pt R d b : Fin n → Pt R n d) b i) = 0 :=
    fun b i => GlobalTheory.DerivEndo.cc_pt b i
  have key : Jac * blockJ G (fun b => pt R d b) =
      blockJ G ψ * (C (σ := Fin n × Fin d) (R := R)).mapMatrix Um := by
    ext i q
    rw [Matrix.mul_apply, Matrix.mul_apply, Fintype.sum_prod_type, Fintype.sum_prod_type]
    have e1 : ∀ j1 : Fin n, ∑ j2, Jac i (j1, j2) * blockJ G (fun b => pt R d b) (j1, j2) q =
        if j1 = q.1 then ∑ c, pderiv R (j1, c) (ψ i.1 i.2) * invJ G (pt R d j1) c q.2 else 0 := by
      intro j1
      unfold blockJ
      split_ifs with h <;> simp [hJac, h]
    have e2 : ∀ p1 : Fin n, ∑ p2, blockJ G ψ i (p1, p2) *
        (C (σ := Fin n × Fin d) (R := R)).mapMatrix Um (p1, p2) q =
        if i.1 = p1 then ∑ l, invJ G (ψ i.1) i.2 l * C (u i.1 q l) else 0 := by
      intro p1
      unfold blockJ
      split_ifs with h
      · subst h
        simp [hUm]
      · simp [h]
    simp only [e1, e2, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [← hu]
    rfl
  have hUpt : IsUnit (blockJ G (fun b => pt R d b)).det :=
    isUnit_det_of_const _ (const_blockJ G hpt0)
  have hUψ : IsUnit (blockJ G ψ).det := isUnit_det_of_const _ (const_blockJ G hψ0)
  have hL : (constantCoeff (σ := Fin n × Fin d) (R := R)).mapMatrix Jac = Lm := by
    ext p q
    simp [hJac, hLm, GlobalTheory.FormalMulN.coeff_single_one]
  have hCU : (constantCoeff (σ := Fin n × Fin d) (R := R)).mapMatrix
      ((C (σ := Fin n × Fin d) (R := R)).mapMatrix Um) = Um := by
    ext p q
    simp
  have hUL : Lm = Um := by
    have := congrArg (constantCoeff (σ := Fin n × Fin d) (R := R)).mapMatrix key
    rw [map_mul, map_mul, const_blockJ G hpt0, const_blockJ G hψ0, hL, hCU, mul_one, one_mul] at this
    exact this
  have hdet := congrArg Matrix.det key
  rw [Matrix.det_mul, Matrix.det_mul, ← RingHom.map_det] at hdet
  refine ⟨hUψ.unit * hUpt.unit⁻¹, ?_⟩
  have e : Jac.det = Jac.det * (blockJ G (fun b => pt R d b)).det *
      ((hUpt.unit⁻¹ : (PS R n d)ˣ) : PS R n d) := by
    rw [mul_assoc, IsUnit.mul_val_inv, mul_one]
  rw [e, hdet, hUL, Units.val_mul, IsUnit.unit_spec]
  ring

end General

section Local

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  [IsAdicComplete (maximalIdeal V) V] [CharZero V] {d : ℕ}

theorem evV_eq_ev {m n : ℕ} {a : Fin m → Pt V n d} (ha : ∀ j i, constantCoeff (a j i) = 0)
    (f : PS V m d) : evV a f = ev a f := by
  obtain ⟨-, -, h3, -⟩ := GlobalTheory.PlaceInt.evC_spec V (Fin m × Fin d) (Fin n × Fin d) (Fin n × Fin d)
    (fun p => a p.1 p.2) (fun p => by rw [ha p.1 p.2]; exact Submodule.zero_mem _)
  exact h3 (fun p => ha p.1 p.2) f

theorem inv_foldr {n : ℕ} (G : FGLaw V d) (L : List (Pt V n d)) (hL : ∀ z ∈ L, Inv G z) :
    Inv G (L.foldr (addV G.F) 0) := by
  induction L with
  | nil => exact inv_zero G
  | cons z L ih =>
    have hz := hL z (by simp)
    have hr := ih (fun x hx => hL x (by simp [hx]))
    have e : L.foldr (addV G.F) 0 = L.foldr (addV G.F) 0 := rfl
    have e2 : addV G.F z (L.foldr (addV G.F) 0) = G.add z (L.foldr (addV G.F) 0) := by
      funext i
      rw [formalGroup_add_apply_eq_ev]
      exact evV_eq_ev (GlobalTheory.DerivEndo.noConst_two hz.1 hr.1) _
    rw [List.foldr_cons, e2]
    exact inv_add G hz hr

theorem inv_matV {O : Type} [CommRing O] [StarRing O] (B : FB V d O) {n : ℕ}
    (p : Matrix (Fin n) (Fin n) O) (b : Fin n) :
    Inv B.G (matV B p (fun j => pt V (n := n) d j) b) := by
  unfold matV
  apply inv_foldr
  intro z hz
  rw [List.mem_ofFn] at hz
  obtain ⟨j, rfl⟩ := hz
  have e : compV (B.A.act (p b j)) (pt V (n := n) d j) = comp1 (B.A.act (p b j)) (pt V d j) := by
    funext i
    rw [comp1_apply_eq_ev_single]
    exact evV_eq_ev (GlobalTheory.DerivEndo.noConst_one (GlobalTheory.DerivEndo.cc_pt j)) _
  rw [e]
  exact inv_comp B.G _ (B.A.const _) (B.A.hom _) (inv_pt B.G j)

end Local

theorem det_jacobian_matV : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [IsAdicComplete (maximalIdeal V) V] [CharZero V] (d : ℕ) (O : Type) [CommRing O] [StarRing O]
    (B : FB V d O) (n : ℕ) (p : Matrix (Fin n) (Fin n) O), ∃ U : (PS V n d)ˣ,
    Matrix.det (Matrix.of fun i j : Fin n × Fin d =>
      MvPowerSeries.pderiv V j (matV B p (fun j => pt V (n := n) d j) i.1 i.2)) =
      MvPowerSeries.C (jacM B p) * (U : PS V n d) := by
  intro V _ _ _ _ _ d O _ _ B n p
  exact det_jac_of_inv B.G _ (fun b => inv_matV B p b)

end GlobalTheory.PlaceInt.MatJac
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.det_jacobian_formal_module_matrix_eq_const_mul_unit : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [CharZero V] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB V d O) (n : ℕ) (p : Matrix (Fin n) (Fin n) O), ∃ U : (PS V n d)ˣ, Matrix.det (Matrix.of fun i j : Fin n × Fin d => MvPowerSeries.pderiv V j (matV B p (fun j => pt V (n := n) d j) i.1 i.2)) = MvPowerSeries.C (jacM B p) * (U : PS V n d) := by
  atlas_forward_decl GlobalTheory.PlaceInt.MatJac.det_jacobian_matV
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
open scoped TensorProduct

namespace GlobalTheory.KerCard

theorem isReduced_baseChange_of_smul_kaehler_eq_zero (T Q C : Type) [CommRing T] [CommRing Q]
    [Algebra T Q] [Module.Finite T Q] [Field C] [Algebra T C] (δ : T) (hδ : algebraMap T C δ ≠ 0)
    (h : ∀ ω : KaehlerDifferential T Q, δ • ω = 0) : IsReduced (C ⊗[T] Q) := by
  letI : Algebra Q (C ⊗[T] Q) := Algebra.TensorProduct.rightAlgebra
  have hsub : Subsingleton (C ⊗[T] KaehlerDifferential T Q) := by
    refine subsingleton_of_forall_eq 0 fun x => ?_
    induction x using TensorProduct.induction_on with
    | zero => rfl
    | add x y hx hy => rw [hx, hy, add_zero]
    | tmul c ω =>
      have hc : c = δ • ((algebraMap T C δ)⁻¹ * c) := by
        rw [Algebra.smul_def, ← _root_.mul_assoc, mul_inv_cancel₀ hδ, _root_.one_mul]
      rw [hc, TensorProduct.smul_tmul, h, TensorProduct.tmul_zero]
  have : Algebra.FormallyUnramified C (C ⊗[T] Q) :=
    ⟨(KaehlerDifferential.tensorKaehlerEquivBase T C Q (C ⊗[T] Q)).symm.subsingleton⟩
  exact Algebra.FormallyUnramified.isReduced_of_field C (C ⊗[T] Q)

theorem algHom_ext_of_mem_maximalIdeal {V σ A : Type} [CommRing V] [IsLocalRing V]
    [IsNoetherianRing V] [IsAdicComplete (maximalIdeal V) V] [Finite σ] [CommRing A] [Algebra V A]
    (a : σ → V) (ha : ∀ j, a j ∈ maximalIdeal V) (φ φ' : MvPowerSeries σ V →ₐ[V] A)
    (h : ∀ j, φ (MvPowerSeries.X j) = algebraMap V A (a j))
    (h' : ∀ j, φ' (MvPowerSeries.X j) = algebraMap V A (a j)) : φ = φ' := by
  have hCa : ∀ c : V, (MvPowerSeries.C c : MvPowerSeries σ V) = algebraMap V _ c := fun c => rfl
  have hP := GlobalTheory.T.mvPowerSeries_exists_polynomial_totalDegree_le_sub_mem V (maximalIdeal V) (IsNoetherian.noetherian _) inferInstance σ σ
    (fun j => (MvPowerSeries.X j - MvPowerSeries.C (a j) : MvPowerSeries σ V)) 1 (by
      rw [pow_one, Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      have : (MvPowerSeries.X j : MvPowerSeries σ V) =
          (MvPowerSeries.X j - MvPowerSeries.C (a j)) + MvPowerSeries.C (a j) := by ring
      rw [this]
      exact Submodule.add_mem_sup (Ideal.subset_span ⟨j, rfl⟩)
        (Ideal.mem_map_of_mem _ (ha j)))
  have hk : ∀ ψ : MvPowerSeries σ V →ₐ[V] A,
      (∀ j, ψ (MvPowerSeries.X j) = algebraMap V A (a j)) → ∀ g ∈ Ideal.span (Set.range fun j =>
        (MvPowerSeries.X j - MvPowerSeries.C (a j) : MvPowerSeries σ V)), ψ g = 0 := by
    intro ψ hψ g hg
    have : Ideal.span (Set.range fun j =>
        (MvPowerSeries.X j - MvPowerSeries.C (a j) : MvPowerSeries σ V)) ≤ RingHom.ker ψ := by
      rw [Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      rw [SetLike.mem_coe, RingHom.mem_ker, map_sub, hψ, hCa, AlgHom.commutes, sub_self]
    exact this hg
  have hpol : ∀ P : MvPolynomial σ V, φ (P : MvPowerSeries σ V) = φ' (P : MvPowerSeries σ V) := by
    intro P
    induction P using MvPolynomial.induction_on with
    | C c => rw [MvPolynomial.coe_C, hCa, AlgHom.commutes, AlgHom.commutes]
    | add p q hp hq => rw [MvPolynomial.coe_add, map_add, map_add, hp, hq]
    | mul_X p j hp => rw [MvPolynomial.coe_mul, MvPolynomial.coe_X, map_mul, map_mul, hp, h, h']
  ext g
  obtain ⟨P, -, hP⟩ := hP g
  have h1 := hk φ h _ hP
  have h2 := hk φ' h' _ hP
  rw [map_sub, sub_eq_zero] at h1 h2
  rw [h1, h2, hpol]

theorem mem_maximalIdeal_of_map_X {V σ A : Type} [CommRing V] [IsLocalRing V] [CommRing A]
    [Nontrivial A] [Algebra V A] (φ : MvPowerSeries σ V →ₐ[V] A) (j : σ) (a : V)
    (h : φ (MvPowerSeries.X j) = algebraMap V A a) : a ∈ maximalIdeal V := by
  have hCa : ∀ c : V, (MvPowerSeries.C c : MvPowerSeries σ V) = algebraMap V _ c := fun c => rfl
  rw [mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  have h1 : IsUnit (MvPowerSeries.C a - MvPowerSeries.X j : MvPowerSeries σ V) := by
    rw [MvPowerSeries.isUnit_iff_constantCoeff]; simpa using hu
  have h2 := h1.map φ
  rw [map_sub, h, hCa, AlgHom.commutes, sub_self] at h2
  exact not_isUnit_zero h2

noncomputable def constAlgHom (V σ : Type) [CommRing V] : MvPowerSeries σ V →ₐ[V] V :=
  { (MvPowerSeries.constantCoeff : MvPowerSeries σ V →+* V) with
    commutes' := fun c => MvPowerSeries.constantCoeff_C c }

theorem eq_zero_of_constantCoeff {V σ : Type} [CommRing V] [IsEmpty σ] (g : MvPowerSeries σ V)
    (h : MvPowerSeries.constantCoeff g = 0) : g = 0 := by
  ext e
  have : e = 0 := Subsingleton.elim _ _
  subst this
  simpa using h

theorem finite_ncard_kerM : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [CharZero V] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB V d O), FinHt B → ∀ (n : ℕ) (p p' : Matrix (Fin n) (Fin n) O) (N : ℕ), 1 ≤ N → p' * p = (N : O) • (1 : Matrix (Fin n) (Fin n) O) → jacM B p ≠ 0 → SplitKer B p → (kerM B p).Finite ∧ (kerM B p).ncard = Module.finrank V (PS V n d ⧸ Ideal.span (Set.range fun s : Fin n × Fin d => matV B p (fun j => pt V (n := n) d j) s.1 s.2)) := by
  intro V _ _ _ _ _ d O _ _ B hB n p p' N hN hp hjac hsplit
  classical
  have hcol := GlobalTheory.T.exists_pow_span_X_le_span_formalModuleMatrix V d O B hB n p p' N hN hp
  obtain ⟨U, hU⟩ := GlobalTheory.T.det_jacobian_formal_module_matrix_eq_const_mul_unit V d O B n p
  have hmat : ∀ x : Fin n → Pt V 0 d,
      (∀ b i, MvPowerSeries.constantCoeff (x b i) ∈ maximalIdeal V) →
      (∀ b i, evV x (matV B p (fun j => pt V (n := n) d j) b i) = matV B p x b i) ∧
      (∀ b i, MvPowerSeries.constantCoeff (matV B p (fun j => pt V (n := n) d j) b i) = 0) :=
    fun x hx => ⟨(GlobalTheory.T.formalModuleMatrixApplyPoints_action_laws V d O B n 0 p p x x hx hx).2.2.2.2.1,
      (GlobalTheory.T.formalModuleMatrixApplyPoints_action_laws V d O B n 0 p p x x hx hx).2.2.2.2.2.1⟩
  have h0 := (hmat 0 (fun b i => by simp)).2
  set f : Fin n × Fin d → PS V n d :=
    fun s => matV B p (fun j => pt V (n := n) d j) s.1 s.2 with hf
  let e := (Fintype.equivFin (Fin n × Fin d)).symm
  have hff := GlobalTheory.FiniteColength.free_finite_quotient V inferInstance (Fin n × Fin d) _ e
    (fun j => f (e j)) (fun j => h0 _ _) (by
      have : (Set.range fun j => MvPowerSeries.map (σ := Fin n × Fin d) (residue V) (f (e j))) =
          Set.range fun s => MvPowerSeries.map (σ := Fin n × Fin d) (residue V) (f s) :=
        e.surjective.range_comp fun s => MvPowerSeries.map (σ := Fin n × Fin d) (residue V) (f s)
      rw [this]; exact hcol)
  have hr : (Set.range fun j => f (e j)) = Set.range f := e.surjective.range_comp f
  rw [hr] at hff
  obtain ⟨hfree, hfin⟩ := hff
  let Ω := AlgebraicClosure (FractionRing V)
  have hinj : Function.Injective (algebraMap V Ω) := by
    rw [IsScalarTower.algebraMap_eq V (FractionRing V) Ω]
    exact (algebraMap (FractionRing V) Ω).injective.comp (IsFractionRing.injective V _)
  set I := Ideal.span (Set.range f) with hI
  have hred : IsReduced (Ω ⊗[V] (PS V n d ⧸ I)) := by
    refine isReduced_baseChange_of_smul_kaehler_eq_zero V _ Ω (jacM B p)
      (fun h => hjac (hinj (by rw [h, map_zero]))) fun ω => ?_
    have h1 := GlobalTheory.FiniteQuotOmega.jacobian_smul_kaehler_eq_zero V (Fin n × Fin d) f hfin
      (Ideal.Quotient.mk I (↑U⁻¹ : PS V n d) • ω)
    rw [hU, smul_smul, ← map_mul, _root_.mul_assoc, Units.mul_inv, _root_.mul_one] at h1
    rw [← h1]
    exact (algebraMap_smul (PS V n d ⧸ I) (jacM B p) ω).symm
  obtain ⟨hF, hcard, -⟩ := GlobalTheory.finite_card_trace_algHom_of_isReduced_baseChange V
    (PS V n d ⧸ I) Ω hred
  have hfI : ∀ b i, Ideal.Quotient.mk I (matV B p (fun j => pt V (n := n) d j) b i) = 0 :=
    fun b i => Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨(b, i), rfl⟩)
  have hex : ∀ (χ : (PS V n d ⧸ I) →ₐ[V] Ω) (s : Fin n × Fin d), ∃ a : V,
      algebraMap V Ω a = χ.comp (Ideal.Quotient.mkₐ V I) (MvPowerSeries.X s) := fun χ s =>
    hsplit Ω hinj (χ.comp (Ideal.Quotient.mkₐ V I)) (fun b i => by
      rw [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, hfI, map_zero]) s
  choose G hG using hex
  have hGm : ∀ χ s, G χ s ∈ maximalIdeal V := fun χ s =>
    mem_maximalIdeal_of_map_X _ s _ (hG χ s).symm
  have hpt : ∀ α : Fin n → Fin d → V, (∀ b i, α b i ∈ maximalIdeal V) →
      ∃ ψ : PS V n d →ₐ[V] Ω, (∀ s, ψ (MvPowerSeries.X s) = algebraMap V Ω (α s.1 s.2)) ∧
        ∀ b i, ψ (matV B p (fun j => pt V (n := n) d j) b i) = algebraMap V Ω
          (MvPowerSeries.constantCoeff (matV B (m := 0) p (fun j => cpt (α j)) b i)) := by
    intro α hα
    have hx : ∀ b i, MvPowerSeries.constantCoeff ((fun j => cpt (n := 0) (α j)) b i) ∈
        maximalIdeal V := fun b i => by simpa [cpt] using hα b i
    obtain ⟨ψ, hψ, hψ'⟩ := (GlobalTheory.T.mvPowerSeriesSubstConstTerms_local_algHom_spec V (Fin n × Fin d) (Fin 0 × Fin d) (Fin 0 × Fin d)
      (fun s => cpt (n := 0) (α s.1) s.2) (fun s => hx s.1 s.2)).1
    refine ⟨(Algebra.ofId V Ω).comp ((constAlgHom V _).comp ψ), fun s => ?_, fun b i => ?_⟩
    · rw [AlgHom.comp_apply, AlgHom.comp_apply, hψ]
      exact congrArg (algebraMap V Ω) (MvPowerSeries.constantCoeff_C _)
    · rw [AlgHom.comp_apply, AlgHom.comp_apply, ← hψ', ← (hmat _ hx).1 b i]
      rfl
  let G' : ((PS V n d ⧸ I) →ₐ[V] Ω) → (Fin n → Fin d → V) := fun χ b i => G χ (b, i)
  have hG'inj : Function.Injective G' := by
    intro χ χ' h
    have h1 := algHom_ext_of_mem_maximalIdeal (G χ) (hGm χ) _ (χ'.comp (Ideal.Quotient.mkₐ V I))
      (fun s => (hG χ s).symm) (fun s => by
        rw [← hG χ' s]; exact congrArg (algebraMap V Ω) (congrFun (congrFun h s.1) s.2).symm)
    exact Ideal.Quotient.algHom_ext V h1
  have hrange : kerM B p = Set.range G' := by
    ext α
    constructor
    · rintro ⟨hs, hz⟩
      obtain ⟨ψ, hψ, hψ'⟩ := hpt α hs
      have hker : ∀ g ∈ I, ψ g = 0 := by
        have : I ≤ RingHom.ker ψ := by
          rw [hI, Ideal.span_le]
          rintro _ ⟨s, rfl⟩
          rw [SetLike.mem_coe, RingHom.mem_ker]
          refine (hψ' s.1 s.2).trans ?_
          rw [hz]; simp
        exact fun g hg => this hg
      refine ⟨Ideal.Quotient.liftₐ I ψ hker, ?_⟩
      funext b i
      apply hinj
      refine (hG _ (b, i)).trans ?_
      exact hψ (b, i)
    · rintro ⟨χ, rfl⟩
      refine ⟨fun b i => hGm χ (b, i), ?_⟩
      obtain ⟨ψ, hψ, hψ'⟩ := hpt (G' χ) fun b i => hGm χ (b, i)
      have h1 := algHom_ext_of_mem_maximalIdeal (G χ) (hGm χ) _ ψ
        (fun s => (hG χ s).symm) hψ
      funext b i
      refine eq_zero_of_constantCoeff _ (hinj ?_)
      rw [← hψ', ← h1, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, hfI, map_zero, map_zero]
  rw [hrange]
  refine ⟨Set.finite_range _, ?_⟩
  rw [← hcard, ← Nat.card_coe_set_eq, Nat.card_range_of_injective hG'inj]

end GlobalTheory.KerCard
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formalMatrixKernel_finite_ncard_eq_rank : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [CharZero V] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB V d O), FinHt B → ∀ (n : ℕ) (p p' : Matrix (Fin n) (Fin n) O) (N : ℕ), 1 ≤ N → p' * p = (N : O) • (1 : Matrix (Fin n) (Fin n) O) → jacM B p ≠ 0 → SplitKer B p → (kerM B p).Finite ∧ (kerM B p).ncard = Module.finrank V (PS V n d ⧸ Ideal.span (Set.range fun s : Fin n × Fin d => matV B p (fun j => pt V (n := n) d j) s.1 s.2)) := by
  atlas_forward_decl GlobalTheory.KerCard.finite_ncard_kerM
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formalGroupTranslate_automorphism_and_matrixKernel : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [CharZero V] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB V d O) (n : ℕ) (p : Matrix (Fin n) (Fin n) O), (0 ∈ kerM B p) ∧ (∀ f : PS V n d, shift B.G.F 0 f = f) ∧ ∀ α β : Fin n → Fin d → V, (∀ b, Small (α b)) → (∀ b, Small (β b)) → (∃ ψ : PS V n d ≃ₐ[V] PS V n d, ∀ f, shift B.G.F α f = ψ f) ∧ (α ∈ kerM B p ↔ ∀ f, shift B.G.F α (pullM B p f) = pullM B p f) ∧ ((∀ f, shift B.G.F α f = shift B.G.F β f) → α = β) ∧ ∃ δ : Fin n → Fin d → V, (∀ b, Small (δ b)) ∧ (∀ b, (cpt (δ b) : Pt V 0 d) = addV B.G.F (cpt (α b)) (cpt (β b))) ∧ (∀ f, shift B.G.F α (shift B.G.F β f) = shift B.G.F δ f) ∧ (α ∈ kerM B p → β ∈ kerM B p → δ ∈ kerM B p) := by
  first | exact @GlobalTheory.PlaceInt.shift_kerM | exact GlobalTheory.PlaceInt.shift_kerM | (intros; apply GlobalTheory.PlaceInt.shift_kerM <;> assumption)
end

section
section
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
namespace GlobalTheory.PlaceInt

theorem mem_range_of_invariant (A R : Type) [CommRing A] [IsDomain A] [CommRing R] [IsDomain R] (Φ : A →+* R)
    (r : ℕ) (b : Fin r → R) (hb : ∀ f, ∃! cf : Fin r → A, f = ∑ i, Φ (cf i) * b i)
    {J : Type} (S : Set J) (hS : S.Finite) (hc : S.ncard = r) (g : J → R → R)
    (hg : ∀ α ∈ S, ∃ ψ : R →+* R, ∀ f, g α f = ψ f) (hfix : ∀ α ∈ S, ∀ a, g α (Φ a) = Φ a)
    (hinj : ∀ α ∈ S, ∀ β ∈ S, (∀ f, g α f = g β f) → α = β) (x : R) (hx : ∀ α ∈ S, g α x = x) :
    ∃ a, x = Φ a := by
  classical
  let _ : Algebra A R := Φ.toAlgebra
  have hsm : ∀ (a : A) (y : R), a • y = Φ a * y := fun a y => rfl
  have hli : LinearIndependent A b := by
    rw [Fintype.linearIndependent_iff]
    intro c hc0
    have h0 := (hb 0).unique (y₁ := c) (y₂ := 0) (by simpa [hsm] using hc0.symm) (by simp)
    intro i
    rw [h0]; rfl
  have hsp : ⊤ ≤ Submodule.span A (Set.range b) := by
    intro f _
    obtain ⟨c, hc, -⟩ := hb f
    rw [hc]
    exact Submodule.sum_mem _ fun i _ => (hsm (c i) (b i)) ▸
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  let bs : Module.Basis (Fin r) A R := Module.Basis.mk hli hsp
  have : Module.Free A R := Module.Free.of_basis bs
  have : Module.Finite A R := Module.Finite.of_basis bs
  have hr : Module.finrank A R = r := by rw [Module.finrank_eq_card_basis bs, Fintype.card_fin]
  choose ψ hψ using hg
  let G : S → (R →ₐ[A] R) := fun α =>
    { ψ α.1 α.2 with
      commutes' := fun a => by
        have := hfix α.1 α.2 a
        rw [hψ α.1 α.2] at this
        exact this }
  have hG : ∀ (α : S) f, G α f = g α.1 f := fun α f => (hψ α.1 α.2 f).symm
  have hGi : Function.Injective G := fun α β h =>
    Subtype.ext (hinj _ α.2 _ β.2 fun f => by rw [← hG, ← hG, h])
  have : Fintype S := hS.fintype
  have hcard : (Finset.univ.image G).card = Module.finrank A R := by
    rw [Finset.card_image_of_injective _ hGi, hr, ← hc, Finset.card_univ, ← Nat.card_eq_fintype_card]
    rfl
  obtain ⟨a, ha⟩ := (GlobalTheory.PlaceInt.invariants_and_trace_of_card_eq_finrank A R _ hcard).1 x (by
    intro g0 hg0
    obtain ⟨α, -, rfl⟩ := Finset.mem_image.1 hg0
    rw [hG, hx _ α.2])
  exact ⟨a, ha.symm⟩

theorem descends_of_invariant : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [CharZero V] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB V d O), FinHt B → ∀ (n : ℕ) (q q' : Matrix (Fin n) (Fin n) O) (N : ℕ), 1 ≤ N → q' * q = (N : O) • (1 : Matrix (Fin n) (Fin n) O) → jacM B q ≠ 0 → SplitKer B q → ∀ f : PS V n d, (∀ α ∈ kerM B q, shift B.G.F α f = f) → ∃ f', f = pullM B q f' := by
  intro V _ _ _ _ _ d O _ _ B hB n q q' N hN hq hj hs f hf
  have h0 : ∀ b i, MvPowerSeries.constantCoeff (matV B q (fun j => pt V (n := n) d j) b i) = 0 :=
    (GlobalTheory.T.formalModuleMatrixApplyPoints_action_laws V d O B n 0 q q 0 0 (fun b i => by simp) (fun b i => by simp)).2.2.2.2.2.1
  set φ : Fin n × Fin d → MvPowerSeries (Fin n × Fin d) V :=
    fun s => matV B q (fun j => pt V (n := n) d j) s.1 s.2 with hφ
  have hφ0 : ∀ s, MvPowerSeries.constantCoeff (φ s) = 0 := fun s => h0 s.1 s.2
  obtain ⟨⟨Ψ, -, hΨ⟩, -, hsub, -⟩ := GlobalTheory.PlaceInt.evC_spec V (Fin n × Fin d) (Fin n × Fin d) (Fin n × Fin d) φ
    (fun s => by rw [hφ0]; exact Ideal.zero_mem _)
  have hp : ∀ a, pullM B q a = Ψ a := fun a => hΨ a
  have hs' : ∀ a, MvPowerSeries.subst φ a = Ψ a := fun a => (hsub hφ0 a).symm.trans (hΨ a)
  obtain ⟨r, b, hr, hb⟩ := GlobalTheory.FiniteColength.exists_basis_subst_finrank_quotient V (Fin n × Fin d) φ hφ0 (GlobalTheory.T.exists_pow_span_X_le_span_formalModuleMatrix V d O B hB n q q' N hN hq)
  obtain ⟨hfin, hcard⟩ := GlobalTheory.T.formalMatrixKernel_finite_ncard_eq_rank V d O B hB n q q' N hN hq hj hs
  have : IsDomain (MvPowerSeries (Fin n × Fin d) V) := NoZeroDivisors.to_isDomain _
  have hsh := (GlobalTheory.T.formalGroupTranslate_automorphism_and_matrixKernel V d O B n q).2.2
  obtain ⟨a, ha⟩ := mem_range_of_invariant (MvPowerSeries (Fin n × Fin d) V) (MvPowerSeries (Fin n × Fin d) V)
    (Ψ : MvPowerSeries (Fin n × Fin d) V →+* MvPowerSeries (Fin n × Fin d) V) r b
    (fun f => by simpa only [hs', RingHom.coe_coe] using hb f) (kerM B q) hfin (hcard.trans hr) (shift B.G.F)
    (fun α hα => by
      obtain ⟨ψ, hψ⟩ := (hsh α α hα.1 hα.1).1
      exact ⟨ψ.toRingEquiv.toRingHom, hψ⟩)
    (fun α hα a => by
      have := (hsh α α hα.1 hα.1).2.1.1 hα a
      rw [hp] at this
      exact this)
    (fun α hα β hβ h => (hsh α β hα.1 hβ.1).2.2.1 h) f hf
  exact ⟨a, ha.trans (hp a).symm⟩

end GlobalTheory.PlaceInt
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formalSeries_descends_of_splitKernel_invariant : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [CharZero V] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB V d O), FinHt B → ∀ (n : ℕ) (q q' : Matrix (Fin n) (Fin n) O) (N : ℕ), 1 ≤ N → q' * q = (N : O) • (1 : Matrix (Fin n) (Fin n) O) → jacM B q ≠ 0 → SplitKer B q → ∀ f : PS V n d, (∀ α ∈ kerM B q, shift B.G.F α f = f) → ∃ f', f = pullM B q f' := by
  atlas_forward_decl GlobalTheory.PlaceInt.descends_of_invariant
end

section
namespace GlobalTheory.TraceDiagonal

open IsLocalRing
open scoped TensorProduct

theorem exists_trace_eq_of_isUnit_det {A R : Type} [CommRing A] [CommRing R] [Algebra A R]
    {d : ℕ} (b : Module.Basis (Fin d) A R) (M : Matrix (Fin d) (Fin d) A)
    (h : ∀ x : R, (∑ i, ∑ j, M i j • TensorProduct.tmul A (b i) (b j)) *
      (TensorProduct.tmul A x 1 - TensorProduct.tmul A 1 x) = 0) (hu : IsUnit M.det) :
    ∃ lam : R →ₗ[A] A, ∀ x : R,
      Algebra.trace A R x = lam (x * ∑ i, ∑ j, M i j • (b i * b j)) := by
  have hΦ : ∀ f : R →ₗ[A] A, ∑ i, ∑ j, (M i j * f (b i)) • b j
      = b.equivFun.symm (Matrix.vecMul (fun i => f (b i)) M) := by
    intro f
    rw [b.equivFun_symm_apply, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [Matrix.vecMul, dotProduct, Finset.sum_smul, mul_comm]
  set J : R := ∑ i, ∑ j, M i j • (b i * b j) with hJ
  let lam : R →ₗ[A] A := b.constr A (Matrix.vecMul (b.equivFun 1) M⁻¹)
  have h1 : ∑ i, ∑ j, (M i j * lam (b i)) • b j = 1 := by
    have e : (fun i => lam (b i)) = Matrix.vecMul (b.equivFun 1) M⁻¹ :=
      funext fun i => b.constr_basis A _ i
    rw [hΦ, e, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hu, Matrix.vecMul_one,
      LinearEquiv.symm_apply_apply]
  have h2 : ∑ i, ∑ j, (M i j * (lam ∘ₗ LinearMap.mulRight A J) (b i)) • b j = J := by
    have := annihilator_diagonal_form_swap b M h lam J
    simp only [LinearMap.comp_apply, LinearMap.mulRight_apply]
    rw [this]
    simp only [← smul_mul_assoc, ← Finset.sum_mul]
    rw [h1, one_mul]
  have h3 := annihilator_diagonal_trace b M h
  rw [← hJ, ← h2, hΦ, hΦ] at h3
  have h4 := congrArg (fun v => Matrix.vecMul v M⁻¹) (b.equivFun.symm.injective h3)
  simp only [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hu, Matrix.vecMul_one] at h4
  have h5 : Algebra.trace A R = lam ∘ₗ LinearMap.mulRight A J := b.ext fun i => congrFun h4 i
  exact ⟨lam, fun x => by rw [h5]; rfl⟩

end GlobalTheory.TraceDiagonal

namespace GlobalTheory

open IsLocalRing

theorem exists_trace_eq_form_mul_diagonal : ∀ (A R : Type) [CommRing A] [IsLocalRing A] [CommRing R] [Algebra A R] [Module.Free A R] [Module.Finite A R] (Δ : TensorProduct A R R) (ε : R →+* ResidueField A), ε.comp (algebraMap A R) = residue A → (∀ x : R, ε x = 0 → ∃ m : ℕ, x ^ m ∈ (maximalIdeal A).map (algebraMap A R)) → (∀ x : R, (TensorProduct.tmul A x 1 - TensorProduct.tmul A 1 x) * Δ = 0) → (∀ (s : Finset (R × R)), Δ = ∑ p ∈ s, TensorProduct.tmul A p.1 p.2 → ∀ lift : ResidueField A → A, (∀ z, residue A (lift z) = z) → ∑ p ∈ s, lift (ε p.1) • p.2 ∉ (maximalIdeal A).map (algebraMap A R)) → ∃ lam : R →ₗ[A] A, ∀ x : R, Algebra.trace A R x = lam (x * Algebra.TensorProduct.lmul' (S := R) A Δ) := by
  intro A R _ _ _ _ _ _ Δ ε hε hnil hΔ hne
  classical
  let b := Module.finBasis A R
  let M : Matrix (Fin (Module.finrank A R)) (Fin (Module.finrank A R)) A :=
    Matrix.of fun i j => (b.tensorProduct b).repr Δ (i, j)
  have hM : Δ = ∑ i, ∑ j, M i j • TensorProduct.tmul A (b i) (b j) := by
    conv_lhs => rw [← (b.tensorProduct b).sum_repr Δ, Fintype.sum_prod_type]
    simp [M]
  have hJ : Algebra.TensorProduct.lmul' (S := R) A Δ = ∑ i, ∑ j, M i j • (b i * b j) := by
    rw [hM]; simp
  rw [hJ]
  refine TraceDiagonal.exists_trace_eq_of_isUnit_det b M (fun x => by rw [← hM, mul_comm, hΔ]) ?_
  let k := ResidueField A
  let I : Ideal R := (maximalIdeal A).map (algebraMap A R)
  letI : Algebra k (R ⧸ I) := Ideal.Quotient.algebraQuotientMapQuotient
  haveI : IsScalarTower A k (R ⧸ I) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  obtain ⟨lift, hlift⟩ := (residue_surjective (R := A)).hasRightInverse
  have hεa : ∀ a, ε (algebraMap A R a) = residue A a := fun a => RingHom.congr_fun hε a
  let ev : R →ₐ[A] k := { ε with commutes' := hεa }
  have hev : ∀ x, ev x = ε x := fun _ => rfl
  let n : Ideal R := Ideal.span (Set.range fun i => b i - algebraMap A R (lift (ε (b i))))
  obtain ⟨N, hN⟩ : ∃ N, n ^ N ≤ I := by
    refine Ideal.exists_pow_le_of_le_radical_of_fg ?_ (Submodule.fg_span (Set.finite_range _))
    refine Ideal.span_le.2 ?_
    rintro _ ⟨j, rfl⟩
    exact hnil _ (by rw [map_sub, hεa, hlift, sub_self])
  obtain ⟨s, hs⟩ := TensorProduct.exists_finset Δ
  rw [← Matrix.det_transpose]
  refine DiscrJacobian.isUnit_det_of_productMap_ne_zero (C := R ⧸ I) b n N hN ev ?_ ?_
    (Ideal.Quotient.mkₐ A I) (Algebra.TensorProduct.comm A R R Δ) M.transpose ?_ ?_ ?_
  · intro w hw
    have : n ≤ RingHom.ker ev := Ideal.span_le.2 (by
      rintro _ ⟨j, rfl⟩
      simp only [SetLike.mem_coe, RingHom.mem_ker, hev]
      rw [map_sub, hεa, hlift, sub_self])
    exact this hw
  · intro w
    refine ⟨∑ i, b.repr w i * lift (ε (b i)), ?_⟩
    have e : w - algebraMap A R (∑ i, b.repr w i * lift (ε (b i)))
        = ∑ i, algebraMap A R (b.repr w i) * (b i - algebraMap A R (lift (ε (b i)))) := by
      conv_lhs => lhs; rw [← b.sum_repr w]
      simp only [map_sum, map_mul, mul_sub, Finset.sum_sub_distrib, Algebra.smul_def]
    rw [e]
    exact n.sum_mem fun j _ => n.mul_mem_left _ (Ideal.subset_span ⟨j, rfl⟩)
  · rw [hM, Finset.sum_comm]
    simp
  · intro x
    have := congrArg (Algebra.TensorProduct.comm A R R) (hΔ x)
    rw [map_mul, map_sub, map_zero, Algebra.TensorProduct.comm_tmul,
      Algebra.TensorProduct.comm_tmul] at this
    linear_combination -this
  · intro h0
    refine hne s hs lift hlift (Ideal.Quotient.eq_zero_iff_mem.1 ?_)
    rw [← h0, hs, map_sum, map_sum, map_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    have e : algebraMap k (R ⧸ I) (ε p.1) = Ideal.Quotient.mk I (algebraMap A R (lift (ε p.1))) := by
      conv_lhs => rw [← hlift (ε p.1)]
      rfl
    rw [Algebra.smul_def, map_mul, ← e, mul_comm]
    rfl

end GlobalTheory
end

section
section
open IsLocalRing MvPowerSeries
open scoped TensorProduct

namespace GlobalTheory.TraceJacobian

theorem det_notMem_span (k : Type) [Field k] (σ : Type) [Fintype σ] [DecidableEq σ] (N : ℕ)
    (f : σ → MvPowerSeries σ k) (a : Matrix σ σ (MvPowerSeries σ k))
    (hf : ∀ i, f i = ∑ j, a i j * X j)
    (hN : ∀ i, (X i : MvPowerSeries σ k) ^ N ∈ Ideal.span (Set.range f)) :
    a.det ∉ Ideal.span (Set.range f) := by
  let e := Fintype.equivFin σ
  let ρ : MvPowerSeries σ k ≃ₐ[k] MvPowerSeries (Fin (Fintype.card σ)) k := renameEquiv k e
  have hX : ∀ j, ρ (X j) = X (e j) := fun j => by simp [ρ]
  have hmap : ∀ s ∈ Ideal.span (Set.range f),
      ρ s ∈ Ideal.span (Set.range fun i => ρ (f (e.symm i))) := by
    intro s hs
    obtain ⟨u, rfl⟩ := Ideal.mem_span_range_iff_exists_fun.1 hs
    rw [map_sum]
    refine Ideal.sum_mem _ fun j _ => ?_
    rw [map_mul]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨e j, by simp⟩)
  intro hdet
  refine SocleDet.det_notMem_span k _ N (fun i => ρ (f (e.symm i)))
    ((ρ.toAlgHom.mapMatrix a).submatrix e.symm e.symm) (fun i => ?_) (fun i => ?_) ?_
  · rw [hf, map_sum, ← e.symm.sum_comp]
    simp [hX]
  · have := hmap _ (hN (e.symm i))
    rwa [map_pow, hX, e.apply_symm_apply] at this
  · rw [Matrix.det_submatrix_equiv_self, ← AlgHom.map_det]
    exact hmap _ hdet

theorem exists_eq_C_add_sum {R σ : Type} [CommRing R] [Fintype σ] (s : MvPowerSeries σ R) :
    ∃ u : σ → MvPowerSeries σ R, s = C (constantCoeff s) + ∑ j, X j * u j := by
  have h := SocleDet.mem_span_X_of_coeff Finset.univ (s - C (constantCoeff s)) (fun m hm => by
    have : m = 0 := Finsupp.ext fun j => hm j (Finset.mem_univ j)
    subst this
    simp)
  rw [Finset.coe_univ, Set.image_univ] at h
  obtain ⟨u, hu⟩ := Ideal.mem_span_range_iff_exists_fun.1 h
  exact ⟨u, by simp only [mul_comm (X _), hu]; ring⟩

theorem exists_ringHom_eval {A B σ : Type} [CommRing A] [CommRing B] [Finite σ] (ι : A →+* B)
    (K : Ideal B) [h : IsAdicComplete K B] (a : σ → B) (ha : ∀ j, a j ∈ K) :
    ∃ θ : MvPowerSeries σ A →+* B, (∀ c, θ (C c) = ι c) ∧ ∀ j, θ (X j) = a j := by
  letI := ι.toAlgebra
  obtain ⟨ψ, hψ⟩ := (mvPowerSeries_eval_of_pow_mem B K σ a fun j => ⟨1, by simpa using ha j⟩).1 h A
  exact ⟨ψ, fun c => ψ.commutes c, hψ⟩

open DiscrJacobian in

theorem exists_trace_eq {A B σ : Type} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [CommRing B] [Fintype σ] [DecidableEq σ] [Algebra A B] [Algebra (MvPowerSeries σ A) B]
    [IsScalarTower A (MvPowerSeries σ A) B] [Module.Free A B] [Module.Finite A B]
    (hsurj : Function.Surjective (algebraMap (MvPowerSeries σ A) B))
    (f : σ → MvPowerSeries σ A) (hf0 : ∀ i, algebraMap _ B (f i) = 0)
    (ε : B →+* ResidueField A)
    (hε : ∀ s : MvPowerSeries σ A, ε (algebraMap _ B s) = residue A (constantCoeff s))
    (hW : ∀ a : Matrix σ σ B, (∀ i, algebraMap A B (constantCoeff (f i)) =
        ∑ j, a i j * -algebraMap (MvPowerSeries σ A) B (X j)) →
      a.det ∉ (maximalIdeal A).map (algebraMap A B)) :
    ∃ lam : B →ₗ[A] A, ∀ x : B, Algebra.trace A B x =
      lam (x * algebraMap _ B (Matrix.of fun i j => pderiv A j (f i)).det) := by
  let S := MvPowerSeries σ A
  have : Module.Finite S B := Module.Finite.of_restrictScalars_finite A S B
  have : Module.FinitePresentation S B := Module.finitePresentation_of_finite S B
  let t : σ → S ⊗[A] B := fun j => (X j : S) ⊗ₜ[A] (1 : B) - (1 : S) ⊗ₜ[A] algebraMap S B (X j)
  have hker : ∀ z : S ⊗[A] B, mu A S B z = 0 → z ∈ Ideal.span (Set.range t) :=
    mem_span_of_mu_eq_zero (fun j => (X j : S)) X_mem_jacobson fun s =>
      ⟨constantCoeff s, exists_eq_C_add_sum s⟩
  choose a ha using fun i => Ideal.mem_span_range_iff_exists_fun.1
    (hker (f i ⊗ₜ 1) (by simp [S, hf0]))
  let P : Matrix σ σ (S ⊗[A] B) := Matrix.of a
  have hmt : ∀ j, mu A S B (t j) = 0 := fun j => by simp [t]
  have hmu : ∀ i j, mu A S B (a i j) = algebraMap S B (pderiv A j (f i)) := by
    intro i j
    have := congrArg (der (S := S) (B := B) (pderiv A j)) (ha i)
    simp only [map_sum, der_mul, hmt, zero_mul, add_zero, der_tmul, mul_one] at this
    rw [← this, Finset.sum_eq_single j]
    · simp [t, S]
    · intro l _ hl
      simp [t, S, hl]
    · simp
  let q : S →ₐ[A] B := IsScalarTower.toAlgHom A S B
  let π : S ⊗[A] B →ₐ[A] B ⊗[A] B := Algebra.TensorProduct.map q (AlgHom.id A B)
  have hπ : ∀ s w, π (s ⊗ₜ w) = algebraMap S B s ⊗ₜ w := fun s w => rfl
  have hDt : ∀ z ∈ Ideal.span (Set.range t), π z * π P.det = 0 := by
    intro z hz
    obtain ⟨c, rfl⟩ := Ideal.mem_span_range_iff_exists_fun.1 hz
    rw [map_sum, Finset.sum_mul]
    refine Finset.sum_eq_zero fun j _ => ?_
    have := SocleDet.det_mul_mem (RingHom.ker π) P t j fun r => by
      have : (P.mulVec t) r = f r ⊗ₜ 1 := ha r
      rw [this, RingHom.mem_ker, hπ, hf0, TensorProduct.zero_tmul]
    rw [RingHom.mem_ker, map_mul] at this
    rw [map_mul, mul_assoc, mul_comm (π (t j)), this, mul_zero]
  have hD : ∀ x : B, (TensorProduct.tmul A x 1 - TensorProduct.tmul A 1 x) * π P.det = 0 := by
    intro x
    obtain ⟨s, rfl⟩ := hsurj x
    have := hDt _ (hker (s ⊗ₜ 1 - 1 ⊗ₜ algebraMap S B s) (by simp))
    rwa [map_sub, hπ, hπ, map_one] at this
  have hJ : Algebra.TensorProduct.lmul' (S := B) A (π P.det)
      = algebraMap S B (Matrix.of fun i j => pderiv A j (f i)).det := by
    have e : ∀ z, Algebra.TensorProduct.lmul' (S := B) A (π z) = mu A S B z := by
      intro z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | add a b ha hb => simp only [map_add, ha, hb]
      | tmul s w => simp [hπ]
    rw [e, AlgHom.map_det, RingHom.map_det]
    congr 1
    ext i j
    exact hmu i j
  rw [← hJ]
  have hεA : ∀ c, ε (algebraMap A B c) = residue A c := fun c => by
    rw [IsScalarTower.algebraMap_apply A S B, hε]
    simp [S, MvPowerSeries.algebraMap_apply]
  let m : Ideal B := (maximalIdeal A).map (algebraMap A B)
  refine exists_trace_eq_form_mul_diagonal A B _ ε (RingHom.ext hεA) (fun x hx => ?_) hD ?_
  · obtain ⟨s, rfl⟩ := hsurj x
    obtain ⟨u, hu⟩ := exists_eq_C_add_sum s
    rw [hε, residue_eq_zero_iff] at hx
    change _ ∈ m.radical
    rw [hu, map_add, map_sum]
    refine add_mem (Ideal.le_radical ?_) (Ideal.sum_mem _ fun j _ => ?_)
    · have : algebraMap S B (C (constantCoeff s)) = algebraMap A B (constantCoeff s) :=
        (IsScalarTower.algebraMap_apply A S B _).symm
      rw [this]
      exact Ideal.mem_map_of_mem _ hx
    · rw [map_mul]
      exact Ideal.mul_mem_right _ _ (map_mem_radical hsurj (X_mem_jacobson j))
  · intro s hs lift hlift hmem
    let κ : ResidueField A →+* B ⧸ m :=
      Ideal.Quotient.lift _ ((Ideal.Quotient.mk m).comp (algebraMap A B)) fun c hc =>
        Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem _ hc)
    have hκ : ∀ c, κ (residue A c) = Ideal.Quotient.mk m (algebraMap A B c) := fun c => rfl
    let E : B →ₐ[A] B ⧸ m :=
      { κ.comp ε with commutes' := fun c => by simp [hεA, hκ] }
    have hE : ∀ x, E x = κ (ε x) := fun x => rfl
    let cc : S →ₐ[A] B :=
      { (algebraMap A B).comp (constantCoeff : S →+* A) with
        commutes' := fun r => by simp [S, MvPowerSeries.algebraMap_apply] }
    have hcc : ∀ s, cc s = algebraMap A B (constantCoeff s) := fun s => rfl
    let η : S ⊗[A] B →ₐ[A] B := Algebra.TensorProduct.productMap cc (AlgHom.id A B)
    have hη : ∀ s w, η (s ⊗ₜ w) = algebraMap A B (constantCoeff s) * w := fun s w => rfl
    have e : ∀ z, Algebra.TensorProduct.productMap E (Ideal.Quotient.mkₐ A m) (π z)
        = Ideal.Quotient.mk m (η z) := by
      intro z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | add a b ha hb => simp only [map_add, ha, hb]
      | tmul s w =>
        rw [hπ, hη, map_mul, ← hκ, ← hε]; rfl
    have h1 := e P.det
    rw [hs, map_sum, AlgHom.map_det] at h1
    refine hW (η.mapMatrix P) (fun i => ?_) ?_
    · have := congrArg η (ha i)
      simp only [map_sum, map_mul, hη, mul_one] at this
      rw [← this]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp [t, hη, P, S]
    · rw [← Ideal.Quotient.eq_zero_iff_mem, ← h1, ← Ideal.Quotient.eq_zero_iff_mem.2 hmem, map_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [Algebra.smul_def, map_mul, ← hκ, hlift]
      rfl

theorem dvd_trace_of_ringHom {A B σ : Type} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [CommRing B] [Fintype σ] [DecidableEq σ] (θ : MvPowerSeries σ A →+* B) (ι : A →+* B)
    (hι : ∀ c, θ (C c) = ι c) (hsurj : Function.Surjective θ)
    (f : σ → MvPowerSeries σ A) (hf0 : ∀ i, θ (f i) = 0)
    (ε : B →+* ResidueField A) (hε : ∀ s, ε (θ s) = residue A (constantCoeff s))
    (hW : ∀ a : Matrix σ σ B, (∀ i, ι (constantCoeff (f i)) = ∑ j, a i j * -θ (X j)) →
      a.det ∉ (maximalIdeal A).map ι)
    (δ : A) (U : B) (hJ : θ (Matrix.of fun i j => pderiv A j (f i)).det = ι δ * U)
    {r : ℕ} (b : Fin r → B) (hb : ∀ g, ∃! c : Fin r → A, g = ∑ i, ι (c i) * b i)
    (g : B) (M : Matrix (Fin r) (Fin r) A) (hM : ∀ j, g * b j = ∑ i, ι (M i j) * b i) :
    δ ∣ M.trace := by
  letI := ι.toAlgebra
  letI := θ.toAlgebra
  haveI : IsScalarTower A (MvPowerSeries σ A) B := IsScalarTower.of_algebraMap_eq fun c => (hι c).symm
  have hsm : ∀ (c : A) (x : B), c • x = ι c * x := fun c x => rfl
  let β : Module.Basis (Fin r) A B := Module.Basis.mk (v := b)
    (Fintype.linearIndependent_iff.2 fun c hc => by
      have := (hb 0).unique (y₁ := c) (y₂ := 0) hc.symm (by simp)
      exact congrFun this)
    (fun x _ => by
      obtain ⟨c, hc, -⟩ := hb x
      exact (Submodule.mem_span_range_iff_exists_fun A).2 ⟨c, hc.symm⟩)
  have hβ : ∀ i, β i = b i := fun i => Module.Basis.mk_apply _ _ i
  haveI : Module.Free A B := Module.Free.of_basis β
  haveI : Module.Finite A B := Module.Finite.of_basis β
  obtain ⟨lam, hlam⟩ := exists_trace_eq (A := A) (B := B) hsurj f hf0 ε hε hW
  have e : Algebra.leftMulMatrix β g = M := by
    ext i j
    rw [Algebra.leftMulMatrix_eq_repr_mul, hβ, hM]
    simp only [← hsm, ← hβ]
    rw [β.repr_sum_self]
  rw [← e, ← Algebra.trace_eq_matrix_trace, hlam]
  refine ⟨lam (g * U), ?_⟩
  change lam (g * θ _) = _
  rw [hJ, mul_left_comm, ← hsm, map_smul, smul_eq_mul]

end GlobalTheory.TraceJacobian

namespace GlobalTheory

theorem C_dvd_trace_of_jacobian : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [CharZero V] (σ : Type) [Fintype σ] [DecidableEq σ] (φ : σ → MvPowerSeries σ V), (∀ j, MvPowerSeries.constantCoeff (φ j) = 0) → (∃ M : ℕ, Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ (ResidueField V))) ^ M ≤ Ideal.span (Set.range fun j => MvPowerSeries.map (residue V) (φ j))) → ∀ (δ : V) (U : (MvPowerSeries σ V)ˣ), δ ≠ 0 → Matrix.det (Matrix.of fun i j : σ => MvPowerSeries.pderiv V j (φ i)) = MvPowerSeries.C δ * (U : MvPowerSeries σ V) → ∀ (r : ℕ) (b : Fin r → MvPowerSeries σ V), (∀ f, ∃! cf : Fin r → MvPowerSeries σ V, f = ∑ i, MvPowerSeries.subst φ (cf i) * b i) → ∀ (f : MvPowerSeries σ V) (M : Matrix (Fin r) (Fin r) (MvPowerSeries σ V)), (∀ j, f * b j = ∑ i, MvPowerSeries.subst φ (M i j) * b i) → MvPowerSeries.C δ ∣ M.trace := by
  intro V _ _ _ _ _ σ _ _ φ h0 hM δ U _ hJ r b hb g M hg
  have hs : HasSubst φ := hasSubst_of_constantCoeff_zero h0
  let ι : MvPowerSeries σ V →ₐ[V] MvPowerSeries σ V := substAlgHom hs
  have hι : ∀ c, ι c = subst φ c := fun c => substAlgHom_apply hs c
  have hιX : ∀ j, ι (X j) = φ j := fun j => substAlgHom_X hs j
  have hιC : ∀ c, ι (C c) = C c := fun c => ι.commutes c
  have hcomp := PlaceInt.isAdicComplete_mvPowerSeries_finite (V := V) σ
  have hXm : ∀ j, (X j : MvPowerSeries σ V) ∈ maximalIdeal _ := fun j =>
    (PlaceInt.mem_maximalIdeal_mvPowerSeries_iff _).2 (by simp)
  obtain ⟨θ, hθC, hθX⟩ := TraceJacobian.exists_ringHom_eval (ι : MvPowerSeries σ V →+* _)
    (maximalIdeal _) X hXm
  have hθ : θ.comp (MvPowerSeries.map (C : V →+* MvPowerSeries σ V)) = RingHom.id _ :=
    (mvPowerSeries_eval_of_pow_mem _ (maximalIdeal _) σ X
      fun j => ⟨1, by simpa using hXm j⟩).2 inferInstance V _ _
      (fun t => by simp [hθC, hιC]) (fun j => by simp [hθX]) (fun j => rfl)
  have hθm : ∀ s, θ (MvPowerSeries.map C s) = s := fun s => RingHom.congr_fun hθ s
  have hcc : ∀ c, constantCoeff (ι c) = constantCoeff c := fun c => by
    obtain ⟨u, hu⟩ := TraceJacobian.exists_eq_C_add_sum c
    conv_lhs => rw [hu]
    simp [hιC, hιX, h0]
  refine TraceJacobian.dvd_trace_of_ringHom θ (ι : MvPowerSeries σ V →+* _) hθC
    (fun s => ⟨_, hθm s⟩) (fun i => MvPowerSeries.map C (φ i) - C (X i))
    (fun i => by simp [hθm, hθC, hιX])
    ((residue _).comp ((C : V →+* MvPowerSeries σ V).comp constantCoeff)) (fun s => ?_)
    (fun a ha hdet => ?_) (C δ) U ?_ b (by simpa only [← hι, RingHom.coe_coe] using hb) g M
    (by simpa only [← hι, RingHom.coe_coe] using hg)
  · obtain ⟨u, hu⟩ := TraceJacobian.exists_eq_C_add_sum s
    have : constantCoeff (θ s) = constantCoeff (constantCoeff s) := by
      conv_lhs => rw [hu]
      simp [hθC, hθX, hcc]
    simp only [RingHom.comp_apply, this]
    rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff,
      PlaceInt.mem_maximalIdeal_mvPowerSeries_iff]
    simp
  · obtain ⟨N, hN⟩ := hM
    let red : MvPowerSeries σ V →+* MvPowerSeries σ (ResidueField V) :=
      MvPowerSeries.map (residue V)
    refine TraceJacobian.det_notMem_span (ResidueField V) σ N (fun j => red (φ j))
      (red.mapMatrix a) (fun i => ?_)
      (fun i => hN (Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_range_self i)) N)) ?_
    · have h1 := ha i
      simp only [map_sub, constantCoeff_map, h0, map_zero, constantCoeff_C, zero_sub, map_neg,
        RingHom.coe_coe, hιX, hθX, mul_neg, Finset.sum_neg_distrib, neg_inj] at h1
      rw [h1]
      simp [red]
    · rw [← RingHom.map_det]
      refine Ideal.mem_comap.1
        ((Ideal.map_le_iff_le_comap (K := Ideal.comap red _)).2 (fun c hc => ?_) hdet)
      obtain ⟨u, hu⟩ := TraceJacobian.exists_eq_C_add_sum c
      rw [PlaceInt.mem_maximalIdeal_mvPowerSeries_iff, ← residue_eq_zero_iff] at hc
      rw [Ideal.mem_comap, Ideal.mem_comap, hu]
      simp only [RingHom.coe_coe, map_add, map_sum, map_mul, hιC, hιX]
      refine add_mem ?_ (Ideal.sum_mem _ fun j _ =>
        Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨j, rfl⟩))
      simp [red, hc]
  · rw [RingHom.coe_coe, hιC, ← hJ, RingHom.map_det]
    congr 1
    ext i j : 2
    have : pderiv _ j (MvPowerSeries.map (C : V →+* MvPowerSeries σ V) (φ i) - C (X i))
        = MvPowerSeries.map C (pderiv V j (φ i)) := by
      ext m : 1
      simp [coeff_pderiv, coeff_C]
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply]
    rw [this, hθm]

end GlobalTheory
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constant_dvd_trace_of_jacobian_finite_colength : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [CharZero V] (σ : Type) [Fintype σ] [DecidableEq σ] (φ : σ → MvPowerSeries σ V), (∀ j, MvPowerSeries.constantCoeff (φ j) = 0) → (∃ M : ℕ, Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ (ResidueField V))) ^ M ≤ Ideal.span (Set.range fun j => MvPowerSeries.map (residue V) (φ j))) → ∀ (δ : V) (U : (MvPowerSeries σ V)ˣ), δ ≠ 0 → Matrix.det (Matrix.of fun i j : σ => MvPowerSeries.pderiv V j (φ i)) = MvPowerSeries.C δ * (U : MvPowerSeries σ V) → ∀ (r : ℕ) (b : Fin r → MvPowerSeries σ V), (∀ f, ∃! cf : Fin r → MvPowerSeries σ V, f = ∑ i, MvPowerSeries.subst φ (cf i) * b i) → ∀ (f : MvPowerSeries σ V) (M : Matrix (Fin r) (Fin r) (MvPowerSeries σ V)), (∀ j, f * b j = ∑ i, MvPowerSeries.subst φ (M i j) * b i) → MvPowerSeries.C δ ∣ M.trace := by
  atlas_forward_decl GlobalTheory.C_dvd_trace_of_jacobian
end

section
namespace GlobalTheory.SmoothEvaluation

theorem main : ∀ {A R : Type} [inst : CommRing A] [inst_1 : CommRing R] [inst_2 : Algebra A R] {r : ℕ} (b : Fin r → R), (∀ (f : R), ∃! cf : Fin r → A, f = ∑ i : Fin r, (Algebra.algebraMap A R : A → R) (cf i) * b i) → ∃ (e : Module.Basis (Fin r) A R), ∀ (i : Fin r), (e : Fin r → R) i = b i := by
  intro A R _ _ _ r b h
  have hli : LinearIndependent A b := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    obtain ⟨c, _, hc⟩ := h 0
    have h1 := hc g (by simp only [Algebra.smul_def] at hg; exact hg.symm)
    have h2 := hc 0 (by simp)
    intro i
    rw [h1, ← h2]
    rfl
  have hsp : ⊤ ≤ Submodule.span A (Set.range b) := by
    intro f _
    obtain ⟨c, hc, _⟩ := h f
    rw [hc]
    refine Submodule.sum_mem _ (fun i _ => ?_)
    rw [← Algebra.smul_def]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  exact ⟨Module.Basis.mk hli hsp, fun i => Module.Basis.mk_apply hli hsp i⟩

end GlobalTheory.SmoothEvaluation
end

section
section
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
namespace GlobalTheory.PlaceInt.KerTrace

theorem exists_basis {A R : Type} [CommRing A] [CommRing R] [Algebra A R] {r : ℕ} (b : Fin r → R)
    (h : ∀ f, ∃! cf : Fin r → A, f = ∑ i, algebraMap A R (cf i) * b i) :
    ∃ e : Module.Basis (Fin r) A R, ∀ i, e i = b i := by
  first
  | exact @_root_.GlobalTheory.SmoothEvaluation.main
  | exact _root_.GlobalTheory.SmoothEvaluation.main
  | (apply _root_.GlobalTheory.SmoothEvaluation.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.SmoothEvaluation.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SmoothEvaluation.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SmoothEvaluation.main ..)

theorem sum_tower {A₀ A₁ R : Type} [CommRing A₀] [IsDomain A₀] [CommRing A₁] [IsDomain A₁] [CommRing R] [IsDomain R]
    (φ : A₀ →+* A₁) (ψ : A₁ →+* R) {r r' r'' : ℕ} (b : Fin r → A₁) (b' : Fin r' → R) (b'' : Fin r'' → R)
    (h : ∀ f, ∃! cf : Fin r → A₀, f = ∑ i, φ (cf i) * b i)
    (h' : ∀ f, ∃! cf : Fin r' → A₁, f = ∑ i, ψ (cf i) * b' i)
    (h'' : ∀ f, ∃! cf : Fin r'' → A₀, f = ∑ i, ψ (φ (cf i)) * b'' i)
    {J : Type} (S : Finset J) (hS : S.card = r'') (g : J → R → R)
    (hg : ∀ α ∈ S, ∃ χ : R →+* R, ∀ f, g α f = χ f) (hfix : ∀ α ∈ S, ∀ a, g α (ψ (φ a)) = ψ (φ a))
    (hinj : ∀ α ∈ S, ∀ β ∈ S, (∀ f, g α f = g β f) → α = β)
    (x : A₁) (M : Matrix (Fin r) (Fin r) A₀) (hM : ∀ j, x * b j = ∑ i, φ (M i j) * b i) :
    ∑ α ∈ S, g α (ψ x) = ψ (φ ((r' : A₀) * M.trace)) := by
  classical
  letI := φ.toAlgebra
  letI := ψ.toAlgebra
  letI := (ψ.comp φ).toAlgebra
  haveI : IsScalarTower A₀ A₁ R := IsScalarTower.of_algebraMap_eq fun _ => rfl
  obtain ⟨e, he⟩ := exists_basis (A := A₀) b h
  obtain ⟨e', -⟩ := exists_basis (A := A₁) b' h'
  obtain ⟨e'', -⟩ := exists_basis (A := A₀) b'' h''
  haveI := Module.Free.of_basis e
  haveI := Module.Free.of_basis e'
  haveI := Module.Free.of_basis e''
  haveI := Module.Finite.of_basis e
  haveI := Module.Finite.of_basis e'
  haveI := Module.Finite.of_basis e''
  choose χ hχ using hg
  let G : S → (R →ₐ[A₀] R) := fun α =>
    { χ α.1 α.2 with commutes' := fun a => (hχ α.1 α.2 _).symm.trans (hfix α.1 α.2 a) }
  have hG : ∀ α f, G α f = g α.1 f := fun α f => (hχ α.1 α.2 f).symm
  have hGi : Function.Injective G := by
    intro α β hab
    exact Subtype.ext (hinj _ α.2 _ β.2 fun f => by rw [← hG, ← hG, hab])
  have hcard : (Finset.univ.map ⟨G, hGi⟩).card = Module.finrank A₀ R := by
    rw [Finset.card_map, Module.finrank_eq_card_basis e'']
    simp [hS]
  have key := (GlobalTheory.T.invariants_and_trace_finite_free_domain_endomorphisms A₀ R _ hcard).2 (ψ x)
  rw [Finset.sum_map] at key
  have h1 : ∑ α ∈ S, g α (ψ x) = ∑ α : S, G α (ψ x) := by
    simp only [hG]
    exact (Finset.sum_coe_sort S fun α => g α (ψ x)).symm
  have h2 : Algebra.trace A₀ A₁ x = M.trace := by
    rw [Algebra.trace_eq_matrix_trace e]
    congr 1
    ext i j
    rw [Algebra.leftMulMatrix_eq_repr_mul, he, hM]
    have : ∑ i, φ (M i j) * b i = ∑ i, M i j • e i := Finset.sum_congr rfl fun i _ => by
      rw [he, Algebra.smul_def]; rfl
    rw [this, e.repr_sum_self]
  have h3 : Algebra.trace A₀ R (ψ x) = (r' : A₀) * M.trace := by
    rw [← Algebra.trace_trace (S := A₁), show ψ x = algebraMap A₁ R x from rfl, Algebra.trace_algebraMap,
      Module.finrank_eq_card_basis e', Fintype.card_fin, map_nsmul, h2, nsmul_eq_mul]
  rw [h1, ← h3]
  exact key.symm

theorem coeff_one_subst {k σ τ : Type} [CommRing k] [Fintype σ] {a : σ → MvPowerSeries τ k}
    (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) (f : MvPowerSeries σ k) (t : τ) :
    MvPowerSeries.coeff (Finsupp.single t 1) (MvPowerSeries.subst a f) =
      ∑ s, MvPowerSeries.coeff (Finsupp.single s 1) f * MvPowerSeries.coeff (Finsupp.single t 1) (a s) := by
  have h0 : ∀ {ρ : Type} (u : ρ) (g : MvPowerSeries ρ k), MvPowerSeries.constantCoeff (MvPowerSeries.pderiv k u g) =
      MvPowerSeries.coeff (Finsupp.single u 1) g := by
    intro ρ u g
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_pderiv]
    simp
  have h1 : ∀ g : MvPowerSeries σ k, MvPowerSeries.constantCoeff (MvPowerSeries.subst a g) =
      MvPowerSeries.constantCoeff g := by
    intro g
    rw [MvPowerSeries.constantCoeff_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero ha),
      finsum_eq_single _ 0]
    · simp
    · intro e he
      obtain ⟨s, hs⟩ := Finsupp.support_nonempty_iff.2 he
      rw [Finsupp.prod, map_prod, Finset.prod_eq_zero hs, smul_zero]
      rw [map_pow, ha, zero_pow (Finsupp.mem_support_iff.1 hs)]
  rw [← h0, ReciprocityTheory.ChartRestriction.G.TB.LogPf.pderiv_subst ha, map_sum]
  simp only [map_mul, h1, h0]

theorem map_subst_eq_zero {k σ τ Ω : Type} [CommRing k] [CommRing Ω] [Algebra k Ω] [Fintype σ]
    {a : σ → MvPowerSeries τ k} (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) (χ : MvPowerSeries τ k →ₐ[k] Ω)
    (hχ : ∀ s, χ (a s) = 0) {g : MvPowerSeries σ k} (hg : MvPowerSeries.constantCoeff g = 0) :
    χ (MvPowerSeries.subst a g) = 0 := by
  have hs := MvPowerSeries.hasSubst_of_constantCoeff_zero ha
  have h1 := GlobalTheory.SocleDet.mem_span_X_of_coeff (Finset.univ : Finset σ) g fun m hm => by
    have : m = 0 := Finsupp.ext fun j => hm j (Finset.mem_univ j)
    rw [this]; exact hg
  have h2 : Ideal.span ((fun i => (MvPowerSeries.X i : MvPowerSeries σ k)) '' (Finset.univ : Finset σ)) ≤
      RingHom.ker (χ.comp (MvPowerSeries.substAlgHom hs)) := by
    rw [Ideal.span_le]
    rintro _ ⟨i, -, rfl⟩
    simp [RingHom.mem_ker, MvPowerSeries.subst_X hs, hχ]
  have h3 := h2 h1
  rw [RingHom.mem_ker, AlgHom.comp_apply, MvPowerSeries.substAlgHom_apply] at h3
  exact h3

theorem left_inv_of_right {O : Type} [CommRing O] [IsDomain O] {n : ℕ} (p q s : Matrix (Fin n) (Fin n) O) (c : O)
    (hc : c ≠ 0) (h1 : s * (p * q) = c • (1 : Matrix (Fin n) (Fin n) O))
    (h2 : (p * q) * s = c • (1 : Matrix (Fin n) (Fin n) O)) : (q * s) * p = c • (1 : Matrix (Fin n) (Fin n) O) := by
  have hd : q.det ≠ 0 := by
    intro h
    have := congrArg Matrix.det h1
    rw [Matrix.det_mul, Matrix.det_mul, h, Matrix.det_smul, Matrix.det_one] at this
    exact pow_ne_zero _ hc (by simpa using this.symm)
  have h3 : (q * s * p - c • (1 : Matrix (Fin n) (Fin n) O)) * q = 0 := by
    rw [sub_mul, _root_.mul_assoc, _root_.mul_assoc, h1]; simp
  have h4 : q.det • (q * s * p - c • (1 : Matrix (Fin n) (Fin n) O)) = 0 := by
    have := congrArg (· * q.adjugate) h3
    simpa only [_root_.mul_assoc, Matrix.mul_adjugate, Matrix.mul_smul, _root_.mul_one, zero_mul] using this
  exact sub_eq_zero.1 ((smul_eq_zero.1 h4).resolve_left hd)

section
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [CharZero V]
  {d : ℕ} {O : Type} [CommRing O] [StarRing O] (B : FB V d O) {n : ℕ}

abbrev crd (p : Matrix (Fin n) (Fin n) O) : Fin n × Fin d → PS V n d :=
  fun s => matV B p (fun j => pt V (n := n) d j) s.1 s.2

omit [IsAdicComplete (maximalIdeal V) V] [CharZero V] in
theorem pt_small (b : Fin n) (i : Fin d) : MvPowerSeries.constantCoeff (pt V (n := n) d b i) ∈ maximalIdeal V := by
  simp [pt]

theorem crd_const (p : Matrix (Fin n) (Fin n) O) (s : Fin n × Fin d) : MvPowerSeries.constantCoeff (crd B p s) = 0 :=
  (GlobalTheory.T.formalModuleMatrixApplyPoints_action_laws V d O B n n p p _ _ pt_small pt_small).2.2.2.2.2.1 s.1 s.2

theorem pullM_eq (p : Matrix (Fin n) (Fin n) O) (f : PS V n d) : pullM B p f = MvPowerSeries.subst (crd B p) f :=
  (GlobalTheory.T.mvPowerSeriesSubstConstTerms_local_algHom_spec V _ _ Unit (crd B p) fun j => by rw [crd_const]; exact zero_mem _).2.2.1 (crd_const B p) f

theorem crd_mul (p q : Matrix (Fin n) (Fin n) O) (s : Fin n × Fin d) :
    crd B (p * q) s = MvPowerSeries.subst (crd B q) (crd B p s) := by
  have h1 := (GlobalTheory.T.formalModuleMatrixApplyPoints_action_laws V d O B n n p q _ _ pt_small pt_small).2.1
  have hq : ∀ b i, MvPowerSeries.constantCoeff (matV B q (fun j => pt V (n := n) d j) b i) ∈ maximalIdeal V :=
    fun b i => by rw [crd_const B q (b, i)]; exact zero_mem _
  have h2 := (GlobalTheory.T.formalModuleMatrixApplyPoints_action_laws V d O B n n p q _ _ hq hq).2.2.2.2.1 s.1 s.2
  rw [← pullM_eq]
  exact (congrFun (congrFun h1 s.1) s.2).trans h2.symm

theorem jacM_mul (p q : Matrix (Fin n) (Fin n) O) : jacM B (p * q) = jacM B p * jacM B q := by
  unfold jacM
  rw [← Matrix.det_mul]
  congr 1
  ext s t
  rw [Matrix.mul_apply]
  exact (congrArg _ (crd_mul B p q s)).trans (coeff_one_subst (crd_const B q) _ t)

theorem splitKer_right (p q : Matrix (Fin n) (Fin n) O) (h : SplitKer B (p * q)) : SplitKer B q := by
  intro Ω _ _ hi χ hχ
  refine h Ω hi χ fun b i => ?_
  exact (congrArg χ (crd_mul B p q (b, i))).trans
    (map_subst_eq_zero (crd_const B q) χ (fun s => hχ s.1 s.2) (crd_const B p _))

def pullHom (p : Matrix (Fin n) (Fin n) O) : PS V n d →ₐ[V] PS V n d :=
  MvPowerSeries.substAlgHom (MvPowerSeries.hasSubst_of_constantCoeff_zero (crd_const B p))

theorem pullHom_apply (p : Matrix (Fin n) (Fin n) O) (f : PS V n d) :
    pullHom B p f = MvPowerSeries.subst (crd B p) f := MvPowerSeries.substAlgHom_apply _ _

theorem pullHom_mul (p q : Matrix (Fin n) (Fin n) O) (f : PS V n d) :
    pullHom B q (pullHom B p f) = pullM B (p * q) f := by
  rw [(GlobalTheory.T.formalModuleMatrixApplyPoints_action_laws V d O B n n p q _ _ pt_small pt_small).2.2.2.2.2.2 f, pullM_eq, pullM_eq, pullHom_apply,
    pullHom_apply]

end

theorem sum_shift_kerM_mul : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [CharZero V] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB V d O), FinHt B → ∀ (n : ℕ) (p q s : Matrix (Fin n) (Fin n) O) (N : ℕ), 1 ≤ N → s * (p * q) = (N : O) • (1 : Matrix (Fin n) (Fin n) O) → (p * q) * s = (N : O) • (1 : Matrix (Fin n) (Fin n) O) → IsDomain O → (N : O) ≠ 0 → jacM B (p * q) ≠ 0 → SplitKer B (p * q) → ∀ f : PS V n d, (∀ α ∈ kerM B q, shift B.G.F α f = f) → (kerM B (p * q)).Finite ∧ ∃ g : PS V n d, ∑ᶠ α ∈ kerM B (p * q), shift B.G.F α f = MvPowerSeries.C (((kerM B q).ncard : V) * jacM B p) * pullM B (p * q) g := by
  intro V _ _ _ _ _ d O _ _ B hB n p q s N hN h1 h2 hO hN0 hj hsp f hf
  have hq : (s * p) * q = (N : O) • (1 : Matrix (Fin n) (Fin n) O) := by rw [_root_.mul_assoc, h1]
  have hp := left_inv_of_right p q s _ hN0 h1 h2
  have hjm := jacM_mul B p q
  have hjp : jacM B p ≠ 0 := fun h => hj (by rw [hjm, h, zero_mul])
  have hjq : jacM B q ≠ 0 := fun h => hj (by rw [hjm, h, mul_zero])
  have hsq := splitKer_right B p q hsp
  obtain ⟨f', rfl⟩ := GlobalTheory.T.formalSeries_descends_of_splitKernel_invariant V d O B hB n q _ N hN hq hjq hsq f hf
  obtain ⟨hfin, hcard⟩ := GlobalTheory.T.formalMatrixKernel_finite_ncard_eq_rank V d O B hB n (p * q) s N hN h1 hj hsp
  obtain ⟨-, hcardq⟩ := GlobalTheory.T.formalMatrixKernel_finite_ncard_eq_rank V d O B hB n q _ N hN hq hjq hsq
  have cp := GlobalTheory.T.exists_pow_span_X_le_span_formalModuleMatrix V d O B hB n p _ N hN hp
  obtain ⟨r, b, -, hb⟩ := GlobalTheory.T.exists_finite_basis_powerSeries_subst_finite_colength V _ (crd B p) (crd_const B p) cp
  obtain ⟨r', b', hr', hb'⟩ := GlobalTheory.T.exists_finite_basis_powerSeries_subst_finite_colength V _ (crd B q) (crd_const B q) (GlobalTheory.T.exists_pow_span_X_le_span_formalModuleMatrix V d O B hB n q _ N hN hq)
  obtain ⟨r'', b'', hr'', hb''⟩ := GlobalTheory.T.exists_finite_basis_powerSeries_subst_finite_colength V _ (crd B (p * q)) (crd_const B _)
    (GlobalTheory.T.exists_pow_span_X_le_span_formalModuleMatrix V d O B hB n _ s N hN h1)
  refine ⟨hfin, ?_⟩
  choose M hM using fun j => (hb (f' * b j)).exists
  obtain ⟨U, hU⟩ := GlobalTheory.T.det_jacobian_formal_module_matrix_eq_const_mul_unit V d O B n p
  obtain ⟨g, hg⟩ := GlobalTheory.T.constant_dvd_trace_of_jacobian_finite_colength V _ (crd B p) (crd_const B p) cp _ U hjp hU r b hb f' (Matrix.of fun i j => M j i) hM
  refine ⟨g, ?_⟩
  haveI : IsDomain (PS V n d) := NoZeroDivisors.to_isDomain _
  have hsm : ∀ α ∈ hfin.toFinset, ∀ b, Small (α b) := fun α hα => (hfin.mem_toFinset.1 hα).1
  have hsh := (GlobalTheory.T.formalGroupTranslate_automorphism_and_matrixKernel V d O B n (p * q)).2.2
  have key := sum_tower (pullHom B p : PS V n d →+* PS V n d) (pullHom B q : PS V n d →+* PS V n d) b b' b''
    (by simpa only [RingHom.coe_coe, pullHom_apply] using hb)
    (by simpa only [RingHom.coe_coe, pullHom_apply] using hb')
    (by simpa only [RingHom.coe_coe, pullHom_mul, pullM_eq] using hb'')
    hfin.toFinset (by rw [← Set.ncard_eq_toFinset_card _ hfin, hcard]; exact hr'') (shift B.G.F)
    (fun α hα => by
      obtain ⟨ψ, hψ⟩ := (hsh α α (hsm α hα) (hsm α hα)).1
      exact ⟨(ψ : PS V n d →+* PS V n d), hψ⟩)
    (fun α hα a => by
      simp only [RingHom.coe_coe, pullHom_mul]
      exact (hsh α α (hsm α hα) (hsm α hα)).2.1.1 (hfin.mem_toFinset.1 hα) a)
    (fun α hα β hβ => (hsh α β (hsm α hα) (hsm β hβ)).2.2.1)
    f' (Matrix.of fun i j => M j i) (by simpa only [RingHom.coe_coe, pullHom_apply, Matrix.of_apply] using hM)
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, pullM_eq B q, ← pullHom_apply]
  refine key.trans ?_
  have hC : ∀ (m : Matrix (Fin n) (Fin n) O) (c : V), pullHom B m (MvPowerSeries.C c) = MvPowerSeries.C c :=
    fun m c => (pullHom B m).commutes c
  rw [hg, hcardq.trans hr', ← pullHom_mul]
  simp only [RingHom.coe_coe, map_mul, map_natCast, hC, _root_.mul_assoc]

end GlobalTheory.PlaceInt.KerTrace
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacobian_nonzero_splitting_of_product : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [CharZero V] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB V d O), FinHt B → ∀ (n : ℕ) (p q s : Matrix (Fin n) (Fin n) O) (N : ℕ), 1 ≤ N → s * (p * q) = (N : O) • (1 : Matrix (Fin n) (Fin n) O) → (p * q) * s = (N : O) • (1 : Matrix (Fin n) (Fin n) O) → IsDomain O → (N : O) ≠ 0 → jacM B (p * q) ≠ 0 → SplitKer B (p * q) → ∀ f : PS V n d, (∀ α ∈ kerM B q, shift B.G.F α f = f) → (kerM B (p * q)).Finite ∧ ∃ g : PS V n d, ∑ᶠ α ∈ kerM B (p * q), shift B.G.F α f = MvPowerSeries.C (((kerM B q).ncard : V) * jacM B p) * pullM B (p * q) g := by
  atlas_forward_decl GlobalTheory.PlaceInt.KerTrace.sum_shift_kerM_mul
end
