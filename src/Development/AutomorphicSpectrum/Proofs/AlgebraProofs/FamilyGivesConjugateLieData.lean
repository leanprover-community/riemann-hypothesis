import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DualLatticeDegreeNeg
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FrobeniusLatticeDegreeMulP
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.FormalGroupActionLinearPartRingHom
import BuildAid.ForwardExisting
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FormalHermitianActionPairing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.ConstantCoeffEv
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FormalBilinearTermProduct
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PowerSeriesPowPFrobenius
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.MultiplicationByPFactorsFrobenius
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PowOneSeriesPFormula
import Development.WeilBound.CoreStatements.HodgeTatePoints.FirstPowerZeroAt
import Development.WeilBound.CoreStatements.HodgeTatePoints.CbAlpha
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FormalDataBaseChange
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FormalIsomorphismTransport
import Development.WeilBound.CoreStatements.HodgeTatePoints.GermCompOneAssocOfConstantCoeffZero
import Development.WeilBound.CoreStatements.HodgeTatePoints.CgSplit

section
section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

namespace GlobalTheory.CompanionTheory.Ar.Conj

theorem rho_hom : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB R d O), ∃ ρ : O →+* Matrix (Fin d) (Fin d) R, ∀ a, ρ a = rho B a := by
  intro R _ d O _ _ B
  obtain ⟨ρ, h⟩ := GlobalTheory.ChF.linPart_act_ringHom R d B.G O B.A R (RingHom.id R)
  refine ⟨ρ, fun a => ?_⟩
  rw [(h a).2]
  ext i j
  rfl

end GlobalTheory.CompanionTheory.Ar.Conj
end

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formal_group_action_ring_hom : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB R d O), ∃ ρ : O →+* Matrix (Fin d) (Fin d) R, ∀ a, ρ a = rho B a := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Conj.rho_hom
end

section
section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

namespace GlobalTheory.CompanionTheory.Ar.Conj

theorem pow_sy_exchange : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB R d O) (n : ℕ), pow2 B n * B.sy ^ n = ev (n := 2) ![pt R d 0, comp1 (B.A.act (n : O)) (pt R d 1)] B.sy * ev (n := 2) ![pt R d 1, pt R d 0] (pow1 B n) :=
  @PositivityTheory.HtPt.Cc.pow_sy

end GlobalTheory.CompanionTheory.Ar.Conj
end

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pow_two_symplectic_relation : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB R d O) (n : ℕ), pow2 B n * B.sy ^ n = ev (n := 2) ![pt R d 0, comp1 (B.A.act (n : O)) (pt R d 1)] B.sy * ev (n := 2) ![pt R d 1, pt R d 0] (pow1 B n) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Conj.pow_sy_exchange
end

section
section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

namespace GlobalTheory.CompanionTheory.Ar.Conj

theorem pow_interchange : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB R d O) (m n : ℕ), pow2 B n ^ m * ev (n := 2) ![pt R d 0, comp1 (B.A.act (n : O)) (pt R d 1)] (pow1 B m) = pow1 B m ^ n * ev (n := 2) ![comp1 (B.A.act (m : O)) (pt R d 0), pt R d 1] (pow2 B n) :=
  PositivityTheory.HtPt.Cc.pow_inter

end GlobalTheory.CompanionTheory.Ar.Conj
end

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pow_one_pow_two_commutation : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB R d O) (m n : ℕ), pow2 B n ^ m * ev (n := 2) ![pt R d 0, comp1 (B.A.act (n : O)) (pt R d 1)] (pow1 B m) = pow1 B m ^ n * ev (n := 2) ![comp1 (B.A.act (m : O)) (pt R d 0), pt R d 1] (pow2 B n) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Conj.pow_interchange
end

section
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Conj.Isotropy

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB.LogPf GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

variable {R : Type} [CommRing R] {d : ℕ}

local notation "P₀" => pt R (n := 2) d 0
local notation "P₁" => pt R (n := 2) d 1

theorem cz_pair {n : ℕ} {a b : Pt R n d} (ha : ∀ i, constantCoeff (a i) = 0)
    (hb : ∀ i, constantCoeff (b i) = 0) : CZ ![a, b] := by
  intro j i
  fin_cases j
  · exact ha i
  · exact hb i

theorem cz_single {n : ℕ} {a : Pt R n d} (ha : ∀ i, constantCoeff (a i) = 0) : CZ ![a] := by
  intro j i
  fin_cases j
  exact ha i

theorem pt_noConst {n : ℕ} (j : Fin n) (i : Fin d) : constantCoeff (pt R d j i) = 0 := by
  simp [pt]

theorem ptPow_noConst {n p : ℕ} (hp : p ≠ 0) (j : Fin n) (i : Fin d) :
    constantCoeff (ptPow R d p j i) = 0 := by
  simp [ptPow, hp]

theorem composition_no_constant_term {V : Pt R 1 d} (hV : ∀ i, constantCoeff (V i) = 0) {n : ℕ} {a : Pt R n d}
    (ha : ∀ i, constantCoeff (a i) = 0) (i : Fin d) : constantCoeff (comp1 V a i) = 0 :=
  constantCoeff_ev (cz_single ha) (hV i)

theorem ev_pow_eq {m n : ℕ} {a : Fin m → Pt R n d} (ha : CZ a) (f : PS R m d) (k : ℕ) :
    ev a (f ^ k) = ev a f ^ k := by
  simp only [← evHom_apply ha, map_pow]

theorem ev_pair_ev {n : ℕ} {a b : Pt R n d} (ha : ∀ i, constantCoeff (a i) = 0)
    (hb : ∀ i, constantCoeff (b i) = 0) {u v : Pt R 2 d} (hu : ∀ i, constantCoeff (u i) = 0)
    (hv : ∀ i, constantCoeff (v i) = 0) (f : PS R 2 d) :
    ev ![a, b] (ev ![u, v] f) = ev ![fun i => ev ![a, b] (u i), fun i => ev ![a, b] (v i)] f := by
  rw [ev_ev (cz_pair ha hb) (cz_pair hu hv)]
  congr 1
  funext j i
  fin_cases j <;> rfl

theorem ev_first {n : ℕ} {a b : Pt R n d} (ha : ∀ i, constantCoeff (a i) = 0)
    (hb : ∀ i, constantCoeff (b i) = 0) : (fun i => ev ![a, b] (P₀ i)) = a :=
  funext fun i => ev_X (cz_pair ha hb) 0 i

theorem ev_second {n : ℕ} {a b : Pt R n d} (ha : ∀ i, constantCoeff (a i) = 0)
    (hb : ∀ i, constantCoeff (b i) = 0) : (fun i => ev ![a, b] (P₁ i)) = b :=
  funext fun i => ev_X (cz_pair ha hb) 1 i

theorem ev_first_pow {n : ℕ} (p : ℕ) {a b : Pt R n d} (ha : ∀ i, constantCoeff (a i) = 0)
    (hb : ∀ i, constantCoeff (b i) = 0) :
    (fun i => ev ![a, b] (ptPow R d p 0 i)) = fun i => a i ^ p :=
  funext fun i => by
    simp only [ptPow]
    rw [ev_pow_eq (cz_pair ha hb), ev_X (cz_pair ha hb)]
    rfl

theorem ev_second_pow {n : ℕ} (p : ℕ) {a b : Pt R n d} (ha : ∀ i, constantCoeff (a i) = 0)
    (hb : ∀ i, constantCoeff (b i) = 0) :
    (fun i => ev ![a, b] (ptPow R d p 1 i)) = fun i => b i ^ p :=
  funext fun i => by
    simp only [ptPow]
    rw [ev_pow_eq (cz_pair ha hb), ev_X (cz_pair ha hb)]
    rfl

theorem pt_pow_eq {n : ℕ} (p : ℕ) (j : Fin n) : (fun i => pt R (n := n) d j i ^ p) = ptPow R d p j := rfl

theorem ev_comp1_pair {V : Pt R 1 d} (hV : ∀ i, constantCoeff (V i) = 0) {m n : ℕ}
    {a : Fin m → Pt R n d} (ha : CZ a) {b : Pt R m d} (hb : ∀ i, constantCoeff (b i) = 0) :
    (fun i => ev a (comp1 V b i)) = comp1 V (fun i => ev a (b i)) := by
  funext i
  simp only [comp1]
  rw [ev_ev ha (cz_single hb)]
  congr 1
  funext j l
  fin_cases j
  rfl

theorem composition_frobenius_point {p n : ℕ} {a : Pt R n d} (ha : ∀ i, constantCoeff (a i) = 0) :
    comp1 (ptPow R d p 0) a = fun i => a i ^ p := by
  funext i
  simp only [comp1, ptPow]
  rw [ev_pow_eq (cz_single ha), ev_X (cz_single ha)]
  rfl

theorem composition_assoc_frobenius_point {V : Pt R 1 d} {p n : ℕ} (hp : p ≠ 0) {a : Pt R n d}
    (ha : ∀ i, constantCoeff (a i) = 0) :
    comp1 (comp1 V (ptPow R d p 0)) a = comp1 V (fun i => a i ^ p) := by
  funext i
  simp only [comp1]
  rw [ev_ev (cz_single ha) (cz_single (ptPow_noConst hp 0))]
  congr 1
  funext j l
  fin_cases j
  exact congrFun (composition_frobenius_point ha) l

theorem lin_tau {p : ℕ} (hp : p ≠ 1) : lin (ptPow R d p 0 : Pt R 1 d) 1 = 0 := by
  ext i j
  simp only [lin, ptPow, Matrix.zero_apply]
  rw [coeff_X_pow, if_neg]
  intro h
  rcases (Finsupp.single_eq_single_iff _ _ _ _).1 h with ⟨_, h⟩ | ⟨h, _⟩
  · exact hp h.symm
  · exact one_ne_zero h

theorem calc_cmp {f : PS R 2 d} (hf : AxOne f) {φ ψ : Pt R 1 d} (hφ : ∀ i, constantCoeff (φ i) = 0)
    (hψ : ∀ i, constantCoeff (ψ i) = 0) :
    AxOne (ev (n := 2) ![comp1 φ P₀, comp1 ψ P₁] f) ∧
      bil (ev (n := 2) ![comp1 φ P₀, comp1 ψ P₁] f) 1 1 = (lin φ 1).transpose * bil f 1 1 * lin ψ 1 :=
  have t := GlobalTheory.T.formal_bilinear_term_product R d f f φ ψ hf hf hφ hψ
  ⟨t.2.2.2.1, t.2.2.2.2.1⟩

theorem comp1_identity_left {n : ℕ} (j : Fin n) : comp1 (pt R d 0) (pt R (n := n) d j) = pt R d j :=
  germ_comp1_zero_point_left _ (pt_noConst j)

theorem calc_right {f : PS R 2 d} (hf : AxOne f) {p : ℕ} (hp0 : p ≠ 0) (hp : p ≠ 1) :
    AxOne (ev (n := 2) ![P₀, ptPow R d p 1] f) ∧ bil (ev (n := 2) ![P₀, ptPow R d p 1] f) 1 1 = 0 := by
  have t := calc_cmp hf (φ := pt R d 0) (ψ := ptPow R d p 0) (pt_noConst 0) (ptPow_noConst hp0 0)
  rw [comp1_identity_left, composition_frobenius_point (pt_noConst 1), pt_pow_eq, lin_tau hp, Matrix.mul_zero] at t
  exact t

theorem calc_left {f : PS R 2 d} (hf : AxOne f) {p : ℕ} (hp0 : p ≠ 0) (hp : p ≠ 1) :
    AxOne (ev (n := 2) ![ptPow R d p 0, P₁] f) ∧ bil (ev (n := 2) ![ptPow R d p 0, P₁] f) 1 1 = 0 := by
  have t := calc_cmp hf (φ := ptPow R d p 0) (ψ := pt R d 0) (ptPow_noConst hp0 0) (pt_noConst 0)
  rw [comp1_identity_left, composition_frobenius_point (pt_noConst 0), pt_pow_eq, lin_tau hp, Matrix.transpose_zero,
    Matrix.zero_mul, Matrix.zero_mul] at t
  exact t

theorem calc_map_right {f : PS R 2 d} (hf : AxOne f) {V : Pt R 1 d} (hV : ∀ i, constantCoeff (V i) = 0) :
    AxOne (ev (n := 2) ![P₀, comp1 V P₁] f) ∧
      bil (ev (n := 2) ![P₀, comp1 V P₁] f) 1 1 = bil f 1 1 * lin V 1 := by
  have t := calc_cmp hf (φ := pt R d 0) (ψ := V) (pt_noConst 0) hV
  rw [comp1_identity_left, lin_pt_eq_one, Matrix.transpose_one, Matrix.one_mul] at t
  exact t

theorem calc_map_left {f : PS R 2 d} (hf : AxOne f) {V : Pt R 1 d} (hV : ∀ i, constantCoeff (V i) = 0) :
    AxOne (ev (n := 2) ![comp1 V P₀, P₁] f) ∧
      bil (ev (n := 2) ![comp1 V P₀, P₁] f) 1 1 = (lin V 1).transpose * bil f 1 1 := by
  have t := calc_cmp hf (φ := V) (ψ := pt R d 0) hV (pt_noConst 0)
  rw [comp1_identity_left, lin_pt_eq_one, Matrix.mul_one] at t
  exact t

theorem axOne_swap {f : PS R 2 d} (hf : AxOne f) : AxOne (ev (n := 2) ![P₁, P₀] f) := by
  have c0 : ∀ i, constantCoeff ((0 : Pt R 1 d) i) = 0 := fun i => by simp
  have c1 : ∀ i, constantCoeff (pt R (n := 1) d 0 i) = 0 := pt_noConst 0
  constructor
  · rw [ev_pair_ev c0 c1 (pt_noConst 1) (pt_noConst 0), ev_first c0 c1, ev_second c0 c1]
    exact hf.2
  · rw [ev_pair_ev c1 c0 (pt_noConst 1) (pt_noConst 0), ev_first c1 c0, ev_second c1 c0]
    exact hf.1

theorem axOne_map {S : Type} [CommRing S] (φ : R →+* S) {f : PS R 2 d} (hf : AxOne f) :
    AxOne (MvPowerSeries.map φ f) := by
  have key : ∀ a : Fin 2 → Pt R 1 d, CZ a → ev a f = 1 →
      ev (fun j l => MvPowerSeries.map φ (a j l)) (MvPowerSeries.map φ f) = 1 := by
    intro a ha h
    have e : MvPowerSeries.map φ (ev a f) =
        ev (fun j l => MvPowerSeries.map φ (a j l)) (MvPowerSeries.map φ f) := by
      unfold ev
      exact map_subst ha.hasSubst f
    rw [← e, h, map_one]
  have c0 : ∀ i, constantCoeff ((0 : Pt R 1 d) i) = 0 := fun i => by simp
  have c1 : ∀ i, constantCoeff (pt R (n := 1) d 0 i) = 0 := pt_noConst 0
  constructor
  · have := key _ (cz_pair c0 c1) hf.1
    convert this using 2
    funext j l
    fin_cases j
    · simp
    · simp [pt]
  · have := key _ (cz_pair c1 c0) hf.2
    convert this using 2
    funext j l
    fin_cases j
    · simp [pt]
    · simp

theorem calc_mul {f g : PS R 2 d} (hf : AxOne f) (hg : AxOne g) :
    AxOne (f * g) ∧ bil (f * g) 1 1 = bil f 1 1 + bil g 1 1 :=
  have t := GlobalTheory.T.formal_bilinear_term_product R d f g (pt R d 0) (pt R d 0) hf hg (pt_noConst 0) (pt_noConst 0)
  ⟨t.1, t.2.1 1⟩

theorem calc_swap {f : PS R 2 d} (hf : AxOne f) :
    bil (ev (n := 2) ![P₁, P₀] f) 1 1 = (bil f 1 1).transpose :=
  (GlobalTheory.T.formal_bilinear_term_product R d f f (pt R d 0) (pt R d 0) hf hf (pt_noConst 0) (pt_noConst 0)).2.2.2.2.2.1 1 1

theorem calc_pow {f : PS R 2 d} (hf : AxOne f) {p : ℕ} (hp : 1 ≤ p) :
    bil (ev (n := 2) ![ptPow R d p 0, ptPow R d p 1] f) p p = bil f 1 1 :=
  (GlobalTheory.T.formal_bilinear_term_product R d f f (pt R d 0) (pt R d 0) hf hf (pt_noConst 0) (pt_noConst 0)).2.2.2.2.2.2 p p hp hp

theorem bil_map_eq_zero {S : Type} [CommRing S] (φ : R →+* S) {f : PS R 2 d} (h : bil f 1 1 = 0) :
    bil (MvPowerSeries.map φ f) 1 1 = 0 := by
  ext i j
  have := congrFun (congrFun h i) j
  simp only [bil, coeff_map, Matrix.zero_apply] at this ⊢
  rw [this, map_zero]

variable {O : Type} [CommRing O] [StarRing O]

theorem am_mul_hw {p : ℕ} [Fact p.Prime] [CharP R p] (B : FB R d O) :
    am B p * hw B p = (hw B p).transpose * (bil B.sy 1 1 * hw B p + (am B p).transpose) := by
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hp1 : p ≠ 1 := (Fact.out : p.Prime).ne_one
  obtain ⟨V, hV, hact, hlin⟩ := GlobalTheory.T.multiplication_by_p_factors_frobenius R p d O B
  obtain ⟨g, hg, ha, hgb⟩ := GlobalTheory.T.pow_one_series_p_formula R p d O B
  have c0 : ∀ i, constantCoeff (P₀ i) = 0 := pt_noConst 0
  have c1 : ∀ i, constantCoeff (P₁ i) = 0 := pt_noConst 1
  have u0 : ∀ i, constantCoeff (ptPow R (n := 2) d p 0 i) = 0 := ptPow_noConst hp0 0
  have u1 : ∀ i, constantCoeff (ptPow R (n := 2) d p 1 i) = 0 := ptPow_noConst hp0 1
  have v0 := composition_no_constant_term hV c0
  have v1 := composition_no_constant_term hV c1
  have w0 := composition_no_constant_term hV u0
  have w1 := composition_no_constant_term hV u1
  have hA0 : comp1 (B.A.act (p : O)) P₀ = comp1 V (ptPow R d p 0) := by
    rw [hact, composition_assoc_frobenius_point hp0 c0, pt_pow_eq]
  have hA1 : comp1 (B.A.act (p : O)) P₁ = comp1 V (ptPow R d p 1) := by
    rw [hact, composition_assoc_frobenius_point hp0 c1, pt_pow_eq]
  have hsym : AxOne B.sy := ⟨B.symmetry_zero_fst, B.symmetry_zero_snd⟩
  have hfs : ∀ f : PS R 2 d, f ^ p = ev (n := 2) ![ptPow R d p 0, ptPow R d p 1]
      (MvPowerSeries.map (frobenius R p) f) := by
    intro f
    rw [GlobalTheory.T.power_series_pow_p_frobenius R p d 2 f]
    congr 1
    funext j
    fin_cases j <;> rfl

  obtain ⟨sy', hsy'⟩ : ∃ s, s = ev (n := 2) ![P₁, P₀] B.sy := ⟨_, rfl⟩
  obtain ⟨s2, hs2⟩ : ∃ s, s = ev (n := 2) ![P₀, comp1 V P₁] B.sy := ⟨_, rfl⟩
  obtain ⟨g1, hg1⟩ : ∃ s, s = ev (n := 2) ![P₁, P₀] g := ⟨_, rfl⟩
  obtain ⟨t, ht⟩ : ∃ s, s = ev (n := 2) ![ptPow R d p 0, P₁] (MvPowerSeries.map (frobenius R p) sy') :=
    ⟨_, rfl⟩
  have axs2 : AxOne s2 := hs2 ▸ (calc_map_right hsym hV).1
  have bs2 : bil s2 1 1 = bil B.sy 1 1 * hw B p := by rw [hs2, (calc_map_right hsym hV).2, hlin]
  have axg1 : AxOne g1 := hg1 ▸ axOne_swap hg
  have bg1 : bil g1 1 1 = (am B p).transpose := by rw [hg1, calc_swap hg, hgb]
  have axsy' : AxOne (MvPowerSeries.map (frobenius R p) sy') :=
    axOne_map _ (hsy' ▸ axOne_swap hsym)
  have axt : AxOne t := ht ▸ (calc_left axsy' hp0 hp1).1
  have bt : bil t 1 1 = 0 := ht ▸ (calc_left axsy' hp0 hp1).2
  obtain ⟨g', hg'⟩ : ∃ s, s = s2 * g1 * t := ⟨_, rfl⟩
  have axg' : AxOne g' := hg' ▸ (calc_mul (calc_mul axs2 axg1).1 axt).1
  have bg' : bil g' 1 1 = bil B.sy 1 1 * hw B p + (am B p).transpose := by
    rw [hg', (calc_mul (calc_mul axs2 axg1).1 axt).2, (calc_mul axs2 axg1).2, bs2, bg1, bt, add_zero]
  have cQ := cz_pair c0 u1
  have hb : pow2 B p = ev (n := 2) ![P₀, ptPow R d p 1] g' := by
    have e1 := GlobalTheory.T.pow_two_symplectic_relation R d O B p
    have f1 : ev (n := 2) ![P₀, comp1 (B.A.act (p : O)) P₁] B.sy =
        ev (n := 2) ![P₀, ptPow R d p 1] s2 := by
      rw [hA1, hs2, ev_pair_ev c0 u1 c0 v1, ev_first c0 u1, ev_comp1_pair hV cQ c1, ev_second c0 u1]
    have f2 : ev (n := 2) ![P₁, P₀] (pow1 B p) = ev (n := 2) ![P₀, ptPow R d p 1] g1 := by
      rw [ha, hg1, ev_pair_ev c1 c0 u0 c1, ev_first_pow p c1 c0, ev_second c1 c0, pt_pow_eq,
        ev_pair_ev c0 u1 c1 c0, ev_first c0 u1, ev_second c0 u1]
    have f3 : sy' ^ p = ev (n := 2) ![P₀, ptPow R d p 1] t := by
      rw [hfs, ht, ev_pair_ev c0 u1 u0 c1, ev_first_pow p c0 u1, ev_second c0 u1, pt_pow_eq]
    have f4 : B.sy ^ p * sy' ^ p = 1 := by rw [← mul_pow, hsy', B.sy_inv, one_pow]
    calc pow2 B p = pow2 B p * (B.sy ^ p * sy' ^ p) := by rw [f4, mul_one]
      _ = pow2 B p * B.sy ^ p * sy' ^ p := (mul_assoc _ _ _).symm
      _ = ev (n := 2) ![P₀, ptPow R d p 1] s2 * ev (n := 2) ![P₀, ptPow R d p 1] g1 *
          ev (n := 2) ![P₀, ptPow R d p 1] t := by rw [e1, f1, f2, f3]
      _ = ev (n := 2) ![P₀, ptPow R d p 1] g' := by rw [hg', ev_mul cQ, ev_mul cQ]

  obtain ⟨g2, hg2⟩ : ∃ s, s = ev (n := 2) ![P₀, comp1 V P₁] g := ⟨_, rfl⟩
  obtain ⟨g3, hg3⟩ : ∃ s, s = ev (n := 2) ![comp1 V P₀, P₁] g' := ⟨_, rfl⟩
  have axg2 : AxOne g2 := hg2 ▸ (calc_map_right hg hV).1
  have bg2 : bil g2 1 1 = am B p * hw B p := by rw [hg2, (calc_map_right hg hV).2, hgb, hlin]
  have axg3 : AxOne g3 := hg3 ▸ (calc_map_left axg' hV).1
  have bg3 : bil g3 1 1 = (hw B p).transpose * (bil B.sy 1 1 * hw B p + (am B p).transpose) := by
    rw [hg3, (calc_map_left axg' hV).2, hlin, bg']
  have cP := cz_pair u0 u1
  have h1 : ev (n := 2) ![P₀, comp1 (B.A.act (p : O)) P₁] (pow1 B p) =
      ev (n := 2) ![ptPow R d p 0, ptPow R d p 1] g2 := by
    rw [hA1, ha, hg2, ev_pair_ev c0 w1 u0 c1, ev_first_pow p c0 w1, ev_second c0 w1, pt_pow_eq,
      ev_pair_ev u0 u1 c0 v1, ev_first u0 u1, ev_comp1_pair hV cP c1, ev_second u0 u1]
  have h2 : ev (n := 2) ![comp1 (B.A.act (p : O)) P₀, P₁] (pow2 B p) =
      ev (n := 2) ![ptPow R d p 0, ptPow R d p 1] g3 := by
    rw [hA0, hb, hg3, ev_pair_ev w0 c1 c0 u1, ev_first w0 c1, ev_second_pow p w0 c1, pt_pow_eq,
      ev_pair_ev u0 u1 v0 c1, ev_comp1_pair hV cP c0, ev_first u0 u1, ev_second u0 u1]
  have hmain : ev (n := 2) ![ptPow R d p 0, ptPow R d p 1]
        (MvPowerSeries.map (frobenius R p) (pow2 B p) * g2) =
      ev (n := 2) ![ptPow R d p 0, ptPow R d p 1]
        (MvPowerSeries.map (frobenius R p) (pow1 B p) * g3) := by
    rw [ev_mul cP, ev_mul cP, ← hfs, ← hfs, ← h1, ← h2]
    exact GlobalTheory.T.pow_one_pow_two_commutation R d O B p p

  have axb : AxOne (pow2 B p) := hb ▸ (calc_right axg' hp0 hp1).1
  have bb : bil (pow2 B p) 1 1 = 0 := hb ▸ (calc_right axg' hp0 hp1).2
  have axa : AxOne (pow1 B p) := ha ▸ (calc_left hg hp0 hp1).1
  have ba : bil (pow1 B p) 1 1 = 0 := ha ▸ (calc_left hg hp0 hp1).2
  have axfb := axOne_map (frobenius R p) axb
  have axfa := axOne_map (frobenius R p) axa
  have hp : 1 ≤ p := Nat.one_le_iff_ne_zero.2 hp0
  have hco := congrArg (fun f => bil f p p) hmain
  rw [calc_pow (calc_mul axfb axg2).1 hp, calc_pow (calc_mul axfa axg3).1 hp, (calc_mul axfb axg2).2,
    (calc_mul axfa axg3).2, bil_map_eq_zero _ bb, bil_map_eq_zero _ ba, zero_add, zero_add, bg2, bg3] at hco
  exact hco

theorem beta_comp_alpha : ∀ (R : Type) [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p] (d : ℕ) (O : Type)
    [CommRing O] [StarRing O] (B : FB R d O),
    (∀ u y, u ⬝ᵥ beta B p y = pairH B (alpha B p u) y) ∧ beta B p ∘ₗ alpha B p = 0 := by
  intro R _ p _ _ d O _ _ B
  refine ⟨fun u y => dotProduct_beta B p u y, LinearMap.ext fun u => ?_⟩
  have h : (hw B p).transpose * (am B p).transpose - am B p * hw B p +
      (hw B p).transpose * bil B.sy 1 1 * hw B p = 0 := by
    rw [am_mul_hw, Matrix.mul_add, Matrix.mul_assoc]
    abel
  rw [LinearMap.comp_apply, beta_alpha_apply, h, Matrix.zero_mulVec]
  rfl

end GlobalTheory.CompanionTheory.Ar.Conj.Isotropy
end
end

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.alpha_beta_adjoint_exact : ∀ (R : Type) [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB R d O), (∀ u y, u ⬝ᵥ beta B p y = pairH B (alpha B p u) y) ∧ beta B p ∘ₗ alpha B p = 0 := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Conj.Isotropy.beta_comp_alpha
end

section
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Conj.AlphaAct

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

theorem alpha_comm_act : ∀ (R : Type) [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB R d O) (a : O) (u : Fin d → R), alpha B p (((rho B a).map (· ^ p)).mulVec u) = rhoH B a (alpha B p u) :=
  @PositivityTheory.HtPt.Cb.alpha_act

end GlobalTheory.CompanionTheory.Ar.Conj.AlphaAct
end
end

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.alpha_equivariant_frobenius : ∀ (R : Type) [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB R d O) (a : O) (u : Fin d → R), alpha B p (((rho B a).map (· ^ p)).mulVec u) = rhoH B a (alpha B p u) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Conj.AlphaAct.alpha_comm_act
end

section
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Conj

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv

theorem beta_rhoH_eq : ∀ (R : Type) [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p] (d : ℕ) (O : Type) [CommRing O]
    [StarRing O] (B : FB R d O) (a : O) (y : (Fin d → R) × (Fin d → R)),
    beta B p (rhoH B a y) = ((rho B (star a)).transpose.map (· ^ p)).mulVec (beta B p y) := by
  intro R _ p _ _ d O _ _ B a y
  refine dotProduct_eq _ _ fun u => ?_
  have hadj := (GlobalTheory.T.formal_hermitian_action_pairing R d O B).2.2 (star a) (alpha B p u) y
  rw [star_star] at hadj
  have htw := GlobalTheory.T.alpha_equivariant_frobenius R p d O B (star a) u
  rw [dotProduct_comm, dotProduct_beta, ← hadj, ← htw, ← dotProduct_beta, dotProduct_comm _ (beta B p y),
    Matrix.dotProduct_mulVec, Matrix.transpose_map, Matrix.mulVec_transpose]

end GlobalTheory.CompanionTheory.Ar.Conj
end
end

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.beta_equivariant_frobenius : ∀ (R : Type) [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB R d O) (a : O) (y : (Fin d → R) × (Fin d → R)), beta B p (rhoH B a y) = ((rho B (star a)).transpose.map (· ^ p)).mulVec (beta B p y) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Conj.beta_rhoH_eq
end

section
section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

namespace GlobalTheory.CompanionTheory.Ar.Conj

theorem iso_pow_one_law : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB R d O) (B₂ : FB R d O) (φ ψ : Pt R 1 d) (lam : PS R 2 d) (n : ℕ), IsIso B B₂ φ ψ lam → pow1 B₂ n * ev (n := 2) ![comp1 (B₂.A.act (n : O)) (pt R d 0), pt R d 1] lam = lam ^ n * ev (n := 2) ![comp1 φ (pt R d 0), comp1 φ (pt R d 1)] (pow1 B n) :=
  @PositivityTheory.HtPt.Cc.iso_first_power

end GlobalTheory.CompanionTheory.Ar.Conj
end

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iso_pow_one_law_formula : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB R d O) (B₂ : FB R d O) (φ ψ : Pt R 1 d) (lam : PS R 2 d) (n : ℕ), IsIso B B₂ φ ψ lam → pow1 B₂ n * ev (n := 2) ![comp1 (B₂.A.act (n : O)) (pt R d 0), pt R d 1] lam = lam ^ n * ev (n := 2) ![comp1 φ (pt R d 0), comp1 φ (pt R d 1)] (pow1 B n) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Conj.iso_pow_one_law
end

section
section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

namespace GlobalTheory.CompanionTheory.Ar.Conj

theorem lin_comp_chain : ∀ (R : Type) [CommRing R] (d : ℕ) (φ ψ : Pt R 1 d), (∀ i, constantCoeff (φ i) = 0) → (∀ i, constantCoeff (ψ i) = 0) → lin (comp1 φ ψ) 1 = lin φ 1 * lin ψ 1 ∧ lin (pt R (n := 1) d 0) 1 = 1 ∧ ∀ p : ℕ, 1 ≤ p → lin (comp1 φ (ptPow R d p 0)) p = lin φ 1 ∧ lin (comp1 φ (comp1 ψ (ptPow R d p 0))) p = lin φ 1 * lin ψ 1 :=
  @PositivityTheory.HtPt.Ca.lin_comp

end GlobalTheory.CompanionTheory.Ar.Conj
end

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formal_linear_term_composition : ∀ (R : Type) [CommRing R] (d : ℕ) (φ ψ : Pt R 1 d), (∀ i, constantCoeff (φ i) = 0) → (∀ i, constantCoeff (ψ i) = 0) → lin (comp1 φ ψ) 1 = lin φ 1 * lin ψ 1 ∧ lin (pt R (n := 1) d 0) 1 = 1 ∧ ∀ p : ℕ, 1 ≤ p → lin (comp1 φ (ptPow R d p 0)) p = lin φ 1 ∧ lin (comp1 φ (comp1 ψ (ptPow R d p 0))) p = lin φ 1 * lin ψ 1 := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Conj.lin_comp_chain
end

section
section
set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

namespace GlobalTheory.CompanionTheory.Ar.Conj.IsoAlpha

variable {R : Type} [CommRing R] {d : ℕ}

theorem hs {m n : ℕ} (b : Fin m → Pt R n d) (hb : ∀ j i, constantCoeff (b j i) = 0) :
    HasSubst (fun p : Fin m × Fin d => b p.1 p.2) :=
  hasSubst_of_constantCoeff_zero fun p => hb p.1 p.2

theorem cc_ev {m n : ℕ} (b : Fin m → Pt R n d) (hb : ∀ j i, constantCoeff (b j i) = 0) (f : PS R m d)
    (hf : constantCoeff f = 0) : constantCoeff (ev b f) = 0 :=
  constantCoeff_subst_eq_zero (a := fun p : Fin m × Fin d => b p.1 p.2) (hs b hb) (fun p => hb p.1 p.2) hf

theorem hb1 {n : ℕ} {a : Pt R n d} (ha : ∀ i, constantCoeff (a i) = 0) :
    ∀ (j : Fin 1) (i : Fin d), constantCoeff ((![a] : Fin 1 → Pt R n d) j i) = 0 := by
  intro j i
  rw [Matrix.cons_val_fin_one]
  exact ha i

theorem hb2 {n : ℕ} {a b : Pt R n d} (ha : ∀ i, constantCoeff (a i) = 0) (hb : ∀ i, constantCoeff (b i) = 0) :
    ∀ (j : Fin 2) (i : Fin d), constantCoeff ((![a, b] : Fin 2 → Pt R n d) j i) = 0 := by
  intro j i
  fin_cases j
  · exact ha i
  · exact hb i

theorem cc_comp1 {n : ℕ} {φ : Pt R 1 d} {a : Pt R n d} (hφ : ∀ i, constantCoeff (φ i) = 0)
    (ha : ∀ i, constantCoeff (a i) = 0) (i : Fin d) : constantCoeff (comp1 φ a i) = 0 :=
  cc_ev _ (hb1 ha) _ (hφ i)

theorem cc_pt {n : ℕ} (j : Fin n) (i : Fin d) : constantCoeff (pt R d j i) = 0 := by
  simp [pt]

theorem ev_ev {l m n : ℕ} (b : Fin m → Pt R n d) (hb : ∀ j i, constantCoeff (b j i) = 0)
    (a : Fin l → Pt R m d) (ha : ∀ j i, constantCoeff (a j i) = 0) (f : PS R l d) :
    ev b (ev a f) = ev (fun j i => ev b (a j i)) f :=
  subst_comp_subst_apply (hs a ha) (hs b hb) f

theorem ev_pt {m n : ℕ} (b : Fin m → Pt R n d) (hb : ∀ j i, constantCoeff (b j i) = 0) (j : Fin m) (l : Fin d) :
    ev b (pt R d j l) = b j l :=
  subst_X (hs b hb) (j, l)

theorem ev_comp1 {m n : ℕ} (b : Fin m → Pt R n d) (hb : ∀ j i, constantCoeff (b j i) = 0) (C : Pt R 1 d)
    (a : Pt R m d) (ha : ∀ i, constantCoeff (a i) = 0) (i : Fin d) :
    ev b (comp1 C a i) = comp1 C (fun l => ev b (a l)) i := by
  change ev b (ev ![a] (C i)) = ev ![fun l => ev b (a l)] (C i)
  rw [ev_ev b hb _ (hb1 ha)]
  congr 1
  funext j l
  fin_cases j
  rfl

theorem composition_assoc_no_constant {n : ℕ} (C A : Pt R 1 d) (a : Pt R n d) (hA : ∀ i, constantCoeff (A i) = 0)
    (ha : ∀ i, constantCoeff (a i) = 0) : comp1 (comp1 C A) a = comp1 C (comp1 A a) := by
  funext i
  change ev ![a] (ev ![A] (C i)) = ev ![comp1 A a] (C i)
  rw [ev_ev _ (hb1 ha) _ (hb1 hA)]
  congr 1
  funext j l
  fin_cases j
  rfl

theorem composition_identity_point_right (a : Pt R 1 d) : comp1 a (pt R d 0) = a :=
  funext fun i => ev_pt_self _ (fun j => by fin_cases j; rfl) _

theorem cc_ptPow {n : ℕ} {p : ℕ} (hp : p ≠ 0) (j : Fin n) (i : Fin d) :
    constantCoeff (ptPow R d p j i) = 0 := by
  simp [ptPow, hp]

theorem comp1_point_power_expand {n : ℕ} (p : ℕ) (a : Pt R n d) (ha : ∀ i, constantCoeff (a i) = 0) :
    comp1 (ptPow R d p (0 : Fin 1)) a = fun i => a i ^ p := by
  funext i
  change ev ![a] ((X ((0 : Fin 1), i) : PS R 1 d) ^ p) = _
  unfold ev
  rw [← coe_substAlgHom (hs _ (hb1 ha)), map_pow, coe_substAlgHom, subst_X (hs _ (hb1 ha))]
  rfl

def frobPt (p : ℕ) [Fact p.Prime] [CharP R p] (φ : Pt R 1 d) : Pt R 1 d :=
  fun i => MvPowerSeries.map (frobenius R p) (φ i)

section Frob

variable (p : ℕ) [Fact p.Prime] [CharP R p]

theorem cc_frobPt {φ : Pt R 1 d} (hφ : ∀ i, constantCoeff (φ i) = 0) (i : Fin d) :
    constantCoeff (frobPt p φ i) = 0 := by
  have h := congrArg (frobenius R p) (hφ i)
  rw [map_zero] at h
  rw [← h, frobPt, ← coeff_zero_eq_constantCoeff_apply, ← coeff_zero_eq_constantCoeff_apply, coeff_map]

theorem lin_frobPt (φ : Pt R 1 d) : lin (frobPt p φ) 1 = (lin φ 1).map (· ^ p) := by
  ext i j
  simp only [lin, frobPt, coeff_map, Matrix.map_apply, frobenius_def]

theorem frobenius_point_commutes_composition {φ : Pt R 1 d} (hφ : ∀ i, constantCoeff (φ i) = 0) :
    comp1 (ptPow R d p (0 : Fin 1)) φ = comp1 (frobPt p φ) (ptPow R d p (0 : Fin 1)) := by
  rw [comp1_point_power_expand p φ hφ]
  funext i
  rw [GlobalTheory.T.power_series_pow_p_frobenius R p d 1 (φ i)]
  change _ = ev ![ptPow R d p (0 : Fin 1)] (frobPt p φ i)
  congr 1
  funext j
  fin_cases j
  rfl

end Frob

def E (A B : Pt R 1 d) (f : PS R 2 d) : PS R 2 d :=
  ev (n := 2) ![comp1 A (pt R d 0), comp1 B (pt R d 1)] f

theorem E_E {A B C D : Pt R 1 d} (hA : ∀ i, constantCoeff (A i) = 0) (hB : ∀ i, constantCoeff (B i) = 0)
    (hC : ∀ i, constantCoeff (C i) = 0) (hD : ∀ i, constantCoeff (D i) = 0) (f : PS R 2 d) :
    E A B (E C D f) = E (comp1 C A) (comp1 D B) f := by
  have h0 : ∀ i, constantCoeff ((pt R d 0 : Pt R 2 d) i) = 0 := cc_pt 0
  have h1 : ∀ i, constantCoeff ((pt R d 1 : Pt R 2 d) i) = 0 := cc_pt 1
  have hb := hb2 (cc_comp1 hA h0) (cc_comp1 hB h1)
  unfold E
  rw [ev_ev _ hb _ (hb2 (cc_comp1 hC h0) (cc_comp1 hD h1))]
  congr 1
  funext j l
  fin_cases j
  · change ev _ (comp1 C (pt R d 0) l) = comp1 (comp1 C A) (pt R d 0) l
    rw [ev_comp1 _ hb _ _ h0, composition_assoc_no_constant C A _ hA h0]
    congr 2
    funext m
    exact ev_pt _ hb 0 m
  · change ev _ (comp1 D (pt R d 1) l) = comp1 (comp1 D B) (pt R d 1) l
    rw [ev_comp1 _ hb _ _ h1, composition_assoc_no_constant D B _ hB h1]
    congr 2
    funext m
    exact ev_pt _ hb 1 m

theorem E_eq_ptPow (p : ℕ) (f : PS R 2 d) :
    E (ptPow R d p (0 : Fin 1)) (pt R d 0) f = ev (n := 2) ![ptPow R d p 0, ptPow R d 1 1] f := by
  have e : (pt R d 1 : Pt R 2 d) = ptPow R d 1 1 := funext fun i => (pow_one _).symm
  unfold E
  rw [comp1_point_power_expand p _ (cc_pt 0), germ_comp1_zero_point_left _ (cc_pt 1), e]
  rfl

theorem E_eq_ptPow' (p : ℕ) (f : PS R 2 d) :
    E (ptPow R d p (0 : Fin 1)) (pt R d 0) f = ev (n := 2) ![ptPow R d p 0, pt R d 1] f := by
  unfold E
  rw [comp1_point_power_expand p _ (cc_pt 0), germ_comp1_zero_point_left _ (cc_pt 1)]
  rfl

theorem axOne_E {A B : Pt R 1 d} (hA : ∀ i, constantCoeff (A i) = 0) (hB : ∀ i, constantCoeff (B i) = 0)
    {f : PS R 2 d} (hf : AxOne f) : AxOne (E A B f) :=
  (GlobalTheory.T.formal_bilinear_term_product R d f f A B hf hf hA hB).2.2.2.1

theorem bil_E {A B : Pt R 1 d} (hA : ∀ i, constantCoeff (A i) = 0) (hB : ∀ i, constantCoeff (B i) = 0)
    {f : PS R 2 d} (hf : AxOne f) : bil (E A B f) 1 1 = (lin A 1).transpose * bil f 1 1 * lin B 1 :=
  (GlobalTheory.T.formal_bilinear_term_product R d f f A B hf hf hA hB).2.2.2.2.1

theorem bil_E_ptPow {p : ℕ} (hp : 1 ≤ p) {f : PS R 2 d} (hf : AxOne f) :
    bil (E (ptPow R d p (0 : Fin 1)) (pt R d 0) f) p 1 = bil f 1 1 := by
  have hc : ∀ i, constantCoeff ((pt R d 0 : Pt R 1 d) i) = 0 := cc_pt 0
  rw [E_eq_ptPow]
  exact (GlobalTheory.T.formal_bilinear_term_product R d f f _ _ hf hf hc hc).2.2.2.2.2.2 p 1 hp le_rfl

theorem axOne_mul {f g : PS R 2 d} (hf : AxOne f) (hg : AxOne g) : AxOne (f * g) :=
  (GlobalTheory.T.formal_bilinear_term_product R d f g _ _ hf hg (cc_pt 0) (cc_pt 0)).1

theorem bil_mul {f g : PS R 2 d} (hf : AxOne f) (hg : AxOne g) (m : ℕ) :
    bil (f * g) m 1 = bil f m 1 + bil g m 1 :=
  (GlobalTheory.T.formal_bilinear_term_product R d f g _ _ hf hg (cc_pt 0) (cc_pt 0)).2.1 m

theorem axOne_one : AxOne (1 : PS R 2 d) := ⟨ev_one _, ev_one _⟩

theorem axOne_pow {f : PS R 2 d} (hf : AxOne f) (n : ℕ) : AxOne (f ^ n) := by
  induction n with
  | zero => simpa using axOne_one
  | succ n ih => rw [pow_succ]; exact axOne_mul ih hf

theorem bil_pow {f : PS R 2 d} (hf : AxOne f) {m : ℕ} (hm : m ≠ 0) (n : ℕ) :
    bil (f ^ n) m 1 = n • bil f m 1 := by
  induction n with
  | zero => simp [bil_one_eq_zero hm]
  | succ n ih => rw [pow_succ, bil_mul (axOne_pow hf n) hf, ih, succ_nsmul]

section Main

variable {O : Type} [CommRing O] [StarRing O] (p : ℕ) [Fact p.Prime] [CharP R p]
variable {B B₂ : FB R d O} {φ ψ : Pt R 1 d} {lam : PS R 2 d}

theorem hw_rel (h : IsIso B B₂ φ ψ lam) : lin φ 1 * hw B₂ p = hw B p * (lin φ 1).map (· ^ p) := by
  obtain ⟨V, cV, eV, lV⟩ := GlobalTheory.T.multiplication_by_p_factors_frobenius R p d O B
  obtain ⟨V₂, cV₂, eV₂, lV₂⟩ := GlobalTheory.T.multiplication_by_p_factors_frobenius R p d O B₂
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hp1 : 1 ≤ p := Nat.one_le_iff_ne_zero.2 hp
  have e := h.act (p : O)
  rw [eV₂, eV, composition_assoc_no_constant V _ φ (cc_ptPow hp 0) h.c₁, frobenius_point_commutes_composition p h.c₁] at e
  have l1 := ((GlobalTheory.T.formal_linear_term_composition R d φ V₂ h.c₁ cV₂).2.2 p hp1).2
  have l2 := ((GlobalTheory.T.formal_linear_term_composition R d V (frobPt p φ) cV (cc_frobPt p h.c₁)).2.2 p hp1).2
  rw [← lV₂, ← lV, ← lin_frobPt, ← l1, ← l2, e]

theorem am_rel (h : IsIso B B₂ φ ψ lam) :
    am B₂ p + (hw B₂ p).transpose * bil lam 1 1 =
      ((lin φ 1).map (· ^ p)).transpose * am B p * lin φ 1 := by
  obtain ⟨V₂, cV₂, eV₂, lV₂⟩ := GlobalTheory.T.multiplication_by_p_factors_frobenius R p d O B₂
  obtain ⟨g₂, ax₂, e₂, b₂⟩ := GlobalTheory.T.pow_one_series_p_formula R p d O B₂
  obtain ⟨g, ax, e, b⟩ := GlobalTheory.T.pow_one_series_p_formula R p d O B
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hp1 : 1 ≤ p := Nat.one_le_iff_ne_zero.2 hp
  have cPw : ∀ i, constantCoeff (ptPow R d p (0 : Fin 1) i) = 0 := cc_ptPow hp 0
  have cI : ∀ i, constantCoeff ((pt R d 0 : Pt R 1 d) i) = 0 := cc_pt 0
  have cF : ∀ i, constantCoeff (frobPt p φ i) = 0 := cc_frobPt p h.c₁
  have key := GlobalTheory.T.iso_pow_one_law_formula R d O B B₂ φ ψ lam p h
  have r1 : pow1 B₂ p = E (ptPow R d p (0 : Fin 1)) (pt R d 0) g₂ := by rw [e₂, E_eq_ptPow']
  have r2 : ev (n := 2) ![comp1 (B₂.A.act (p : O)) (pt R d 0), pt R d 1] lam =
      E (ptPow R d p (0 : Fin 1)) (pt R d 0) (E V₂ (pt R d 0) lam) := by
    rw [E_E cPw cI cV₂ cI, composition_identity_point_right, ← eV₂]
    unfold E
    rw [germ_comp1_zero_point_left _ (cc_pt 1)]
  have r3 : ev (n := 2) ![comp1 φ (pt R d 0), comp1 φ (pt R d 1)] (pow1 B p) =
      E (ptPow R d p (0 : Fin 1)) (pt R d 0) (E (frobPt p φ) φ g) := by
    change E φ φ (pow1 B p) = _
    rw [e, ← E_eq_ptPow', E_E h.c₁ h.c₁ cPw cI, E_E cPw cI cF h.c₁, frobenius_point_commutes_composition p h.c₁,
      germ_comp1_zero_point_left _ h.c₁, composition_identity_point_right]
  rw [r1, r2, r3] at key
  have a1 := axOne_E cPw cI ax₂
  have aL := axOne_E cV₂ cI h.ax
  have a2 := axOne_E cPw cI aL
  have aG := axOne_E cF h.c₁ ax
  have a3 := axOne_E cPw cI aG
  have k := congrArg (fun f => bil f p 1) key
  have z : p • bil lam p 1 = 0 := by
    ext i j
    simp [nsmul_eq_mul, CharP.cast_eq_zero R p]
  beta_reduce at k
  rw [bil_mul a1 a2, bil_mul (axOne_pow h.ax p) a3, bil_E_ptPow hp1 ax₂, bil_E_ptPow hp1 aL,
    bil_E_ptPow hp1 aG, bil_pow h.ax hp, z, zero_add, bil_E cV₂ cI h.ax, bil_E cF h.c₁ ax, lV₂, b₂, b,
    lin_frobPt, lin_pt_eq_one, mul_one] at k
  exact k

theorem frob_mul_eq_one {g g' : Matrix (Fin d) (Fin d) R} (h : g * g' = 1) :
    g.map (· ^ p) * g'.map (· ^ p) = 1 := by
  have e : ∀ M : Matrix (Fin d) (Fin d) R, M.map (· ^ p) = (frobenius R p).mapMatrix M := fun M => by
    ext i j
    simp [frobenius_def]
  rw [e, e, ← map_mul, h, map_one]

end Main

end GlobalTheory.CompanionTheory.Ar.Conj.IsoAlpha

namespace GlobalTheory.CompanionTheory.Ar.Conj

theorem alpha_beta_of_isIso : ∀ (R : Type) [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p] (d : ℕ) (O : Type)
    [CommRing O] [StarRing O] (B : FB R d O) (B₂ : FB R d O) (φ ψ : Pt R 1 d) (lam : PS R 2 d),
    IsIso B B₂ φ ψ lam →
      (∀ u, alpha B p (((lin φ 1).map (· ^ p)).mulVec u) = transH φ ψ lam (alpha B₂ p u)) ∧
        ∀ y, beta B p (transH φ ψ lam y) = ((lin ψ 1).transpose.map (· ^ p)).mulVec (beta B₂ p y) := by
  intro R _ p _ _ d O _ _ B B₂ φ ψ lam h
  obtain ⟨i1, -, -, -, -, hpair⟩ := GlobalTheory.T.formal_isomorphism_transport R d O B B₂ φ ψ lam h
  have H1 := IsoAlpha.hw_rel p h
  have H2 := IsoAlpha.am_rel p h
  have A : ∀ u, alpha B p (((lin φ 1).map (· ^ p)).mulVec u) = transH φ ψ lam (alpha B₂ p u) := by
    intro u
    rw [alpha_apply, alpha_apply, transH_apply]
    refine Prod.ext ?_ ?_
    · simp only [Matrix.mulVec_mulVec, H1]
    · change (am B p).transpose.mulVec (((lin φ 1).map (· ^ p)).mulVec u) =
        (lin ψ 1).transpose.mulVec ((am B₂ p).transpose.mulVec u +
          (bil lam 1 1).transpose.mulVec ((hw B₂ p).mulVec u))
      have t : (am B₂ p).transpose + (bil lam 1 1).transpose * hw B₂ p =
          (lin φ 1).transpose * ((am B p).transpose * (lin φ 1).map (· ^ p)) := by
        have := congrArg Matrix.transpose H2
        simpa [Matrix.transpose_add, Matrix.transpose_mul, Matrix.mul_assoc] using this
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.add_mulVec, Matrix.mulVec_mulVec, t,
        ← Matrix.mul_assoc, ← Matrix.transpose_mul, i1, Matrix.transpose_one, Matrix.one_mul]
  refine ⟨A, fun y => ?_⟩
  have key : ∀ v, ((lin φ 1).map (· ^ p)).mulVec v ⬝ᵥ beta B p (transH φ ψ lam y) = v ⬝ᵥ beta B₂ p y := fun v => by
    rw [dotProduct_beta, A, hpair, ← dotProduct_beta]
  have k2 : ((lin φ 1).map (· ^ p)).transpose.mulVec (beta B p (transH φ ψ lam y)) = beta B₂ p y := by
    have k3 : ∀ v, v ⬝ᵥ ((lin φ 1).map (· ^ p)).transpose.mulVec (beta B p (transH φ ψ lam y)) =
        v ⬝ᵥ beta B₂ p y := fun v => by
      rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, key]
    funext i
    simpa using k3 (Pi.single i 1)
  rw [← k2, Matrix.mulVec_mulVec, Matrix.transpose_map, ← Matrix.transpose_mul,
    IsoAlpha.frob_mul_eq_one p i1, Matrix.transpose_one, Matrix.one_mulVec]

end GlobalTheory.CompanionTheory.Ar.Conj
end
end

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.alpha_beta_isomorphism_transport : ∀ (R : Type) [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB R d O) (B₂ : FB R d O) (φ ψ : Pt R 1 d) (lam : PS R 2 d), IsIso B B₂ φ ψ lam → (∀ u, alpha B p (((lin φ 1).map (· ^ p)).mulVec u) = transH φ ψ lam (alpha B₂ p u)) ∧ ∀ y, beta B p (transH φ ψ lam y) = ((lin ψ 1).transpose.map (· ^ p)).mulVec (beta B₂ p y) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Conj.alpha_beta_of_isIso
end

section
section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

namespace GlobalTheory.CompanionTheory.Ar.Split

theorem isotropic_residue_injective_splits : ∀ (A : Type) [CommRing A] [IsLocalRing A] (d : ℕ) (h a S : Matrix (Fin d) (Fin d) A), a * h - h.transpose * S * h - h.transpose * a.transpose = 0 → (∀ u : Fin d → IsLocalRing.ResidueField A, (h.map (IsLocalRing.residue A)).mulVec u = 0 → (a.transpose.map (IsLocalRing.residue A)).mulVec u = 0 → u = 0) → ∃ r₁ r₂ s₁ s₂ : Matrix (Fin d) (Fin d) A, r₁ * h + r₂ * a.transpose = 1 ∧ (a - h.transpose * S) * s₁ - h.transpose * s₂ = 1 ∧ h * r₁ + s₁ * (a - h.transpose * S) = 1 ∧ h * r₂ - s₁ * h.transpose = 0 ∧ a.transpose * r₁ + s₂ * (a - h.transpose * S) = 0 ∧ a.transpose * r₂ - s₂ * h.transpose = 1 :=
  @PositivityTheory.HtPt.Cg.split_local

end GlobalTheory.CompanionTheory.Ar.Split
end

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_matrix_coprime_decomposition : ∀ (A : Type) [CommRing A] [IsLocalRing A] (d : ℕ) (h a S : Matrix (Fin d) (Fin d) A), a * h - h.transpose * S * h - h.transpose * a.transpose = 0 → (∀ u : Fin d → IsLocalRing.ResidueField A, (h.map (IsLocalRing.residue A)).mulVec u = 0 → (a.transpose.map (IsLocalRing.residue A)).mulVec u = 0 → u = 0) → ∃ r₁ r₂ s₁ s₂ : Matrix (Fin d) (Fin d) A, r₁ * h + r₂ * a.transpose = 1 ∧ (a - h.transpose * S) * s₁ - h.transpose * s₂ = 1 ∧ h * r₁ + s₁ * (a - h.transpose * S) = 1 ∧ h * r₂ - s₁ * h.transpose = 0 ∧ a.transpose * r₁ + s₂ * (a - h.transpose * S) = 0 ∧ a.transpose * r₂ - s₂ * h.transpose = 1 := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Split.isotropic_residue_injective_splits
end

section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Conj.Fam

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Crv.Inhab

variable {K : Type} [Field K] (C : ACurve K) {d : ℕ}

def colLat (i : C.I) (g : Matrix (Fin d) (Fin d) K) : AddSubgroup (Fin d → K) :=
  (trivLat C d i).map (Matrix.toLin' g).toAddMonoidHom

def stdH (d : ℕ) (i : C.I) : AddSubgroup ((Fin d → K) × (Fin d → K)) :=
  (trivLat C d i).prod (trivLat C d i)

def imLat (i : C.I) (T : ((Fin d → K) × (Fin d → K)) →ₗ[K] (Fin d → K) × (Fin d → K)) :
    AddSubgroup ((Fin d → K) × (Fin d → K)) :=
  (stdH C d i).map T.toAddMonoidHom

theorem mem_colLat {i : C.I} {g : Matrix (Fin d) (Fin d) K} {x : Fin d → K} :
    x ∈ colLat C i g ↔ ∃ w ∈ trivLat C d i, g.mulVec w = x := by
  simp [colLat, AddSubgroup.mem_map]

theorem mem_imLat {i : C.I} {T : ((Fin d → K) × (Fin d → K)) →ₗ[K] (Fin d → K) × (Fin d → K)}
    {y : (Fin d → K) × (Fin d → K)} : y ∈ imLat C i T ↔ ∃ w ∈ stdH C d i, T w = y := by
  simp [imLat, AddSubgroup.mem_map]

theorem mem_stdH {i : C.I} {y : (Fin d → K) × (Fin d → K)} :
    y ∈ stdH C d i ↔ y.1 ∈ trivLat C d i ∧ y.2 ∈ trivLat C d i := AddSubgroup.mem_prod

theorem mem_colLat_iff {i : C.I} {g g' : Matrix (Fin d) (Fin d) K} (h₁ : g * g' = 1) (h₂ : g' * g = 1)
    {x : Fin d → K} : x ∈ colLat C i g ↔ ∀ j, C.v i (g'.mulVec x j) ≤ 1 := by
  rw [mem_colLat]
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [Matrix.mulVec_mulVec, h₂, Matrix.one_mulVec]
    exact hw
  · intro h
    exact ⟨g'.mulVec x, h, by rw [Matrix.mulVec_mulVec, h₁, Matrix.one_mulVec]⟩

def frame {g g' : Matrix (Fin d) (Fin d) K} (h₁ : g * g' = 1) (h₂ : g' * g = 1) :
    Module.Basis (Fin d) K (Fin d → K) :=
  (Pi.basisFun K (Fin d)).map (Matrix.toLin'OfInv h₂ h₁)

theorem frame_repr {g g' : Matrix (Fin d) (Fin d) K} (h₁ : g * g' = 1) (h₂ : g' * g = 1)
    (x : Fin d → K) (q : Fin d) : (frame h₁ h₂).repr x q = g'.mulVec x q := by
  simp [frame, Matrix.toLin'OfInv]

theorem frame_apply {g g' : Matrix (Fin d) (Fin d) K} (h₁ : g * g' = 1) (h₂ : g' * g = 1)
    (q : Fin d) : frame h₁ h₂ q = fun r => g r q := by
  funext r
  simp [frame, Matrix.toLin'OfInv]

theorem isLatOf_frame (i : C.I) {g g' : Matrix (Fin d) (Fin d) K} (h₁ : g * g' = 1) (h₂ : g' * g = 1) :
    IsLatOf C i (frame h₁ h₂) (colLat C i g) := fun x => by
  rw [mem_colLat_iff C h₁ h₂]
  simp only [frame_repr]

theorem isBun_frames {V ι : Type} [AddCommGroup V] [Module K V] [Fintype ι]
    (b : C.I → Module.Basis ι K V) (b₀ : Module.Basis ι K V) (L : C.I → AddSubgroup V)
    (hb : ∀ i x, x ∈ L i ↔ ∀ q, C.v i ((b i).repr x q) ≤ 1)
    (hfin : {i | ¬ ∀ x, x ∈ L i ↔ ∀ q, C.v i (b₀.repr x q) ≤ 1}.Finite) : IsBun C L := by
  let e : ι ≃ Fin (Module.finrank K V) :=
    Fintype.equivFinOfCardEq (Module.finrank_eq_card_basis b₀).symm
  have re : ∀ (c : Module.Basis ι K V) (i : C.I) (L' : AddSubgroup V),
      (∀ x, x ∈ L' ↔ ∀ q, C.v i (c.repr x q) ≤ 1) → IsLatOf C i (c.reindex e) L' := by
    intro c i L' h x
    rw [h]
    simp only [Module.Basis.repr_reindex_apply]
    exact ⟨fun H q => H _, fun H q => by simpa using H (e q)⟩
  exact ⟨fun i => ⟨_, re _ i _ (hb i)⟩, b₀.reindex e,
    hfin.subset fun i hi h => hi (re _ _ _ h)⟩

def IntM (i : C.I) (M : Matrix (Fin d) (Fin d) K) : Prop := ∀ a b, C.v i (M a b) ≤ 1

theorem colLat_eq_triv {i : C.I} {g g' : Matrix (Fin d) (Fin d) K} (h₁ : g * g' = 1) (h₂ : g' * g = 1)
    (hg : IntM C i g) (hg' : IntM C i g') : colLat C i g = trivLat C d i := by
  ext x
  rw [mem_colLat]
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact mulVec_mem_trivLat C hg hw
  · intro hx
    exact ⟨g'.mulVec x, mulVec_mem_trivLat C hg' hx, by rw [Matrix.mulVec_mulVec, h₁, Matrix.one_mulVec]⟩

theorem isBun_colLat (g g' : C.I → Matrix (Fin d) (Fin d) K) (h₁ : ∀ i, g i * g' i = 1)
    (h₂ : ∀ i, g' i * g i = 1) (hfin : {i | ¬ (IntM C i (g i) ∧ IntM C i (g' i))}.Finite) :
    IsBun C fun i => colLat C i (g i) := by
  refine isBun_frames C (fun i => frame (h₁ i) (h₂ i)) (Pi.basisFun K (Fin d)) _
    (fun i x => (isLatOf_frame C i (h₁ i) (h₂ i)) x) (hfin.subset fun i hi h => hi ?_)
  intro x
  rw [colLat_eq_triv C (h₁ i) (h₂ i) h.1 h.2]
  simp [mem_trivLat]

theorem dotDual_colLat (g g' : C.I → Matrix (Fin d) (Fin d) K) (h₁ : ∀ i, g i * g' i = 1)
    (h₂ : ∀ i, g' i * g i = 1) :
    dotDual C (fun i => colLat C i (g i)) = fun i => colLat C i (g' i).transpose := by
  funext i
  have t₁ : (g' i).transpose * (g i).transpose = 1 := by
    rw [← Matrix.transpose_mul, h₁, Matrix.transpose_one]
  have t₂ : (g i).transpose * (g' i).transpose = 1 := by
    rw [← Matrix.transpose_mul, h₂, Matrix.transpose_one]
  have := DegDual.isLatOf_dual C (fun i => colLat C i (g i)) (dotProductBilin K K) i
    (frame (h₁ i) (h₂ i)) (frame t₁ t₂) (fun y q => ?_) (isLatOf_frame C i (h₁ i) (h₂ i))
  · ext y
    rw [show dotDual C (fun i => colLat C i (g i)) i = dualLat C _ (dotProductBilin K K) i from rfl,
      this y, (isLatOf_frame C i t₁ t₂) y]
  · rw [frame_repr, frame_apply]
    simp [Matrix.mulVec, dotProduct, Matrix.transpose_apply]

theorem frobLat_colLat (p : ℕ) [Fact p.Prime] [CharP K p] (g g' : C.I → Matrix (Fin d) (Fin d) K)
    (h₁ : ∀ i, g i * g' i = 1) (h₂ : ∀ i, g' i * g i = 1) :
    frobLat C p (fun i => colLat C i (g i)) = fun i => colLat C i ((g i).map (· ^ p)) := by
  funext i
  have e : ∀ M : Matrix (Fin d) (Fin d) K, M.map (· ^ p) = (frobenius K p).mapMatrix M := fun M => rfl
  have t₁ : (g i).map (· ^ p) * (g' i).map (· ^ p) = 1 := by
    rw [e, e, ← map_mul, h₁, map_one]
  have t₂ : (g' i).map (· ^ p) * (g i).map (· ^ p) = 1 := by
    rw [e, e, ← map_mul, h₂, map_one]
  have := DegFrob.isLatOf_frob C p (fun i => colLat C i (g i)) i (frame (h₁ i) (h₂ i)) (frame t₁ t₂)
    (fun q => ?_) (isLatOf_frame C i (h₁ i) (h₂ i))
  · ext y
    rw [this y, (isLatOf_frame C i t₁ t₂) y]
  · rw [frame_apply, frame_apply]
    rfl

local notation "VV" K:max d:max => ((Fin d → K) × (Fin d → K))

def stdBasis (K : Type) [Field K] (d : ℕ) : Module.Basis (Fin d ⊕ Fin d) K (VV K d) :=
  (Pi.basisFun K (Fin d)).prod (Pi.basisFun K (Fin d))

theorem forall_stdBasis (i : C.I) (y : VV K d) :
    (∀ q, C.v i ((stdBasis K d).repr y q) ≤ 1) ↔ y ∈ stdH C d i := by
  rw [mem_stdH, Sum.forall]
  simp [stdBasis, mem_trivLat]

theorem isBun_imLat (T : C.I → VV K d →ₗ[K] VV K d) (hT : ∀ i, Function.Bijective (T i))
    (hfin : {i | imLat C i (T i) ≠ stdH C d i}.Finite) : IsBun C fun i => imLat C i (T i) := by
  refine isBun_frames C (fun i => (stdBasis K d).map (LinearEquiv.ofBijective (T i) (hT i)))
    (stdBasis K d) _ (fun i x => ?_) (hfin.subset fun i hi h => hi ?_)
  · rw [mem_imLat]
    simp only [Module.Basis.map_repr, LinearEquiv.trans_apply]
    rw [forall_stdBasis]
    constructor
    · rintro ⟨w, hw, rfl⟩
      have : (LinearEquiv.ofBijective (T i) (hT i)).symm (T i w) = w :=
        (LinearEquiv.ofBijective (T i) (hT i)).symm_apply_apply w
      rwa [this]
    · intro h
      exact ⟨_, h, (LinearEquiv.ofBijective (T i) (hT i)).apply_symm_apply x⟩
  · intro x
    rw [forall_stdBasis]
    exact iff_of_eq (congrArg (x ∈ ·) h)

theorem transH_mem_stdH {i : C.I} {φ ψ : Pt K 1 d} {lam : PS K 2 d}
    (hg : IntM C i (lin φ 1)) (hg' : IntM C i (lin ψ 1)) (hl : IntM C i (bil lam 1 1))
    {w : VV K d} (hw : w ∈ stdH C d i) : transH φ ψ lam w ∈ stdH C d i := by
  rw [mem_stdH] at hw ⊢
  rw [transH_apply]
  exact ⟨mulVec_mem_trivLat C hg hw.1, mulVec_mem_trivLat C (fun a b => hg' b a)
    (add_mem hw.2 (mulVec_mem_trivLat C (fun a b => hl b a) hw.1))⟩

theorem imLat_transH_eq {i : C.I} {φ ψ : Pt K 1 d} {lam : PS K 2 d}
    (h₁ : lin φ 1 * lin ψ 1 = 1) (h₂ : lin ψ 1 * lin φ 1 = 1)
    (hg : IntM C i (lin φ 1)) (hg' : IntM C i (lin ψ 1)) (hl : IntM C i (bil lam 1 1)) :
    imLat C i (transH φ ψ lam) = stdH C d i := by
  ext y
  rw [mem_imLat]
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact transH_mem_stdH C hg hg' hl hw
  · intro hy
    have hy' := (mem_stdH C).1 hy
    have a₁ := mulVec_mem_trivLat C hg' hy'.1
    have a₂ := mulVec_mem_trivLat C (fun a b => hl b a) a₁
    have a₃ := mulVec_mem_trivLat C (fun a b => hg b a) hy'.2
    refine ⟨((lin ψ 1).mulVec y.1, (lin φ 1).transpose.mulVec y.2 -
      (bil lam 1 1).transpose.mulVec ((lin ψ 1).mulVec y.1)),
      (mem_stdH C).2 ⟨a₁, sub_mem a₃ a₂⟩, ?_⟩
    have t : (lin ψ 1).transpose * (lin φ 1).transpose = 1 := by
      rw [← Matrix.transpose_mul, h₁, Matrix.transpose_one]
    rw [transH_apply]
    refine Prod.ext ?_ ?_
    · simp only [Matrix.mulVec_mulVec, h₁, Matrix.one_mulVec]
    · simp only [sub_add_cancel, Matrix.mulVec_mulVec, t, Matrix.one_mulVec]

theorem hodge_family (φ ψ : C.I → Pt K 1 d) (lam : C.I → PS K 2 d)
    (h₁ : ∀ i, lin (φ i) 1 * lin (ψ i) 1 = 1) (h₂ : ∀ i, lin (ψ i) 1 * lin (φ i) 1 = 1) :
    ShortExact C (dotDual C fun i => colLat C i (lin (φ i) 1))
      (fun i => imLat C i (transH (φ i) (ψ i) (lam i))) (fun i => colLat C i (lin (φ i) 1))
      (LinearMap.inr K _ _) (LinearMap.fst K _ _) := by
  rw [dotDual_colLat C _ _ h₁ h₂]
  refine ⟨LinearMap.inr_injective, Function.Exact.inr_fst, LinearMap.fst_surjective,
    fun i x => ?_, fun i z => ?_⟩
  · rw [mem_colLat]
    simp only [LinearMap.inr_apply]
    rw [mem_imLat]
    constructor
    · rintro ⟨w, hw, rfl⟩
      refine ⟨(0, w), (mem_stdH C).2 ⟨zero_mem _, hw⟩, ?_⟩
      rw [transH_apply]
      simp
    · rintro ⟨w, hw, e⟩
      rw [transH_apply, Prod.mk.injEq] at e
      have hw' := (mem_stdH C).1 hw
      have e₁ : w.1 = 0 := by
        have := congrArg (lin (ψ i) 1).mulVec e.1
        simpa [Matrix.mulVec_mulVec, h₂ i] using this
      refine ⟨w.2, hw'.2, ?_⟩
      rw [← e.2, e₁]
      simp
  · rw [mem_colLat]
    simp only [LinearMap.fst_apply]
    constructor
    · rintro ⟨w, hw, rfl⟩
      refine ⟨transH (φ i) (ψ i) (lam i) (w, 0), (mem_imLat C).2
        ⟨(w, 0), (mem_stdH C).2 ⟨hw, zero_mem _⟩, rfl⟩, ?_⟩
      rw [transH_apply]
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨w, hw, rfl⟩ := (mem_imLat C).1 hy
      exact ⟨w.1, ((mem_stdH C).1 hw).1, by rw [transH_apply]⟩

structure LocSplit (i : C.I) (a : (Fin d → K) →ₗ[K] VV K d) (b : VV K d →ₗ[K] Fin d → K) : Prop where

  a_int : ∀ u ∈ trivLat C d i, a u ∈ stdH C d i

  b_int : ∀ y ∈ stdH C d i, b y ∈ trivLat C d i

  zero : ∀ u, b (a u) = 0

  split : ∃ (r : VV K d →ₗ[K] Fin d → K) (s : (Fin d → K) →ₗ[K] VV K d),
    (∀ y ∈ stdH C d i, r y ∈ trivLat C d i) ∧ (∀ z ∈ trivLat C d i, s z ∈ stdH C d i) ∧
      (∀ u, r (a u) = u) ∧ (∀ z, b (s z) = z) ∧ ∀ y, a (r y) + s (b y) = y

theorem conj_family (p : ℕ) [Fact p.Prime] [CharP K p] (hI : Nonempty C.I)
    (g g' : C.I → Matrix (Fin d) (Fin d) K) (h₁ : ∀ i, g i * g' i = 1) (h₂ : ∀ i, g' i * g i = 1)
    (T : C.I → VV K d →ₗ[K] VV K d) (hT : ∀ i, Function.Bijective (T i))
    (α : (Fin d → K) →ₗ[K] VV K d) (β : VV K d →ₗ[K] Fin d → K)
    (a : C.I → (Fin d → K) →ₗ[K] VV K d) (b : C.I → VV K d →ₗ[K] Fin d → K)
    (hα : ∀ i u, α (((g i).map (· ^ p)).mulVec u) = T i (a i u))
    (hβ : ∀ i y, β (T i y) = ((g' i).transpose.map (· ^ p)).mulVec (b i y))
    (hloc : ∀ i, LocSplit C i (a i) (b i)) :
    ShortExact C (frobLat C p fun i => colLat C i (g i)) (fun i => imLat C i (T i))
      (frobLat C p (dotDual C fun i => colLat C i (g i))) α β := by
  have fm : ∀ M : Matrix (Fin d) (Fin d) K, M.map (· ^ p) = (frobenius K p).mapMatrix M :=
    fun _ => rfl
  have t₁ : ∀ i, (g' i).transpose * (g i).transpose = 1 := fun i => by
    rw [← Matrix.transpose_mul, h₁, Matrix.transpose_one]
  have t₂ : ∀ i, (g i).transpose * (g' i).transpose = 1 := fun i => by
    rw [← Matrix.transpose_mul, h₂, Matrix.transpose_one]
  have hF₂ : frobLat C p (dotDual C fun i => colLat C i (g i)) =
      fun i => colLat C i ((g' i).transpose.map (· ^ p)) := by
    rw [dotDual_colLat C g g' h₁ h₂]
    exact frobLat_colLat C p (fun i => (g' i).transpose) (fun i => (g i).transpose) t₁ t₂
  rw [hF₂, frobLat_colLat C p g g' h₁ h₂]
  have G₁ : ∀ i (u : Fin d → K), ((g i).map (· ^ p)).mulVec (((g' i).map (· ^ p)).mulVec u) = u :=
    fun i u => by rw [Matrix.mulVec_mulVec, fm, fm, ← map_mul, h₁, map_one, Matrix.one_mulVec]
  have G₂ : ∀ i (u : Fin d → K), ((g' i).map (· ^ p)).mulVec (((g i).map (· ^ p)).mulVec u) = u :=
    fun i u => by rw [Matrix.mulVec_mulVec, fm, fm, ← map_mul, h₂, map_one, Matrix.one_mulVec]
  have D₁ : ∀ i (u : Fin d → K), ((g' i).transpose.map (· ^ p)).mulVec
      (((g i).transpose.map (· ^ p)).mulVec u) = u :=
    fun i u => by rw [Matrix.mulVec_mulVec, fm, fm, ← map_mul, t₁, map_one, Matrix.one_mulVec]
  have D₂ : ∀ i (u : Fin d → K), ((g i).transpose.map (· ^ p)).mulVec
      (((g' i).transpose.map (· ^ p)).mulVec u) = u :=
    fun i u => by rw [Matrix.mulVec_mulVec, fm, fm, ← map_mul, t₂, map_one, Matrix.one_mulVec]
  obtain ⟨i₀⟩ := hI
  obtain ⟨r₀, s₀, -, -, ra₀, bs₀, as₀⟩ := (hloc i₀).split
  refine ⟨?_, ?_, ?_, fun i x => ?_, fun i z => ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro x hx
    have e : T i₀ (a i₀ (((g' i₀).map (· ^ p)).mulVec x)) = 0 := by
      rw [← hα, G₁, hx]
    have e' : a i₀ (((g' i₀).map (· ^ p)).mulVec x) = 0 :=
      (hT i₀).1 (by rw [e, map_zero])
    have e'' := ra₀ (((g' i₀).map (· ^ p)).mulVec x)
    rw [e', map_zero] at e''
    rw [← G₁ i₀ x, ← e'', Matrix.mulVec_zero]
  · intro y
    obtain ⟨w, rfl⟩ := (hT i₀).2 y
    constructor
    · intro hy
      rw [hβ] at hy
      have e : b i₀ w = 0 := by
        rw [← D₂ i₀ (b i₀ w), hy, Matrix.mulVec_zero]
      have e' := as₀ w
      rw [e, map_zero, add_zero] at e'
      exact ⟨((g i₀).map (· ^ p)).mulVec (r₀ w), by rw [hα, e']⟩
    · rintro ⟨x, hx⟩
      have e : T i₀ w = T i₀ (a i₀ (((g' i₀).map (· ^ p)).mulVec x)) := by
        rw [← hα, G₁, hx]
      rw [e, hβ, (hloc i₀).zero, Matrix.mulVec_zero]
  · intro z
    refine ⟨T i₀ (s₀ (((g i₀).transpose.map (· ^ p)).mulVec z)), ?_⟩
    rw [hβ, bs₀, D₁]
  · obtain ⟨r, s, hr, hs, ra, bs, as⟩ := (hloc i).split
    rw [mem_colLat]
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact (mem_imLat C).2 ⟨a i w, (hloc i).a_int w hw, (hα i w).symm⟩
    · intro hx
      obtain ⟨w, hw, e⟩ := (mem_imLat C).1 hx
      have e' : w = a i (((g' i).map (· ^ p)).mulVec x) := (hT i).1 (by rw [e, ← hα, G₁])
      refine ⟨r w, hr w hw, ?_⟩
      rw [e', ra, G₁]
  · obtain ⟨r, s, hr, hs, ra, bs, as⟩ := (hloc i).split
    rw [mem_colLat]
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨T i (s w), (mem_imLat C).2 ⟨s w, hs w hw, rfl⟩, by rw [hβ, bs]⟩
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨w, hw, rfl⟩ := (mem_imLat C).1 hy
      exact ⟨b i w, (hloc i).b_int w hw, (hβ i w).symm⟩

theorem intM_map (i : C.I) (M : Matrix (Fin d) (Fin d) (C.v i).valuationSubring) :
    IntM C i (M.map (C.v i).valuationSubring.subtype) := fun a b =>
  (Valuation.mem_valuationSubring_iff _ _).1 (M a b).2

omit [Field K] in
theorem matrix_eq_zero_of_mulVec {R : Type} [CommRing R] {M : Matrix (Fin d) (Fin d) R}
    (h : ∀ u, M.mulVec u = 0) : M = 0 := by
  ext a b
  have := congrFun (h (Pi.single b 1)) a
  simpa using this

variable {O : Type} [CommRing O] [StarRing O]

theorem locSplit_of_mats (B : FB K d O) (p : ℕ) (i : C.I) (r₁ r₂ s₁ s₂ : Matrix (Fin d) (Fin d) K)
    (ih : IntM C i (hw B p)) (ia : IntM C i (am B p)) (iS : IntM C i (bil B.sy 1 1))
    (ir₁ : IntM C i r₁) (ir₂ : IntM C i r₂) (is₁ : IntM C i s₁) (is₂ : IntM C i s₂)
    (hz : ∀ u, beta B p (alpha B p u) = 0)
    (e₁ : r₁ * hw B p + r₂ * (am B p).transpose = 1)
    (e₂ : (am B p - (hw B p).transpose * bil B.sy 1 1) * s₁ - (hw B p).transpose * s₂ = 1)
    (e₃ : hw B p * r₁ + s₁ * (am B p - (hw B p).transpose * bil B.sy 1 1) = 1)
    (e₄ : hw B p * r₂ - s₁ * (hw B p).transpose = 0)
    (e₅ : (am B p).transpose * r₁ + s₂ * (am B p - (hw B p).transpose * bil B.sy 1 1) = 0)
    (e₆ : (am B p).transpose * r₂ - s₂ * (hw B p).transpose = 1) :
    LocSplit C i (alpha B p) (beta B p) := by
  refine ⟨fun u hu => ?_, fun y hy => ?_, hz, ?_⟩
  · rw [alpha_apply]
    exact (mem_stdH C).2 ⟨mulVec_mem_trivLat C ih hu, mulVec_mem_trivLat C (fun a b => ia b a) hu⟩
  · have hy' := (mem_stdH C).1 hy
    rw [beta_apply, Matrix.sub_mulVec, ← Matrix.mulVec_mulVec]
    exact sub_mem (mulVec_mem_trivLat C (fun a b => ih b a) hy'.2)
      (sub_mem (mulVec_mem_trivLat C ia hy'.1) (mulVec_mem_trivLat C (fun a b => ih b a)
        (mulVec_mem_trivLat C iS hy'.1)))
  · let r : VV K d →ₗ[K] Fin d → K := Matrix.toLin' r₁ ∘ₗ LinearMap.fst K _ _ +
      Matrix.toLin' r₂ ∘ₗ LinearMap.snd K _ _
    let s : (Fin d → K) →ₗ[K] VV K d := LinearMap.prod (-Matrix.toLin' s₁) (-Matrix.toLin' s₂)
    have hr : ∀ y, r y = r₁.mulVec y.1 + r₂.mulVec y.2 := fun y => by simp [r]
    have hs : ∀ z, s z = (-(s₁.mulVec z), -(s₂.mulVec z)) := fun z => by simp [s]
    refine ⟨r, s, fun y hy => ?_, fun z hz' => ?_, fun u => ?_, fun z => ?_, fun y => ?_⟩
    · have hy' := (mem_stdH C).1 hy
      rw [hr]
      exact add_mem (mulVec_mem_trivLat C ir₁ hy'.1) (mulVec_mem_trivLat C ir₂ hy'.2)
    · rw [hs]
      exact (mem_stdH C).2 ⟨neg_mem (mulVec_mem_trivLat C is₁ hz'),
        neg_mem (mulVec_mem_trivLat C is₂ hz')⟩
    · rw [hr, alpha_apply]
      simp only [Matrix.mulVec_mulVec, ← Matrix.add_mulVec, e₁, Matrix.one_mulVec]
    · have E : ((am B p - (hw B p).transpose * bil B.sy 1 1) * s₁).mulVec z -
          ((hw B p).transpose * s₂).mulVec z = z := by
        rw [← Matrix.sub_mulVec, e₂, Matrix.one_mulVec]
      rw [hs, beta_apply]
      simp only [Matrix.mulVec_neg, Matrix.mulVec_mulVec]
      calc _ = ((am B p - (hw B p).transpose * bil B.sy 1 1) * s₁).mulVec z -
          ((hw B p).transpose * s₂).mulVec z := by abel
        _ = z := E
    · have E₃ : (hw B p * r₁).mulVec y.1 +
          (s₁ * (am B p - (hw B p).transpose * bil B.sy 1 1)).mulVec y.1 = y.1 := by
        rw [← Matrix.add_mulVec, e₃, Matrix.one_mulVec]
      have E₄ : (hw B p * r₂).mulVec y.2 - (s₁ * (hw B p).transpose).mulVec y.2 = 0 := by
        rw [← Matrix.sub_mulVec, e₄, Matrix.zero_mulVec]
      have E₅ : ((am B p).transpose * r₁).mulVec y.1 +
          (s₂ * (am B p - (hw B p).transpose * bil B.sy 1 1)).mulVec y.1 = 0 := by
        rw [← Matrix.add_mulVec, e₅, Matrix.zero_mulVec]
      have E₆ : ((am B p).transpose * r₂).mulVec y.2 - (s₂ * (hw B p).transpose).mulVec y.2 = y.2 := by
        rw [← Matrix.sub_mulVec, e₆, Matrix.one_mulVec]
      rw [alpha_apply, hs, hr, beta_apply]
      refine Prod.ext ?_ ?_
      · simp only [Prod.fst_add, Matrix.mulVec_add, Matrix.mulVec_neg, Matrix.mulVec_sub,
          Matrix.mulVec_mulVec]
        calc _ = ((hw B p * r₁).mulVec y.1 +
              (s₁ * (am B p - (hw B p).transpose * bil B.sy 1 1)).mulVec y.1) +
            ((hw B p * r₂).mulVec y.2 - (s₁ * (hw B p).transpose).mulVec y.2) := by abel
          _ = y.1 := by rw [E₃, E₄, add_zero]
      · simp only [Prod.snd_add, Matrix.mulVec_add, Matrix.mulVec_neg, Matrix.mulVec_sub,
          Matrix.mulVec_mulVec]
        calc _ = (((am B p).transpose * r₁).mulVec y.1 +
              (s₂ * (am B p - (hw B p).transpose * bil B.sy 1 1)).mulVec y.1) +
            (((am B p).transpose * r₂).mulVec y.2 - (s₂ * (hw B p).transpose).mulVec y.2) := by abel
          _ = y.2 := by rw [E₅, E₆, zero_add]

theorem locSplit {p : ℕ} [Fact p.Prime] [CharP K p] (F : Family C p d O) (i : C.I) :
    LocSplit C i (alpha (F.BK i) p) (beta (F.BK i) p) := by
  haveI : CharP (C.v i).valuationSubring p :=
    (RingHom.charP_iff (C.v i).valuationSubring.subtype Subtype.val_injective p).2 inferInstance
  have mK := GlobalTheory.T.formal_data_base_change _ _ (C.v i).valuationSubring.subtype d O (F.Bi i) (F.BK i) (F.mapK i)
  have mk := GlobalTheory.T.formal_data_base_change _ _ (IsLocalRing.residue _) d O (F.Bi i) (F.Bk i) (F.mapk i)
  have iz : am (F.Bi i) p * hw (F.Bi i) p -
      (hw (F.Bi i) p).transpose * bil (F.Bi i).sy 1 1 * hw (F.Bi i) p -
      (hw (F.Bi i) p).transpose * (am (F.Bi i) p).transpose = 0 := by
    have h0 := matrix_eq_zero_of_mulVec (M := (hw (F.Bi i) p).transpose * (am (F.Bi i) p).transpose -
        am (F.Bi i) p * hw (F.Bi i) p +
        (hw (F.Bi i) p).transpose * bil (F.Bi i).sy 1 1 * hw (F.Bi i) p) fun u => by
      rw [← beta_alpha_apply]
      exact LinearMap.congr_fun (GlobalTheory.T.alpha_beta_adjoint_exact _ p d O (F.Bi i)).2 u
    rw [← neg_eq_zero, ← h0]
    abel
  have inj : ∀ u : Fin d → IsLocalRing.ResidueField (C.v i).valuationSubring,
      ((hw (F.Bi i) p).map (IsLocalRing.residue _)).mulVec u = 0 →
      ((am (F.Bi i) p).transpose.map (IsLocalRing.residue _)).mulVec u = 0 → u = 0 := by
    intro u h1 h2
    apply F.inj i
    rw [map_zero, alpha_apply, (mk.2.2 p).1, (mk.2.2 p).2, ← Matrix.transpose_map, h1, h2]
    rfl
  obtain ⟨r₁, r₂, s₁, s₂, e₁, e₂, e₃, e₄, e₅, e₆⟩ := GlobalTheory.T.local_matrix_coprime_decomposition _ d _ _ _ iz inj
  let Φ := (C.v i).valuationSubring.subtype.mapMatrix (m := Fin d)
  have hT : ∀ M, Φ M.transpose = (Φ M).transpose := fun M => rfl
  have hh : hw (F.BK i) p = Φ (hw (F.Bi i) p) := (mK.2.2 p).1
  have ha : am (F.BK i) p = Φ (am (F.Bi i) p) := (mK.2.2 p).2
  have hS : bil (F.BK i).sy 1 1 = Φ (bil (F.Bi i).sy 1 1) := mK.2.1
  have c₁ := congrArg Φ e₁
  have c₂ := congrArg Φ e₂
  have c₃ := congrArg Φ e₃
  have c₄ := congrArg Φ e₄
  have c₅ := congrArg Φ e₅
  have c₆ := congrArg Φ e₆
  simp only [map_add, map_sub, map_mul, map_one, map_zero, hT] at c₁ c₂ c₃ c₄ c₅ c₆
  refine locSplit_of_mats C (F.BK i) p i (Φ r₁) (Φ r₂) (Φ s₁) (Φ s₂) ?_ ?_ ?_
    (intM_map C i _) (intM_map C i _) (intM_map C i _) (intM_map C i _)
    (fun u => LinearMap.congr_fun (GlobalTheory.T.alpha_beta_adjoint_exact K p d O (F.BK i)).2 u) ?_ ?_ ?_ ?_ ?_ ?_
  · rw [hh]; exact intM_map C i _
  · rw [ha]; exact intM_map C i _
  · rw [hS]; exact intM_map C i _
  all_goals simp only [hh, ha, hS]
  exacts [c₁, c₂, c₃, c₄, c₅, c₆]

theorem rhoH_mem_stdH (i : C.I) (B₀ : FB (C.v i).valuationSubring d O) (B : FB K d O)
    (h : IsMapOf (C.v i).valuationSubring.subtype B₀ B) (a : O) {w : VV K d}
    (hw : w ∈ stdH C d i) : rhoH B a w ∈ stdH C d i := by
  obtain ⟨hm, -⟩ := GlobalTheory.T.formal_data_base_change _ _ (C.v i).valuationSubring.subtype d O B₀ B h
  have hr : ∀ b, IntM C i (rho B b) := fun b => by rw [(hm b).1]; exact intM_map C i _
  have ha : IntM C i (bil (B.ad a) 1 1) := by rw [(hm a).2]; exact intM_map C i _
  rw [mem_stdH] at hw ⊢
  rw [rhoH_apply]
  exact ⟨mulVec_mem_trivLat C (hr a) hw.1, sub_mem (mulVec_mem_trivLat C (fun x y => hr _ y x) hw.2)
    (mulVec_mem_trivLat C (fun x y => ha y x) hw.1)⟩

theorem family_conj : ∀ (K : Type) [Field K] (C : ACurve K) (p : ℕ) [Fact p.Prime] [CharP K p]
    (d : ℕ) (O : Type) [CommRing O] [StarRing O] (F : Family C p d O), Nonempty C.I →
    ∃ D : ConjData C p O d, (∀ a, D.ρ a = rho F.B a) ∧
      ∀ i u, u ∈ D.lie i ↔ ∀ j, C.v i ((lin (F.ψ i) 1).mulVec u j) ≤ 1 := by
  intro K _ C p _ _ d O _ _ F hI
  obtain ⟨ρ, hρ⟩ := GlobalTheory.T.formal_group_action_ring_hom K d O F.B
  obtain ⟨⟨ρH, hρH⟩, -, -⟩ := GlobalTheory.T.formal_hermitian_action_pairing K d O F.B
  have iso := fun i => GlobalTheory.T.formal_isomorphism_transport K d O F.B (F.BK i) (F.φ i) (F.ψ i) (F.lam i) (F.iso i)
  have h₁ := fun i => (iso i).1
  have h₂ := fun i => (iso i).2.1
  have hT := fun i => (iso i).2.2.1
  have hc := fun i => (iso i).2.2.2.2.1
  have good : ∀ i, (∀ a b, C.v i (lin (F.φ i) 1 a b) ≤ 1 ∧ C.v i (lin (F.ψ i) 1 a b) ≤ 1 ∧
      C.v i (bil (F.lam i) 1 1 a b) ≤ 1) → IntM C i (lin (F.φ i) 1) ∧ IntM C i (lin (F.ψ i) 1) ∧
        IntM C i (bil (F.lam i) 1 1) := fun i h =>
    ⟨fun a b => (h a b).1, fun a b => (h a b).2.1, fun a b => (h a b).2.2⟩
  have hiso := fun i => GlobalTheory.T.alpha_beta_isomorphism_transport K p d O F.B (F.BK i) (F.φ i) (F.ψ i) (F.lam i) (F.iso i)
  refine ⟨{ lie := fun i => colLat C i (lin (F.φ i) 1)
            H := fun i => imLat C i (transH (F.φ i) (F.ψ i) (F.lam i))
            lie_bun := isBun_colLat C _ _ h₁ h₂ (F.ae.subset fun i hi h => hi ?_)
            H_bun := isBun_imLat C _ hT (F.ae.subset fun i hi h => hi ?_)
            ρ := ρ
            ρH := ρH
            ρH_hom := fun a i x hx => ?_
            ρH_fst := fun a y => ?_
            ρH_inr := fun a φ => ?_
            hodge := hodge_family C _ _ _ h₁ h₂
            α := alpha F.B p
            β := beta F.B p
            conj := conj_family C p hI _ _ h₁ h₂ _ hT _ _ _ _ (fun i u => (hiso i).1 u)
              (fun i y => (hiso i).2 y) (fun i => locSplit C F i)
            α_act := fun a u => ?_
            β_act := fun a y => ?_ }, hρ, fun i u => mem_colLat_iff C (h₁ i) (h₂ i)⟩
  · exact ⟨(good i h).1, (good i h).2.1⟩
  · obtain ⟨g₁, g₂, g₃⟩ := good i h
    exact imLat_transH_eq C (h₁ i) (h₂ i) g₁ g₂ g₃
  · obtain ⟨w, hw, rfl⟩ := (mem_imLat C).1 hx
    rw [hρH]
    refine (mem_imLat C).2 ⟨rhoH (F.BK i) a w, rhoH_mem_stdH C i (F.Bi i) (F.BK i) (F.mapK i) a hw, ?_⟩
    exact (LinearMap.congr_fun (hc i a) w).symm
  · rw [hρH, rhoH_fst, hρ]
  · rw [hρH, rhoH_inr, hρ]
  · rw [hρ, hρH]
    exact GlobalTheory.T.alpha_equivariant_frobenius K p d O F.B a u
  · rw [hρ, hρH]
    exact GlobalTheory.T.beta_equivariant_frobenius K p d O F.B a y

end GlobalTheory.CompanionTheory.Ar.Conj.Fam
end
end
