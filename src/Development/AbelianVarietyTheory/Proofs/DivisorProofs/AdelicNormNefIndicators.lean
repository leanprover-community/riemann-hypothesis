import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemConeOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsComb
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InducesPl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeVolSlopeOfTendsto
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DegFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularLocalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularLocalImpliesGeometric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateConstantEverywhere
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanExistenceEverywhere
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLawsOfSignature
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntFrBelow
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.FieldTwistConditions
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteDvrExtension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistenceOfComparison
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComparisonStatementHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConnectingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenvalueStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHomogeneousPolysTangentBasis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointCountOfEigenCovolumeHypotheses
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoordinateSectionsOfWeight
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IoOfLeOneIff
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueLiesUnder
import Development.AbelianVarietyTheory.Definitions.Divisors.ReferenceMetricMulDualEqOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicDivisorInducedAdd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicDivisorInducedNeg

section
open NumberField IsDedekindDomain Filter Topology
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovHt.Link GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.Cartier GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace GlobalTheory.CovHt.Link

theorem exists_equiv_over : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (Φ : s.Flag), ∃ q : s.Comp ≃ Comp s.Xo κ.c, ∀ k, Over Φ k (q k) := by
  intro D A N j S κ s Φ
  obtain ⟨q, hq⟩ := GlobalTheory.ShFam.PtComp.exists_equiv s
  refine ⟨q, fun k => ?_⟩
  letI := (constF κ.e (Φ.C k).Y).toAlgebra
  intro t
  have hx : (GlobalTheory.AllWt.ptF (Φ.C k).y0 ≫ s.T.Z.jQ) t = (Φ.C k).π (genericPt (Φ.C k).Y t) := by
    rw [(Φ.C k).y0_x]; rfl
  have hon : OnComp s k ((Φ.C k).π (genericPt (Φ.C k).Y t)) := by
    obtain ⟨z, hz⟩ : ((s.U κ.σ₀).X k).dom.Nonempty := GlobalTheory.OrbitScalar.exists_mem_dom _
    refine ⟨⟨z, hz⟩, fun pt => ?_⟩
    exact (isPreconnected_range (Φ.C k).π.continuous).subset_connectedComponent ⟨_, rfl⟩
      (Φ.label k ⟨z, hz⟩ pt)
  have e := (hq k _).1 hon
  show GlobalTheory.AllWt.ptF (Φ.C k).y0 t ∈ ((q k : _) : Set _)
  rw [e]
  rw [Set.mem_preimage]
  have : s.T.Z.jQ (GlobalTheory.AllWt.ptF (Φ.C k).y0 t) = (GlobalTheory.AllWt.ptF (Φ.C k).y0 ≫ s.T.Z.jQ) t := rfl
  rw [this, hx]
  exact mem_connectedComponent

end GlobalTheory.CovHt.Link
end
end

section
open NumberField IsDedekindDomain Filter Topology
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovHt.Link GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.Cartier GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_components_biject_moduli_components : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (Φ : s.Flag), ∃ q : s.Comp ≃ Comp s.Xo κ.c, ∀ k, Over Φ k (q k) := by
  first | exact @GlobalTheory.CovHt.Link.exists_equiv_over | exact GlobalTheory.CovHt.Link.exists_equiv_over | (intros; apply GlobalTheory.CovHt.Link.exists_equiv_over <;> assumption)
end

section
open NumberField IsDedekindDomain GlobalTheory.ShFam.Pad

namespace GlobalTheory.PlaceSum

variable {F : Type} [Field F] [NumberField F]

theorem residueCharacteristic_eq_iff (v : HeightOneSpectrum (𝓞 F)) {p : ℕ} (hp : p.Prime) :
    resP v = p ↔ ((p : 𝓞 F) ∈ v.asIdeal) := by
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  unfold resP
  constructor
  · intro h
    have h0 : ((ringChar (𝓞 F ⧸ v.asIdeal) : ℕ) : 𝓞 F ⧸ v.asIdeal) = 0 := ringChar.Nat.cast_ringChar
    rw [h, ← map_natCast (Ideal.Quotient.mk v.asIdeal), Ideal.Quotient.eq_zero_iff_mem] at h0
    exact h0
  · intro h
    have h0 : (Ideal.Quotient.mk v.asIdeal (p : 𝓞 F)) = 0 := Ideal.Quotient.eq_zero_iff_mem.2 h
    rw [map_natCast] at h0
    have hd : ringChar (𝓞 F ⧸ v.asIdeal) ∣ p := ringChar.dvd h0
    rcases (Nat.dvd_prime hp).1 hd with h1 | h1
    · exact absurd h1 (CharP.ringChar_ne_one (R := 𝓞 F ⧸ v.asIdeal))
    · exact h1

theorem finprod_adicAbv {z : F} (hz : z ≠ 0) :
    (Function.mulSupport fun v : HeightOneSpectrum (𝓞 F) => HeightOneSpectrum.adicAbv F v z).Finite ∧
    ∏ᶠ v : HeightOneSpectrum (𝓞 F), HeightOneSpectrum.adicAbv F v z =
      |((Algebra.norm ℚ z : ℚ) : ℝ)|⁻¹ := by
  have hfun : (fun v : HeightOneSpectrum (𝓞 F) => HeightOneSpectrum.adicAbv F v z) =
      (fun w : FinitePlace F => w z) ∘ FinitePlace.equivHeightOneSpectrum.symm := by
    funext v
    simp [FinitePlace.equivHeightOneSpectrum_symm_apply, FinitePlace.norm_embedding]
  refine ⟨?_, ?_⟩
  · rw [hfun, Function.mulSupport_comp_eq_preimage]
    exact (FinitePlace.hasFiniteMulSupport hz).preimage
      FinitePlace.equivHeightOneSpectrum.symm.injective.injOn
  · rw [hfun]
    refine (finprod_comp_equiv (FinitePlace.equivHeightOneSpectrum (K := F)).symm
      (f := fun w : FinitePlace F => w z)).trans ?_
    rw [FinitePlace.prod_eq_inv_abs_norm hz]
    push_cast; rfl

theorem adicAbv_natCast_ne_one_iff (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) :
    HeightOneSpectrum.adicAbv F v (n : F) ≠ 1 ↔ (n : 𝓞 F) ∈ v.asIdeal := by
  have e : (n : F) = algebraMap (𝓞 F) F (n : 𝓞 F) := (map_natCast _ n).symm
  rw [e, Ne, ← not_not (a := (n : 𝓞 F) ∈ v.asIdeal)]
  exact not_congr (v.adicAbv_coe_eq_one_iff (HeightOneSpectrum.one_lt_absNorm_nnreal v) _)

theorem finite_mulSupport_adicAbv_natCast {p : ℕ} (hp : p.Prime) :
    (Function.mulSupport fun v : HeightOneSpectrum (𝓞 F) => HeightOneSpectrum.adicAbv F v (p : F)).Finite :=
  (finprod_adicAbv (z := (p : F)) (by exact_mod_cast hp.ne_zero)).1

theorem mem_finite_residueChar_eq {p : ℕ} (hp : p.Prime) (v : HeightOneSpectrum (𝓞 F)) :
    v ∈ (finite_mulSupport_adicAbv_natCast (F := F) hp).toFinset ↔ resP v = p := by
  rw [Set.Finite.mem_toFinset, Function.mem_mulSupport, adicAbv_natCast_ne_one_iff, residueCharacteristic_eq_iff v hp]

theorem sum_localDeg_eq {p : ℕ} (hp : p.Prime) :
    ∑ v ∈ (finite_mulSupport_adicAbv_natCast (F := F) hp).toFinset,
      -Real.log (HeightOneSpectrum.adicAbv F v (p : F)) / Real.log p = (Module.finrank ℚ F : ℝ) := by
  have hp0 : (p : F) ≠ 0 := by exact_mod_cast hp.ne_zero
  obtain ⟨hfin, hprod⟩ := finprod_adicAbv (F := F) hp0
  rw [finprod_eq_prod _ hfin] at hprod
  have hN : Algebra.norm ℚ (p : F) = (p : ℚ) ^ Module.finrank ℚ F := by
    rw [← map_natCast (algebraMap ℚ F) p, Algebra.norm_algebraMap]
  rw [hN] at hprod
  push_cast at hprod
  have hne : ∀ v ∈ hfin.toFinset, HeightOneSpectrum.adicAbv F v (p : F) ≠ 0 :=
    fun v _ => (AbsoluteValue.ne_zero_iff _).2 hp0
  have hlog := congrArg Real.log hprod
  rw [Real.log_prod hne, abs_of_nonneg (by positivity), Real.log_inv, Real.log_pow] at hlog
  have hlp : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  rw [← Finset.sum_div, Finset.sum_neg_distrib, hlog, neg_neg, mul_div_assoc, div_self hlp.ne', mul_one]

theorem sum_localDeg_le : ∀ {F : Type} [Field F] [NumberField F] (T : Finset ℕ), (∀ p ∈ T, p.Prime) →
    ∀ (g : ℕ → ℝ), (∀ p, 0 ≤ g p) →
    (∀ v : HeightOneSpectrum (𝓞 F), NumberField.HeightOneSpectrum.adicAbv F v (resP v : F) ≤ 1) ∧
    ∃ S : Finset (HeightOneSpectrum (𝓞 F)), (∀ v, v ∈ S ↔ resP v ∈ T) ∧
      ∑ v ∈ S, (-Real.log (NumberField.HeightOneSpectrum.adicAbv F v (resP v : F)) / Real.log (resP v)) * g (resP v) ≤
        (Module.finrank ℚ F : ℝ) * ∑ p ∈ T, g p := by
  intro F _ _ T hT g _
  classical
  refine ⟨fun v => HeightOneSpectrum.adicAbv_natCast_le_one F v _, ?_⟩
  let Sp : ℕ → Finset (HeightOneSpectrum (𝓞 F)) := fun p =>
    if h : p.Prime then (finite_mulSupport_adicAbv_natCast (F := F) h).toFinset else ∅
  have hSp : ∀ p ∈ T, ∀ v, v ∈ Sp p ↔ resP v = p := by
    intro p hpT v
    simp only [Sp, dif_pos (hT p hpT)]
    exact mem_finite_residueChar_eq (hT p hpT) v
  let S := T.biUnion Sp
  have hS : ∀ v, v ∈ S ↔ resP v ∈ T := by
    intro v
    simp only [S, Finset.mem_biUnion]
    constructor
    · rintro ⟨p, hpT, hv⟩
      rw [(hSp p hpT v).1 hv]; exact hpT
    · intro h
      exact ⟨resP v, h, (hSp _ h v).2 rfl⟩
  refine ⟨S, hS, le_of_eq ?_⟩
  rw [← Finset.sum_fiberwise_of_maps_to (g := resP) (t := T) (fun v hv => (hS v).1 hv), Finset.mul_sum]
  refine Finset.sum_congr rfl fun p hpT => ?_
  have hfib : S.filter (fun v => resP v = p) = (finite_mulSupport_adicAbv_natCast (F := F) (hT p hpT)).toFinset := by
    ext v
    rw [Finset.mem_filter, mem_finite_residueChar_eq (hT p hpT), hS]
    constructor
    · exact fun h => h.2
    · intro h; exact ⟨h ▸ hpT, h⟩
  rw [hfib]
  have hc : ∀ v ∈ (finite_mulSupport_adicAbv_natCast (F := F) (hT p hpT)).toFinset,
      (-Real.log (HeightOneSpectrum.adicAbv F v (resP v : F)) / Real.log (resP v)) * g (resP v) =
        (-Real.log (HeightOneSpectrum.adicAbv F v (p : F)) / Real.log p) * g p := by
    intro v hv
    rw [(mem_finite_residueChar_eq (hT p hpT) v).1 hv]
  rw [Finset.sum_congr rfl hc, ← Finset.sum_mul, sum_localDeg_eq (hT p hpT), mul_comm]

end GlobalTheory.PlaceSum
end

section
open GlobalTheory.DetHT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.RegularLocalStatement : RegLocSt := by
  first | exact @GlobalTheory.DetHT.RegLoc.main | exact GlobalTheory.DetHT.RegLoc.main | (intros; apply GlobalTheory.DetHT.RegLoc.main <;> assumption)
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain
open scoped NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory.DetHT.AnyLev

theorem at_one (hP : GlobalTheory.CovTop.Hypotheses2) (E : Type) [Field E] [NumberField E] [IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l)
    (hpq : 1 ≤ Dw.p + Dw.q) (hA : l.A = 1) (hg : ∀ q : ℕ, q.Prime → l.GoodAt q) (h1 : ∃ D₁ : Datum H, D₁.p = 1 ∧ D₁.q = 0)
    (hC : GlobalTheory.CompRat.CurveOver H c.F l.M') (Zc : Formalism.L2.Pj.Comp Xo c) (τ : Psi H) :
    ∃ f ∈ secZ Xo c (exOf Dw (flatWt Dw τ) 0),
      ∀ la : HeightOneSpectrum (𝓞 c.F), ∃ ρ : ℝ, ∀ w ∈ htValOn Zc la, w f = (ρ : EReal) := by
  have hF : FnAlgClosed Xo c := GlobalTheory.ShFam.GeomComp.fnAlgClosed_of_curveOver Xo c hpq h1 hC
  obtain ⟨U, hL⟩ := GlobalTheory.FlatCore.Model.exists_laws Dw l Xo c hpq hA hg hF h1
  obtain ⟨s⟩ := GlobalTheory.FlatCore.archEx_always E H Dw l Xo c _ U _ hL Zc τ
  refine ⟨s.sig, s.sig_mem, fun la => ?_⟩
  exact GlobalTheory.FlatCore.htConst_always hP hP.q2 hP.q3 hP.q4 E H Dw l Xo c _ U _ hL Zc τ s la

section Down

open GlobalTheory.CovPull

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {n : ℕ} (d : DeltaDat Xo c n)

theorem pullRule_mem_secZ (hO : GlobalTheory.ClsVal.Cmp.OverBase d) (hK : KA l ≤ KA d.l₂) {e : Ix Dw → ℤ}
    {f : Rul Xo c} (hf : f ∈ secZ Xo c e) : pullRule d f ∈ secZ d.Xo₂ d.c₂ e := by
  refine ⟨fun p q φ u u' hm => ?_, fun p t u u' hb => ?_⟩
  · letI := algDn d p.R
    letI := algDn d q.R
    obtain ⟨y, hy⟩ := below_exists d hO hK (S := p.R) (fun _ => rfl) u
    obtain ⟨y', hy'⟩ := below_exists d hO hK (S := q.R) (fun _ => rfl) u'
    let φc : p.R →ₐ[c.F] q.R := ⟨φ.toRingHom, fun a => φ.commutes (d.eF a)⟩
    obtain ⟨w, hw⟩ := GlobalTheory.TransferCompare.frBC_framed Xo c p.R q.R φc y
    have hw' : FrOver d u' w := GlobalTheory.FrameLift.frOver_map d (ψ := φc) (ψ₂ := φ) rfl hy hw hm
    obtain rfl : y' = w := GlobalTheory.ClassSumCompare.frUnder_unique d hy' hw'
    show pullRule d f q u' = φ (pullRule d f p u)
    rw [pullRule_eq d f q u' y' hy', pullRule_eq d f p u y hy]
    exact GlobalTheory.SupLawProbe.evR_map (GlobalTheory.TransferCompare.evalWD_framed Xo c) f hf.1 φc y
      (GlobalTheory.TransferCompare.allTest_framed Xo c p.R y) y' hw
  · letI := algDn d p.R
    obtain ⟨y, hy⟩ := below_exists d hO hK (S := p.R) (fun _ => rfl) u
    obtain ⟨y', hy'⟩ := below_exists d hO hK (S := p.R) (fun _ => rfl) u'
    show pullRule d f p u' = _ * pullRule d f p u
    rw [pullRule_eq d f p u' y' hy', pullRule_eq d f p u y hy]
    exact GlobalTheory.evR_frBor_of_mem_secZ GlobalTheory.abelianSchemeLaws_all.1.secBaseChange Xo c e hf p.R t y y' (frBor_down d hy hy' hb)

theorem evR_pullRule_nat (hO : GlobalTheory.ClsVal.Cmp.OverBase d) (hK : KA l ≤ KA d.l₂) {f : Rul Xo c}
    (hf : IsNatural (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) f)
    {k : Type} [Field k] [Algebra c.F k] [Algebra d.c₂.F k]
    (hc : ∀ a : c.F, algebraMap d.c₂.F k (d.eF a) = algebraMap c.F k a) (y₂ : FrPt d.Xo₂ d.c₂ k) (y : FrPt Xo c k)
    (hy : FrOver d y₂ y) : evR d.Xo₂ d.c₂ (pullRule d f) y₂ = evR Xo c f y := by
  have key : ∀ (p : TRing d.c₂.F) (φ : p.R →ₐ[d.c₂.F] k) (u : FrPt d.Xo₂ d.c₂ p.R), FrMap φ u y₂ →
      φ (pullRule d f p u) = evR Xo c f y := by
    intro p φ u hu
    letI := algDn d p.R
    obtain ⟨z, hz⟩ := below_exists d hO hK (S := p.R) (fun _ => rfl) u
    let φc : p.R →ₐ[c.F] k := ⟨φ.toRingHom, fun a => (φ.commutes (d.eF a)).trans (hc a)⟩
    obtain ⟨w, hw⟩ := GlobalTheory.TransferCompare.frBC_framed Xo c p.R k φc z
    have hw' : FrOver d y₂ w := GlobalTheory.FrameLift.frOver_map d (ψ := φc) (ψ₂ := φ) rfl hz hw hu
    obtain rfl : y = w := GlobalTheory.ClassSumCompare.frUnder_unique d hy hw'
    rw [pullRule_eq d f p u z hz]
    exact (GlobalTheory.SupLawProbe.evR_map (GlobalTheory.TransferCompare.evalWD_framed Xo c) f hf φc z
      (GlobalTheory.TransferCompare.allTest_framed Xo c p.R z) y hw).symm
  have hT := GlobalTheory.TransferCompare.allTest_framed d.Xo₂ d.c₂ k y₂
  have e : evR d.Xo₂ d.c₂ (pullRule d f) y₂ =
      hT.choose_spec.choose (pullRule d f hT.choose hT.choose_spec.choose_spec.choose) := by
    unfold evR evalAt
    rw [dif_pos hT]
  rw [e]
  exact key _ _ _ hT.choose_spec.choose_spec.choose_spec

variable {p : ℕ} [Fact p.Prime] {C : Type} [Field C] {v : Valuation C ℝ≥0} {O : Type} [CommRing O] [Algebra O C]
  [StarRing (𝓞 E)]

theorem pointOver_down {P : Point p v O (𝓞 E)} {V F : Type} [CommRing V] [Field F] [Algebra V F]
    {x₂ : Sp F ⟶ d.Xo₂.X} {x : Sp F ⟶ Xo.X} (e : x₂ ≫ d.r = x) {k : F →+* C} {kO : V →+* O}
    {ψ : P.A.A.left ⟶ d.Xo₂.univ.t.G.left} (h : PointOver P x₂ k kO ψ) : PointOver P x k kO (ψ ≫ d.m.φ) := by
  obtain ⟨h0, G, t', m₁, m₂, π, φ, h1, h2, h3, h4, h5, h6⟩ := h
  obtain ⟨m', e₁⟩ := LiftBaseChange.exists_comp' d.m m₁ x e.symm
  refine ⟨h0, G, t', m', m₂, π, φ, h1, h2, h3, h4, by rw [e₁, ← Category.assoc, h5], ?_⟩
  obtain ⟨w, hw, -⟩ := d.m.lin
  have i : LBIso (d.Xo₂.univ.t.PP.L.pull ψ) (Xo.univ.t.PP.L.pull (ψ ≫ d.m.φ)) :=
    LBIso.chartPull (Geo.Tor.chartPullPull _ ψ ψ rfl)
      (chartPullSame Xo.univ.t.PP.L _ _ _ ψ fun _ => rfl) (⟨w, hw⟩ : LBIso d.Xo₂.univ.t.PP.L (Xo.univ.t.PP.L.pull d.m.φ))
  exact LBIso.trans P.A.isLB (LB.isLB_pull d.Xo₂.univ.t.PP.isLB _) (LB.isLB_pull Xo.univ.t.PP.isLB _) h6 i

variable [Algebra c.F C] [Algebra d.c₂.F C] [IsAlgClosed C] [CharZero C] [Algebra ℤ_[p] C] [Algebra ℤ_[p] O]
  [IsScalarTower ℤ_[p] O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O]

omit [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] in

theorem htLat_eq (hc : ∀ a : c.F, algebraMap d.c₂.F C (d.eF a) = algebraMap c.F C a) (P : Point p v O (𝓞 E))
    (τ : E →+* ℂ) : htLat d.c₂ P τ = htLat c P τ := by
  have e : embAt d.c₂ C τ = embAt c C τ := RingHom.ext fun a => by
    unfold embAt
    rw [RingHom.comp_apply, RingHom.comp_apply, ← hc]
    exact congrArg _ (Subtype.ext rfl)
  unfold htLat embInt
  rw [e]

theorem isHTChange_down (hc : ∀ a : c.F, algebraMap d.c₂.F C (d.eF a) = algebraMap c.F C a) {P : Point p v O (𝓞 E)}
    {ψ : P.A.A.left ⟶ d.Xo₂.univ.t.G.left} {z₂ y₂ : FrPt d.Xo₂ d.c₂ C} {z y : FrPt Xo c C} (hz : FrOver d z₂ z)
    (hy : FrOver d y₂ y) (h : IsHTChange P ψ z₂ y₂) : IsHTChange P (ψ ≫ d.m.φ) z y := by
  obtain ⟨t, hb, ht⟩ := h.exists_frBor
  obtain ⟨ex, -, pm, q₁, q₂, q₃⟩ := frBor_down d hz hy hb
  obtain ⟨g, a, x, ⟨h1, h2, -⟩, hg, -, hL, hB⟩ := h
  refine ⟨g, t none, x, ⟨ex, fun τ i => ?_, pm, q₁, ?_, q₃⟩, hg, ht, fun τ j => ?_, fun τ => ?_⟩
  · have := (GlobalTheory.FrameLift.comb_iff d.m hz.1 (fun j => (z₂.tan τ j).1) (g τ i) (h1 ▸ (y₂.tan τ i).1)).1 (h2 τ i)
    rw [funext (hz.2.1 τ), hy.2.1] at this
    exact this
  · rw [q₂, show spMap (RingHom.id C) = 𝟙 _ from Spec.map_id _]
    exact (Category.comp_id _).symm
  · obtain ⟨xG, u', k₁, k₂, k₃⟩ := hL τ j
    exact ⟨xG, u', k₁, by rw [← Category.assoc, k₂, hz.2.1], k₃⟩
  · rw [← htLat_eq d hc]
    exact hB τ

theorem isHTFrame_down (hO : GlobalTheory.ClsVal.Cmp.OverBase d) (hK : KA l ≤ KA d.l₂)
    (hc : ∀ a : c.F, algebraMap d.c₂.F C (d.eF a) = algebraMap c.F C a) {T : CDVR} {io : c.F →+* T.Fr}
    {io₂ : d.c₂.F →+* T.Fr} {b₂ : IntFr d.Xo₂ d.c₂ T io₂} {b : IntFr Xo c T io}
    (hb : letI := io.toAlgebra; letI := io₂.toAlgebra; FrOver d b₂.1 b.1)
    {k₂ : letI := io₂.toAlgebra; T.Fr →ₐ[d.c₂.F] C} {k : letI := io.toAlgebra; T.Fr →ₐ[c.F] C}
    (hk : letI := io.toAlgebra; letI := io₂.toAlgebra; k₂.toRingHom = k.toRingHom) {y₂ : FrPt d.Xo₂ d.c₂ C}
    (h : IsHTFrame p v O b₂ k₂ y₂) : ∃ y : FrPt Xo c C, FrOver d y₂ y ∧ IsHTFrame p v O b k y := by
  letI := io.toAlgebra
  letI := io₂.toAlgebra
  obtain ⟨-, kO, P, ψ, z₂, h1, h2, h3⟩ := h
  obtain ⟨y, hy⟩ := below_exists d hO hK hc y₂
  obtain ⟨z, hz⟩ := GlobalTheory.TransferCompare.frBC_framed Xo c T.Fr C k b.1
  have hz' : FrOver d z₂ z := GlobalTheory.FrameLift.frOver_map d (ψ := k) (ψ₂ := k₂) hk hb hz h2
  refine ⟨y, hy, GlobalTheory.TransferCompare.allTest_framed Xo c C y, kO, P, ψ ≫ d.m.φ, z, ?_, hz,
    isHTChange_down d hc hz' hy h3⟩
  rw [← hk]
  exact pointOver_down d hb.1 h1

end Down

section Transfer

open GlobalTheory.CovPull

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {n : ℕ} (d : DeltaDat Xo c n)

theorem liesOn_down (rF : d.Xo₂.XF d.c₂ ⟶ Xo.XF c)
    (e₁ : rF ≫ pullback.fst _ _ = pullback.fst _ _ ≫ d.r)
    (e₂ : rF ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap (d.eF : c.F →+* d.c₂.F))
    {Z₂ : Formalism.L2.Pj.Comp d.Xo₂ d.c₂} {Z : Formalism.L2.Pj.Comp Xo c} (hZ : rF '' (Z₂ : Set (d.Xo₂.XF d.c₂)) ⊆ (Z : Set (Xo.XF c)))
    {S : Type} [CommRing S] [Algebra c.F S] [Algebra d.c₂.F S]
    (hc : ∀ a : c.F, algebraMap d.c₂.F S (d.eF a) = algebraMap c.F S a) {y₂ : FrPt d.Xo₂ d.c₂ S} {y : FrPt Xo c S}
    (hy : FrOver d y₂ y) (h : LiesOn Z₂ y₂) : LiesOn Z y := by
  have e : ptF y = ptF y₂ ≫ rF := by
    apply pullback.hom_ext
    · rw [Category.assoc, e₁, ptF, ptF, pullback.lift_fst, pullback.lift_fst_assoc, hy.1]
    · rw [Category.assoc, e₂, ptF, ptF, pullback.lift_snd, pullback.lift_snd_assoc,
        ← LiftBaseChange.spMap_comp']
      exact congrArg spMap (RingHom.ext fun a => (hc a).symm)
  intro s
  rw [e]
  exact hZ ⟨_, h s, rfl⟩

theorem htValOn_down (hO : GlobalTheory.ClsVal.Cmp.OverBase d) (hK : KA l ≤ KA d.l₂) (rF : d.Xo₂.XF d.c₂ ⟶ Xo.XF c)
    (e₁ : rF ≫ pullback.fst _ _ = pullback.fst _ _ ≫ d.r)
    (e₂ : rF ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap (d.eF : c.F →+* d.c₂.F))
    {Z₂ : Formalism.L2.Pj.Comp d.Xo₂ d.c₂} {Z : Formalism.L2.Pj.Comp Xo c} (hZ : rF '' (Z₂ : Set (d.Xo₂.XF d.c₂)) ⊆ (Z : Set (Xo.XF c)))
    {la₂ : HeightOneSpectrum (𝓞 d.c₂.F)} {la : HeightOneSpectrum (𝓞 c.F)} (hla : ∀ a : c.F, vLa la₂ (d.eF a) = vLa la a)
    {f : Rul Xo c} (hf : IsNatural (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) f) :
    ∀ w₂ ∈ htValOn Z₂ la₂, ∃ w ∈ htValOn Z la, w₂ (pullRule d f) = w f := by
  rintro _ ⟨T, io₂, e, b₂, ho, ⟨halg, hon⟩, p, hp, ha₂, k₂, y₂, hy₂, rfl⟩
  letI := io₂.toAlgebra
  let io : c.F →+* T.Fr := io₂.comp (d.eF : c.F →+* d.c₂.F)
  letI := io.toAlgebra
  letI : Algebra c.F ℂ_[p] := algDn d ℂ_[p]
  obtain ⟨b, hb⟩ := below_exists d hO hK (S := T.Fr) (fun _ => rfl) b₂.1
  let bI : IntFr Xo c T io := ⟨b, GlobalTheory.TransferCompare.allTest_framed Xo c T.Fr b,
    GlobalTheory.CoverDown.integral_below d T _ io₂ (fun _ => rfl) b b₂.1 hb b₂.2.2⟩
  let k : T.Fr →ₐ[c.F] ℂ_[p] := ⟨k₂.toRingHom, fun a => k₂.commutes (d.eF a)⟩
  letI := H.starRing
  obtain ⟨y, hy, hF⟩ := isHTFrame_down d hO hK (C := ℂ_[p]) (fun _ => rfl) (b := bI) (k := k) hb rfl hy₂
  refine ⟨_, ⟨T, io, e, bI, ⟨ho.1, fun a => (ho.2 (d.eF a)).trans (by rw [hla])⟩,
    ⟨halg, liesOn_down d rF e₁ e₂ hZ (fun _ => rfl) hb hon⟩, p, hp, inferInstance, k, y, hF, rfl⟩, ?_⟩
  show val_vw la₂ p _ _ = val_vw la p _ _
  rw [evR_pullRule_nat d hO hK hf (fun _ => rfl) y₂ y hy]
  have hp' : vLa la₂ (p : d.c₂.F) = vLa la (p : c.F) := by rw [← hla, map_natCast]
  unfold val_vw
  rw [hp']

end Transfer

theorem anyLev (hP : GlobalTheory.CovTop.Hypotheses2) : AnyLevSt := by
  intro E _ _ _ H Dw l Xo c hpq hg h1 hC Zc τ
  let l₀ : Level H := { l with A := 1, A_pos := Nat.one_pos }
  have hd : l₀.Dvd l := ⟨dvd_rfl, le_rfl, one_dvd _⟩
  have hM : l₀.M' ∣ l.M' := Nat.lcm_dvd (Nat.dvd_lcm_left _ _) (one_dvd _)
  have hK : KA l₀ ≤ KA l := GlobalTheory.Models.RankZero.KA_le_of_eq_one rfl l
  have hpos : 0 < l.M' := GlobalTheory.LevelExist.M'_pos l
  let c₀ : Coeff l₀ :=
    { F := c.F
      fin := c.fin
      conj := c.conj
      zeta_mem := by
        obtain ⟨e, he⟩ := GlobalTheory.LevelExist.zeta_eq_pow_of_dvd hpos hM
        rw [he]
        exact pow_mem c.zeta_mem e
      le := hK.trans c.le }
  have hC₀ : GlobalTheory.CompRat.CurveOver H c₀.F l₀.M' := by
    obtain ⟨k, hk⟩ := hM
    refine GlobalTheory.IndefiniteRowSideFullHecke.FieldTwistConditions.curveOver_of_mul (k := k) ?_ (hk ▸ hC)
    rintro rfl
    omega
  obtain ⟨Xo₀⟩ := GlobalTheory.Moduli.moduli_scheme_exists E H Dw l₀ hpq
  obtain ⟨r, jK, m, hj, hr, -, -, -, hcF⟩ := (GlobalTheory.moduliScheme_levelMaps_heckePoints.2 E H Dw hpq).1 l₀ l Xo₀ Xo hd
  obtain ⟨rF, e₁, e₂, -⟩ := hcF c₀ c rfl
  let d : DeltaDat Xo₀ c₀ 0 := ⟨1, ⊤, l, Xo, c, rfl, r, m, fun _ _ _ _ => 0, 0, 0⟩
  have hO : GlobalTheory.ClsVal.Cmp.OverBase d := fun h => by
    rw [← GlobalTheory.ClsVal.Cmp.eq_incl h jK hj]
    exact hr
  obtain ⟨Z₀, hZ₀, hZ⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible _
    (Zc.2.1.image rF rF.continuous.continuousOn)
  obtain ⟨f, hf, hρ⟩ := at_one hP E H Dw l₀ Xo₀ c₀ hpq rfl hg h1 hC₀ ⟨Z₀, hZ₀⟩ τ
  refine ⟨GlobalTheory.CovPull.pullRule d f, pullRule_mem_secZ d hO hK hf, fun la => ?_⟩
  obtain ⟨ρ, hρ⟩ := hρ la
  refine ⟨ρ, fun w hw => ?_⟩
  obtain ⟨w₀, hw₀, e⟩ := htValOn_down d hO hK rF e₁ e₂ (Z₂ := Zc) (Z := ⟨Z₀, hZ₀⟩) hZ (la₂ := la) (la := la)
    (fun _ => rfl) hf.1 w hw
  exact e.trans (hρ w₀ hw₀)

end GlobalTheory.DetHT.AnyLev

end
end

open GlobalTheory.DetHT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.anyLevSt_of_covering : GlobalTheory.CovTop.Hypotheses2 → AnyLevSt := by
  atlas_forward_decl GlobalTheory.DetHT.AnyLev.anyLev
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj

namespace GlobalTheory.DetHT.TestPt

theorem spm_spm {R S S' : Type} [CommRing R] [CommRing S] [CommRing S'] (φ : R →+* S) (ψ : S →+* S') :
    spMap ψ ≫ spMap φ = spMap (ψ.comp φ) := by
  rw [← Spec.map_comp]; rfl

theorem exists_chart {X : Scheme.{0}} {K : Type} [Field K] (z : Sp K ⟶ X) :
    ∃ (R : Type) (_ : CommRing R) (ξ : Sp R ⟶ X) (φ : R →+* K), IsOpenImmersion ξ ∧ spMap φ ≫ ξ = z := by
  obtain ⟨q⟩ : Nonempty (Sp K) := inferInstance
  obtain ⟨_, ⟨U, hU, rfl⟩, hq, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (z q)) isOpen_univ
  have hU' : IsAffineOpen U := hU
  have hr : Set.range z ⊆ Set.range hU'.fromSpec := by
    rw [hU'.range_fromSpec]
    rintro _ ⟨q', rfl⟩
    have : q' = q := Subsingleton.elim (α := PrimeSpectrum K) _ _
    rw [this]; exact hq
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (IsOpenImmersion.lift hU'.fromSpec z hr : Sp K ⟶ Spec Γ(X, U))
  refine ⟨Γ(X, U), inferInstance, hU'.fromSpec, φ.hom, inferInstance, ?_⟩
  have : spMap φ.hom = IsOpenImmersion.lift hU'.fromSpec z hr := hφ
  rw [this]
  exact IsOpenImmersion.lift_fac _ _ _

theorem exists_finite_subfield {R F C : Type} [CommRing R] [Algebra.FiniteType ℤ R] [Field F] [CharZero F] [Field C]
    [Algebra F C] {K : Type} [Field K] (k : K →+* C) (hK : ∀ a : K, IsAlgebraic ℤ a) (φ₀ : R →+* K) :
    ∃ L : IntermediateField F C, FiniteDimensional F L ∧ ∀ a, (k.comp φ₀) a ∈ L := by
  have hφ : ∀ a, IsAlgebraic ℤ ((k.comp φ₀) a) := fun a => (hK (φ₀ a)).algHom k.toIntAlgHom
  generalize k.comp φ₀ = φ at hφ ⊢
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := ℤ) (A := R)
  refine ⟨IntermediateField.adjoin F (φ '' (s : Set R)), ?_, fun a => ?_⟩
  · haveI : Finite (φ '' (s : Set R)) := (s.finite_toSet.image φ).to_subtype
    refine IntermediateField.finiteDimensional_adjoin ?_
    rintro _ ⟨a, -, rfl⟩
    exact ((hφ a).extendScalars (S := F) (algebraMap ℤ F).injective_int).isIntegral
  · have ha : a ∈ Algebra.adjoin ℤ (s : Set R) := by rw [hs]; trivial
    induction ha using Algebra.adjoin_induction with
    | mem x hx => exact IntermediateField.subset_adjoin _ _ ⟨x, hx, rfl⟩
    | algebraMap r => simp
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy

theorem exists_extend {X B : Scheme.{0}} (f : X ⟶ B) (hp : IsProper f) {V : Type} [CommRing V] [IsDomain V]
    [ValuationRing V] (y : Sp (FractionRing V) ⟶ X) (s : Sp V ⟶ B)
    (h : y ≫ f = spMap (algebraMap V (FractionRing V)) ≫ s) :
    ∃ χ : Sp V ⟶ X, y = spMap (algebraMap V (FractionRing V)) ≫ χ := by
  have hv : ValuativeCriterion f := by
    rw [IsProper.eq_valuativeCriterion] at hp
    exact hp.1.1.1
  let S : ValuativeCommSq f := { R := V, K := FractionRing V, i₁ := y, i₂ := s, commSq := ⟨h⟩ }
  obtain ⟨U⟩ := hv S
  exact ⟨U.default.l, U.default.fac_left.symm⟩

theorem exists_integral_point {A : Type} [CommRing A] [Module.Finite ℤ A] {X : Scheme.{0}} (s : X ⟶ Sp A)
    (hs : IsProper s) (p : ℕ) [Fact p.Prime] {K : Type} [Field K] (k : K →+* ℂ_[p]) (hK : ∀ a : K, IsAlgebraic ℤ a)
    (z : Sp K ⟶ X) :
    ∃ (T : CDVR) (kO : T.V →+* 𝓞_ℂ_[p]) (yT : Sp T.V ⟶ X), T.FinRes ∧ Function.Injective kO ∧
      spMap (algebraMap 𝓞_ℂ_[p] ℂ_[p]) ≫ spMap kO ≫ yT = spMap k ≫ z := by
  obtain ⟨R, _, ξ, φ, hξ, rfl⟩ := exists_chart z
  let f : A →+* R := (Spec.preimage (ξ ≫ s)).hom
  have hf : spMap f = ξ ≫ s := Spec.map_preimage (ξ ≫ s)
  letI : Algebra A R := f.toAlgebra
  haveI : Algebra.FiniteType A R := by
    have h : LocallyOfFiniteType (ξ ≫ s) := inferInstance
    rw [← Spec.map_preimage (ξ ≫ s)] at h
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).1 h
  haveI : Algebra.FiniteType ℤ R := Algebra.FiniteType.trans (S := A) inferInstance inferInstance
  let T₀ : CDVR := ⟨ℤ_[p]⟩
  have hT₀ : T₀.FinRes := Finite.of_equiv (ZMod p) (PadicInt.residueField (p := p)).symm.toEquiv
  let g₀ : ℤ_[p] →+* ℂ_[p] := (algebraMap ℚ_[p] ℂ_[p]).comp (algebraMap ℤ_[p] ℚ_[p])
  have hg₀ : ∀ a, g₀ a ∈ 𝓞_ℂ_[p] := fun a => by
    rw [GlobalTheory.CdvrLiftCp.mem_int_iff']
    show ‖algebraMap ℚ_[p] ℂ_[p] (a : ℚ_[p])‖ ≤ 1
    rw [norm_algebraMap']
    exact a.2
  have hg₀i : Function.Injective g₀ :=
    (algebraMap ℚ_[p] ℂ_[p]).injective.comp (IsFractionRing.injective ℤ_[p] ℚ_[p])
  let kO₀ : T₀.V →+* 𝓞_ℂ_[p] := g₀.codRestrict 𝓞_ℂ_[p] hg₀
  let k₀ : T₀.Fr →+* ℂ_[p] := IsFractionRing.lift (A := ℤ_[p]) (K := FractionRing ℤ_[p]) hg₀i
  have hk₀ : ∀ a, algebraMap 𝓞_ℂ_[p] ℂ_[p] (kO₀ a) = k₀ (algebraMap T₀.V T₀.Fr a) := fun a =>
    (IsFractionRing.lift_algebraMap (A := ℤ_[p]) (K := FractionRing ℤ_[p]) hg₀i a).symm
  letI : Algebra T₀.Fr ℂ_[p] := k₀.toAlgebra
  haveI : CharZero T₀.Fr := algebraRat.charZero _
  obtain ⟨L, hL, hmem⟩ := exists_finite_subfield (F := T₀.Fr) k hK φ
  let φL : R →+* L := (k.comp φ).codRestrict L hmem
  let kL : L →+* ℂ_[p] := L.val.toRingHom
  have hφL : kL.comp φL = k.comp φ := rfl
  obtain ⟨T', -, -, ψ, kO', hfin, hinj, -, -, hkO', hint⟩ :=
    GlobalTheory.CdvrLiftCp.exists_cdvr_lift p T₀ hT₀ kO₀ k₀ hk₀ L kL (fun a => rfl)
  obtain ⟨β', hβ'⟩ := hint A (φL.comp f) (fun a => by
    rw [← GlobalTheory.CdvrLiftCp.mem_int_iff']
    have h1 : IsIntegral ℤ a := Algebra.IsIntegral.isIntegral a
    have h2 : IsIntegral 𝓞_ℂ_[p] ((kL.comp (φL.comp f)) a) :=
      IsIntegral.map_of_comp_eq (Int.castRingHom 𝓞_ℂ_[p]) _ (RingHom.ext_int _ _) h1
    exact (PadicComplexInt.integers p).mem_of_integral h2)
  have hring : (ψ.toRingHom.comp φL).comp f = (algebraMap T'.V (FractionRing T'.V)).comp β' :=
    RingHom.ext fun a => (hβ' a).symm
  obtain ⟨yT, hyT⟩ := exists_extend s hs (V := T'.V) (spMap (ψ.toRingHom.comp φL) ≫ ξ) (spMap β') (by
    rw [Category.assoc, ← hf, spm_spm, spm_spm, hring])
  refine ⟨T', kO', yT, hfin, hinj, ?_⟩
  have hrk : (algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp kO' =
      (kL.comp ψ.symm.toRingHom).comp (algebraMap T'.V (FractionRing T'.V)) := RingHom.ext hkO'
  have hid : (kL.comp ψ.symm.toRingHom).comp (ψ.toRingHom.comp φL) = k.comp φ := by
    rw [← hφL]
    ext a
    simp
  rw [← Category.assoc, spm_spm, hrk, ← spm_spm, Category.assoc, ← hyT, ← Category.assoc, spm_spm, hid,
    ← Category.assoc, spm_spm]

end GlobalTheory.DetHT.TestPt

namespace GlobalTheory.DetHT

theorem testPtSt : TestPtSt := by
  intro E _ _ _ H Dw l Xo c Z p _ _ P hP
  obtain ⟨K, _, k, z, hK, hz⟩ := hP
  obtain ⟨T, kO, yT, hT, hkO, h⟩ :=
    TestPt.exists_integral_point Z.s (projProper _ _ _ Z.proj) p k hK (z ≫ Z.j)
  refine ⟨spMap kO ≫ yT, ?_, T, kO, yT, hT, hkO, rfl⟩
  rw [h, hz, Category.assoc]

end GlobalTheory.DetHT

end
end

section
open GlobalTheory.DetHT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.TestPointStatement : TestPtSt := by
  first | exact @GlobalTheory.DetHT.testPtSt | exact GlobalTheory.DetHT.testPtSt | (intros; apply GlobalTheory.DetHT.testPtSt <;> assumption)
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain
open scoped NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.FlatModel GlobalTheory.Toroidal
open GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.VertForm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory.DetHT

theorem exists_lift_int {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l}
    (Y : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c (algebraMap (𝓞 c.F) c.F)) {K : Type} [Field K] (z : Sp K ⟶ Y.X)
    (h : Set.range z ⊆ Set.range Y.j) : ∃ y : Sp K ⟶ Xo.XF c, y ≫ Y.j = z := by
  obtain ⟨g, hg⟩ : ∃ g : 𝓞 c.F →+* K, z ≫ Y.s = spMap g := ⟨(Spec.preimage (z ≫ Y.s)).hom, (Spec.map_preimage _).symm⟩
  obtain ⟨x, hx⟩ := h ⟨(default : PrimeSpectrum K), rfl⟩
  have e : Y.j ≫ Y.s = (Y.jQ ≫ pullback.snd _ _) ≫ spMap (algebraMap (𝓞 c.F) c.F) := by
    rw [ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model.j, Category.assoc, pullback.condition, Category.assoc]
  obtain ⟨q, e1⟩ : ∃ q : PrimeSpectrum c.F,
      PrimeSpectrum.comap g default = PrimeSpectrum.comap (algebraMap (𝓞 c.F) c.F) q := by
    have e2 : (z ≫ Y.s) (default : PrimeSpectrum K) = (Y.j ≫ Y.s) x := congrArg Y.s hx.symm
    rw [hg, e] at e2
    exact ⟨_, e2⟩
  have hinj : Function.Injective g := by
    refine (injective_iff_map_eq_zero g).2 fun v hv => ?_
    have h1 : v ∈ (PrimeSpectrum.comap g default).asIdeal := by
      rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, hv]; exact zero_mem _
    rw [e1, PrimeSpectrum.comap_asIdeal, Ideal.mem_comap] at h1
    rw [Ideal.eq_bot_of_prime q.asIdeal] at h1
    exact IsFractionRing.injective (𝓞 c.F) c.F (h1.trans (map_zero _).symm)
  let g' : c.F →+* K := IsFractionRing.lift hinj
  have hg' : spMap g' ≫ spMap (algebraMap (𝓞 c.F) c.F) = spMap g := by
    rw [← Spec.map_comp]
    congr 1
    ext v
    exact IsFractionRing.lift_algebraMap hinj v
  let z' : Sp K ⟶ pullback Y.s (spMap (algebraMap (𝓞 c.F) c.F)) := pullback.lift z (spMap g') (hg.trans hg'.symm)
  have hz' : z' ≫ pullback.fst _ _ = z := pullback.lift_fst _ _ _
  have : IsPreimmersion (spMap (algebraMap (𝓞 c.F) c.F)) :=
    IsPreimmersion.of_isLocalization (nonZeroDivisors (𝓞 c.F)) (S := c.F)
  have h1 : IsPreimmersion (pullback.fst Y.s (spMap (algebraMap (𝓞 c.F) c.F))) :=
    MorphismProperty.of_isPullback (P := @IsPreimmersion) (IsPullback.of_hasPullback _ _).flip this
  have := Y.jQ_open
  have hr : Set.range z' ⊆ Set.range Y.jQ := by
    rintro _ ⟨p, rfl⟩
    obtain rfl : p = (default : PrimeSpectrum K) := Subsingleton.elim (α := PrimeSpectrum K) _ _
    refine ⟨x, (pullback.fst Y.s (spMap (algebraMap (𝓞 c.F) c.F))).isEmbedding.injective ?_⟩
    have e3 : (z' ≫ pullback.fst Y.s (spMap (algebraMap (𝓞 c.F) c.F))) (default : PrimeSpectrum K) =
        z (default : PrimeSpectrum K) := by
      rw [hz']
    exact hx.trans e3.symm
  refine ⟨IsOpenImmersion.lift Y.jQ z' hr, ?_⟩
  rw [ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model.j, ← Category.assoc, IsOpenImmersion.lift_fac, hz']

theorem mono_j_int {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l}
    (Y : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c (algebraMap (𝓞 c.F) c.F)) : Mono Y.j := by
  have : IsPreimmersion (spMap (algebraMap (𝓞 c.F) c.F)) :=
    IsPreimmersion.of_isLocalization (nonZeroDivisors (𝓞 c.F)) (S := c.F)
  have h1 : IsPreimmersion (pullback.fst Y.s (spMap (algebraMap (𝓞 c.F) c.F))) :=
    MorphismProperty.of_isPullback (P := @IsPreimmersion) (IsPullback.of_hasPullback _ _).flip this
  have := Y.jQ_open
  rw [ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model.j]
  infer_instance

theorem log_eq_mul_of_le_one_iff {K : Type} [Field K] (w u : Valuation K (WithZero (Multiplicative ℤ)))
    (h : ∀ a, w a ≤ 1 ↔ u a ≤ 1) (π : K) (hπ : u π = WithZero.exp (-1 : ℤ)) :
    ∃ e : ℕ, 0 < e ∧ ∀ a, -(w a).log = (e : ℤ) * -(u a).log := by
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [map_zero] at hπ
    exact WithZero.exp_ne_zero hπ.symm
  have hw : ∀ a : K, a ≠ 0 → w a ≠ 0 := fun a ha => (Valuation.ne_zero_iff w).2 ha
  have hu : ∀ a : K, a ≠ 0 → u a ≠ 0 := fun a ha => (Valuation.ne_zero_iff u).2 ha
  have hle : ∀ a : K, a ≠ 0 → ((w a).log ≤ 0 ↔ (u a).log ≤ 0) := fun a ha => by
    rw [WithZero.log_le_iff_le_exp (hw a ha), WithZero.log_le_iff_le_exp (hu a ha), WithZero.exp_zero]
    exact h a
  have hlu : (u π).log = -1 := by rw [hπ, WithZero.log_exp]
  have hpos : 0 < -(w π).log := by
    have h1 := hle π⁻¹ (inv_ne_zero hπ0)
    rw [map_inv₀, map_inv₀, WithZero.log_inv, WithZero.log_inv, hlu] at h1
    omega
  refine ⟨(-(w π).log).toNat, by omega, fun a => ?_⟩
  rw [Int.toNat_of_nonneg hpos.le]
  by_cases ha : a = 0
  · simp [ha]
  have hb : a * π ^ (u a).log ≠ 0 := mul_ne_zero ha (zpow_ne_zero _ hπ0)
  have h1 := hle _ hb
  have h2 := hle _ (inv_ne_zero hb)
  rw [map_inv₀, map_inv₀, WithZero.log_inv, WithZero.log_inv] at h2
  have e1 : (u (a * π ^ (u a).log)).log = 0 := by
    rw [map_mul, map_zpow₀, WithZero.log_mul (hu a ha) (zpow_ne_zero _ (hu π hπ0)), WithZero.log_zpow, hlu]
    simp
  have e2 : (w (a * π ^ (u a).log)).log = (w a).log + (u a).log * (w π).log := by
    rw [map_mul, map_zpow₀, WithZero.log_mul (hw a ha) (zpow_ne_zero _ (hw π hπ0)), WithZero.log_zpow, smul_eq_mul]
  rw [e1, e2] at h1 h2
  have h3 := h1.2 le_rfl
  have h4 := h2.2 (by simp)
  linarith

theorem exists_overLa {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) (T : CDVR) (io : K →+* T.Fr)
    (p : ℕ) [Fact p.Prime] (k : T.Fr →+* ℂ_[p]) (kO : T.V →+* 𝓞_ℂ_[p])
    (hk : ∀ a, algebraMap 𝓞_ℂ_[p] ℂ_[p] (kO a) = k (algebraMap T.V T.Fr a))
    (h : ∀ a : K, ‖k (io a)‖ ≤ 1 ↔ la.valuation K a ≤ 1) : ∃ e : ℕ, OverLa la T.V io e := by
  obtain ⟨r, hr⟩ := GlobalTheory.CompHt.exists_log_eq (v := (Valued.v : Valuation ℂ_[p] ℝ≥0)) (PadicComplexInt.integers p) k kO hk
  simp only [coe_valued] at hr
  have hp : p.Prime := Fact.out
  have hp0 : (p : T.Fr) ≠ 0 := fun h0 => by
    have := congrArg k h0
    rw [map_natCast, map_zero] at this
    exact hp.ne_zero (by exact_mod_cast this)
  have hv0 : ∀ x : T.Fr, x ≠ 0 → valV T.V x ≠ 0 := fun x hx => (Valuation.ne_zero_iff _).2 hx
  have hiff : ∀ x : T.Fr, x ≠ 0 → (0 ≤ vV T.V x ↔ valV T.V x ≤ 1) := fun x hx => by
    rw [vV, neg_nonneg, WithZero.log_le_iff_le_exp (hv0 x hx), WithZero.exp_zero]
  have hvp : 0 ≤ vV T.V (p : T.Fr) := by
    rw [hiff _ hp0, ← map_natCast (algebraMap T.V T.Fr)]
    exact HeightOneSpectrum.valuation_le_one _ _
  have hr0 : r < 0 := by
    have h1 := hr _ hp0
    rw [map_natCast] at h1
    have h2 : ‖(p : ℂ_[p])‖ < 1 := by
      rw [← map_natCast (algebraMap ℚ_[p] ℂ_[p]), norm_algebraMap']
      exact Padic.norm_p_lt_one
    have h3 : Real.log ‖(p : ℂ_[p])‖ < 0 :=
      Real.log_neg (norm_pos_iff.2 (by exact_mod_cast hp.ne_zero)) h2
    have h4 : (0 : ℝ) ≤ (vV T.V (p : T.Fr) : ℝ) := by exact_mod_cast hvp
    by_contra h5
    have := mul_nonneg h4 (not_lt.1 h5)
    linarith
  obtain ⟨π, hπ⟩ := la.valuation_exists_uniformizer K
  refine log_eq_mul_of_le_one_iff ((valV T.V).comap io) (la.valuation K) (fun a => ?_) π hπ
  by_cases ha : a = 0
  · simp [ha]
  have ha' : io a ≠ 0 := (map_ne_zero io).2 ha
  rw [← h a, Valuation.comap_apply, ← hiff _ ha', ← Real.log_nonpos_iff (norm_nonneg _), hr _ ha']
  constructor
  · intro h1
    exact mul_nonpos_of_nonneg_of_nonpos (by exact_mod_cast h1) hr0.le
  · intro h1
    have : (0 : ℝ) ≤ (vV T.V (io a) : ℝ) := by nlinarith
    exact_mod_cast this

theorem ptAt_of_isHTFrame {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
    (Y : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) (ν : SABMap Y.oF.t Xo.univ.t (pullback.fst _ _))
    (p : ℕ) [Fact p.Prime] [Algebra c.F ℂ_[p]] (T T' : CDVR) (i : T.V →+* T'.V) (iF : T.Fr →+* T'.Fr)
    (hi : ∀ a, algebraMap T'.V T'.Fr (i a) = iF (algebraMap T.V T.Fr a))
    (io : c.F →+* T.Fr) (y₀ : IntFr Xo c T io) (k : letI := io.toAlgebra; T.Fr →ₐ[c.F] ℂ_[p]) (y : FrPt Xo c ℂ_[p])
    (hy : IsHTFrameCp p y₀ k y) (k' : T'.Fr →+* ℂ_[p]) (kO : T'.V →+* 𝓞_ℂ_[p])
    (hkO : ∀ a, algebraMap 𝓞_ℂ_[p] ℂ_[p] (kO a) = k' (algebraMap T'.V T'.Fr a)) (hk' : ∀ a, k' (iF a) = k a)
    (yT : Sp T'.V ⟶ Y.X) (yyT : Sp T'.Fr ⟶ Xo.XF c) (hT : spMap (algebraMap T'.V T'.Fr) ≫ yT = yyT ≫ Y.j)
    (hr : yyT = spMap iF ≫ (letI := io.toAlgebra; GlobalTheory.AllWt.ptF y₀.1)) :
    letI := H.starRing; ∃ (P : PtP E p) (π : P.G.left ⟶ Y.t.G.left) (ψ : P.A.A.left ⟶ Y.oF.t.G.left) (z : FrPt Xo c ℂ_[p]),
      PtAt Y (spMap kO ≫ yT) (spMap k' ≫ yyT) P π ψ ∧ GlobalTheory.AllWt.ptF y = spMap k' ≫ yyT ∧
        IsHTChange P (ψ ≫ ν.φ) z y := by
  letI := H.starRing
  letI := io.toAlgebra
  have hxeq := GlobalTheory.CompHt.IsHTFrame.x_eq hy
  obtain ⟨-, kO₀, P, ψ₀, z, hP, -, hch⟩ := hy
  obtain ⟨hkO₀, G, t', m₁, m₂, π₀, φ₀, hπ₀, hact₀, hφ₀, hgen₀, hψ₀, -⟩ := hP
  have tr : ∀ {S S' : Scheme.{0}} {s : SAB H S} {s' : SAB H S'} {f g : S' ⟶ S}, f = g →
      ∀ m : SABMap s' s f, ∃ m' : SABMap s' s g, m'.φ = m.φ := by
    intro S S' s s' f g h m
    subst h
    exact ⟨m, rfl⟩

  have hkk : kO₀ = kO.comp i := RingHom.ext fun a => P.integers.hom_inj (by
    rw [hkO₀ a, RingHom.comp_apply, hkO (i a), hi, hk']; rfl)
  have hkk' : k'.comp iF = k.toRingHom := RingHom.ext fun a => hk' a
  have hii : (algebraMap T'.V T'.Fr).comp i = iF.comp (algebraMap T.V T.Fr) := RingHom.ext hi
  have hOO : (algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp kO = k'.comp (algebraMap T'.V T'.Fr) := RingHom.ext hkO
  have hx' : yyT ≫ pullback.fst _ _ = spMap iF ≫ y₀.1.x := by
    rw [hr, Category.assoc]
    congr 1
    exact pullback.lift_fst _ _ _

  obtain ⟨G', ⟨a⟩⟩ := exists_sab (spMap i) G
  obtain ⟨Yt', ⟨b⟩⟩ := exists_sab yT Y.t
  obtain ⟨t₂, ⟨q⟩⟩ := exists_sab yyT Y.oF.t
  obtain ⟨t₁, ⟨c₁⟩⟩ := exists_sab (spMap (algebraMap T'.V T'.Fr)) G'
  obtain ⟨n₁, hn₁⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ ν q
  obtain ⟨e₂, he₂⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ Y.m q
  obtain ⟨e₂', he₂'⟩ := tr (show yyT ≫ Y.jQ ≫ pullback.fst _ _ = spMap (algebraMap T'.V T'.Fr) ≫ yT from hT.symm) e₂
  obtain ⟨n₂, hn₂⟩ := sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ b e₂'
  obtain ⟨e₁, he₁⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ a c₁
  obtain ⟨e₁', he₁'⟩ := tr (show spMap (algebraMap T'.V T'.Fr) ≫ spMap i = spMap iF ≫ spMap (algebraMap T.V T.Fr) by
    rw [spMap_spMap, spMap_spMap, hii]) e₁
  obtain ⟨d, hd⟩ := sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ m₂ e₁'
  obtain ⟨m₁', hm₁'⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m₁ d
  obtain ⟨m₁'', hm₁''⟩ := tr hx'.symm m₁'
  obtain ⟨κ, nn, hκ, hnn⟩ := GlobalTheory.sab_extensions_iso E H Dw l Xo T'.V T'.Fr _ G' Yt' t₁ t₂ m₁'' c₁ n₁ n₂

  have w₁ : π₀ ≫ G.G.hom = (P.G.hom ≫ spMap kO) ≫ spMap i := by
    rw [hπ₀.1.w, Category.assoc, spMap_spMap, hkk]
  let π₁ : P.G.left ⟶ G'.G.left := a.cart.1.lift π₀ (P.G.hom ≫ spMap kO) w₁
  have hπ₁a : π₁ ≫ a.φ = π₀ := a.cart.1.lift_fst _ _ _
  have hπ₁s : π₁ ≫ G'.G.hom = P.G.hom ≫ spMap kO := a.cart.1.lift_snd _ _ _
  have hπ₁ : IsGrpPullback P.G G'.G (spMap kO) π₁ :=
    a.cart.cancel (hπ₀.congr (by rw [spMap_spMap, hkk]) hπ₁a.symm) hπ₁s

  have w₂ : φ₀ ≫ t'.G.hom = (P.A.A.hom ≫ spMap k') ≫ spMap iF := by
    rw [hφ₀.1.w, Category.assoc, spMap_spMap, hkk']
  let ψ₁ : P.A.A.left ⟶ t₁.G.left := d.cart.1.lift φ₀ (P.A.A.hom ≫ spMap k') w₂
  have hψ₁d : ψ₁ ≫ d.φ = φ₀ := d.cart.1.lift_fst _ _ _
  have hψ₁s : ψ₁ ≫ t₁.G.hom = P.A.A.hom ≫ spMap k' := d.cart.1.lift_snd _ _ _
  have hψ₁ : IsGrpPullback P.A.A t₁.G (spMap k') ψ₁ :=
    d.cart.cancel (hφ₀.congr (by rw [spMap_spMap, hkk']) hψ₁d.symm) hψ₁s
  have key : ψ₁ ≫ c₁.φ = P.gen ≫ π₁ := by
    apply a.cart.1.hom_ext
    · rw [Category.assoc, Category.assoc, hπ₁a, ← he₁, ← he₁', hd, ← Category.assoc, hψ₁d, hgen₀]
    · rw [Category.assoc, Category.assoc, hπ₁s, c₁.cart.1.w, ← Category.assoc, hψ₁s, ← Category.assoc,
        P.gen_pull.1.w, Category.assoc, Category.assoc, spMap_spMap, spMap_spMap, hOO]
  refine ⟨P, π₁ ≫ nn.φ ≫ b.φ, ψ₁ ≫ κ.φ ≫ q.φ, z, ?_⟩
  have hψν : (ψ₁ ≫ κ.φ ≫ q.φ) ≫ ν.φ = ψ₀ := by
    rw [Category.assoc, Category.assoc, ← hn₁, hκ, hm₁'', hm₁', ← Category.assoc, hψ₁d, hψ₀]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, by rw [hψν]; exact hch⟩
  · rw [← Category.assoc, spMap_spMap, hOO, ← spMap_spMap, Category.assoc, hT, Category.assoc]
  · exact ((hπ₁.comp nn.cart).comp b.cart).congr (by rw [Category.comp_id]) (by rw [Category.assoc])
  · intro a₀
    have h1 : (P.oG.act a₀).left ≫ π₁ = π₁ ≫ (G'.act.act a₀).left := by
      apply a.cart.1.hom_ext
      · rw [Category.assoc, Category.assoc, hπ₁a, hact₀, a.act, ← Category.assoc, hπ₁a]
      · rw [Category.assoc, Category.assoc, hπ₁s, Over.w, hπ₁s, ← Category.assoc, Over.w]
    simp only [Category.assoc, reassoc_of% h1, reassoc_of% (nn.act a₀), b.act a₀]
  · exact ((hψ₁.comp κ.cart).comp q.cart).congr (by rw [Category.comp_id]) (by rw [Category.assoc])
  · have h2 : q.φ ≫ Y.m.φ = n₂.φ ≫ b.φ := by rw [← he₂, ← he₂', hn₂]
    rw [Category.assoc, Category.assoc, h2, ← Category.assoc κ.φ, ← hnn]
    simp only [Category.assoc]
    rw [reassoc_of% key]
  · apply pullback.hom_ext
    · rw [ptF, pullback.lift_fst, hxeq, Category.assoc, hx', ← Category.assoc, spMap_spMap, hkk']
    · rw [ptF, pullback.lift_snd]
      simp only [Category.assoc]
      rw [hr, Category.assoc, ← Category.assoc, spMap_spMap, hkk', ptF, pullback.lift_snd, spMap_spMap]
      congr 1
      exact (RingHom.ext fun x => k.commutes x).symm

theorem exFrameSt_holds : ExFrameSt := by
  intro E _ _ _ H Dw l Xo c hpq Y Zc la p _ inst hla P yb hyb hP
  obtain ⟨hgen, T, kO, yT, hfin, hkO, hyT⟩ := hyb
  have hiO : Function.Injective (algebraMap 𝓞_ℂ_[p] ℂ_[p]) := (PadicComplexInt.integers p).hom_inj
  have hgX : Set.range (spMap (algebraMap T.V T.Fr) ≫ yT) ⊆ Set.range Y.j := by
    rintro _ ⟨s, rfl⟩
    obtain rfl : s = (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum T.Fr) := Subsingleton.elim (α := PrimeSpectrum T.Fr) _ _
    have h1 := bot_map (IsFractionRing.injective T.V T.Fr) yT
    have h2 := bot_map (φ := (algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp kO) (hiO.comp hkO) yT
    rw [← sp_sp, hyT, hgen] at h2
    rw [h1, ← h2]
    exact ⟨_, (Scheme.Hom.comp_apply _ _ _).symm⟩
  obtain ⟨yyT, hyyT⟩ := exists_lift_int Y _ hgX
  obtain ⟨io, hio⟩ : ∃ io : c.F →+* T.Fr, yyT ≫ pullback.snd _ _ = spMap io :=
    ⟨(Spec.preimage (yyT ≫ pullback.snd _ _)).hom, (Spec.map_preimage (yyT ≫ pullback.snd _ _)).symm⟩
  let x : Sp T.Fr ⟶ Xo.X := yyT ≫ pullback.fst _ _
  have hx : (letI := io.toAlgebra; x ≫ Xo.s = sOf c T.Fr) := by
    letI := io.toAlgebra
    show (yyT ≫ pullback.fst _ _) ≫ Xo.s = _
    rw [Category.assoc, pullback.condition, ← Category.assoc yyT, hio, sOf, spMap_spMap]
  obtain ⟨T', i, rr, hrr, hv, hfin', y₀, hy₀⟩ := GlobalTheory.AnyLevelFrame.intFrExt E H Dw l Xo c hpq T io hfin x hx
  obtain ⟨φ, hφ, hloc⟩ := GlobalTheory.GoodChartExt.exists_local_restrict T T' i rr hrr hv
  have hφi : Function.Injective φ := by
    intro a b h
    apply i.injective.comp (IsFractionRing.injective T.V T.Fr)
    have ha := RingHom.congr_fun hφ a
    have hb := RingHom.congr_fun hφ b
    simp only [RingHom.comp_apply] at ha hb
    simp only [Function.comp_apply, ← ha, ← hb, h]
  have hfinφ : φ.Finite := GlobalTheory.CompHS.finite_of_finRes hfin' φ hφi
  obtain ⟨kO', hkO', hinj'⟩ := exists_ext_of_integral (Valued.v : Valuation ℂ_[p] ℝ≥0) (PadicComplexInt.integers p)
    φ hφi hfinφ.to_isIntegral kO (hiO.comp hkO)
  let k : T'.Fr →+* ℂ_[p] := IsFractionRing.lift hinj'
  have hk : ∀ a, algebraMap 𝓞_ℂ_[p] ℂ_[p] (kO' a) = k (algebraMap T'.V T'.Fr a) := fun a =>
    (IsFractionRing.lift_algebraMap hinj' a).symm
  have hcomm : spMap (algebraMap T'.V T'.Fr) ≫ (spMap φ ≫ yT) = (spMap i ≫ yyT) ≫ Y.j := by
    rw [sp_sp, hφ, ← sp_sp, Category.assoc, hyyT]
  have hPk : GlobalTheory.AllWt.ptF P = spMap k ≫ spMap i ≫ yyT := by
    have := mono_j_int Y
    rw [← cancel_mono Y.j, ← hgen, Category.assoc, ← hcomm, ← hyT, ← hkO', sp_sp, sp_sp, sp_sp]
    congr 2
    exact RingHom.ext fun a => hk (φ a)
  have halg : algebraMap c.F ℂ_[p] = k.comp (i.comp io) := by
    have h1 := ptF_snd P
    rw [hPk, Category.assoc, Category.assoc, hio, spMap_spMap, spMap_spMap] at h1
    exact (congrArg CommRingCat.Hom.hom (Spec.map_injective h1)).symm
  letI := (i.comp io).toAlgebra
  letI := H.starRing
  let kA : T'.Fr →ₐ[c.F] ℂ_[p] := { k with commutes' := fun a => (RingHom.congr_fun halg a).symm }
  obtain ⟨y, hy⟩ := GlobalTheory.CompHt.exists_isHTFrame (p := p) (v := (Valued.v : Valuation ℂ_[p] ℝ≥0)) (O := 𝓞_ℂ_[p])
    (fun _ => rfl) (PadicComplexInt.integers p) y₀ hfin' kA kO' hk
  have hpt : spMap i ≫ yyT = GlobalTheory.AllWt.ptF y₀.1 := by
    apply pullback.hom_ext
    · rw [GlobalTheory.AllWt.ptF, pullback.lift_fst, hy₀, Category.assoc]
    · rw [GlobalTheory.AllWt.ptF, pullback.lift_snd, Category.assoc, hio, spMap_spMap]
  obtain ⟨Q, π, ψ, z, h1, h2, h3⟩ := ptAt_of_isHTFrame Y Y.m0.toSABMap p T' T' (RingHom.id _) (RingHom.id _)
    (fun _ => rfl) (i.comp io) y₀ kA y hy k kO' hk (fun _ => rfl) (spMap φ ≫ yT) (spMap i ≫ yyT) hcomm
    (by rw [show spMap (RingHom.id T'.Fr) = 𝟙 _ from Spec.map_id _, Category.id_comp, hpt])
  rw [sp_sp, hkO', hyT, ← hPk] at h1
  obtain ⟨e, he⟩ := exists_overLa la T' (i.comp io) p k kO' hk fun a => by
    rw [← hla a, halg]; rfl
  refine ⟨y, ⟨T', i.comp io, e, y₀, he, ⟨hfin', fun s => ?_⟩, p, inferInstance, inst, kA, y, hy, rfl⟩, h2.trans hPk.symm,
    Q, π, ψ, z, h1, h3⟩
  obtain rfl : s = (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum T'.Fr) := Subsingleton.elim (α := PrimeSpectrum T'.Fr) _ _
  have h4 := hP (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum ℂ_[p])
  rw [hPk, hpt, bot_map k.injective] at h4
  exact h4

end GlobalTheory.DetHT

end
end

section
open GlobalTheory.DetHT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ExistsFrameStatement : ExFrameSt := by
  first | exact @GlobalTheory.DetHT.exFrameSt_holds | exact GlobalTheory.DetHT.exFrameSt_holds | (intros; apply GlobalTheory.DetHT.exFrameSt_holds <;> assumption)
end

section
open GlobalTheory.DetHT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ConnectingStatement : BridgeSt := by
  first | exact @GlobalTheory.DetHT.Bridge.bridge | exact GlobalTheory.DetHT.Bridge.bridge | (intros; apply GlobalTheory.DetHT.Bridge.bridge <;> assumption)
end

section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain
open scoped NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.DetHT
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DetHT.Covol

open Matrix GlobalTheory.LineNorm

theorem norm_det_col_le {C : Type} [NormedField C] {m : ℕ} (g : Matrix (Fin m) (Fin m) C) (σ : Fin m → Fin m) :
    ‖(g.submatrix id σ).det‖ ≤ ‖g.det‖ := by
  by_cases hσ : Function.Injective σ
  · have hb : Function.Bijective σ := Finite.injective_iff_bijective.1 hσ
    let π : Equiv.Perm (Fin m) := Equiv.ofBijective σ hb
    have : g.submatrix id σ = g.submatrix id π := rfl
    rw [this, Matrix.det_permute', norm_mul]
    rcases Int.units_eq_one_or (Equiv.Perm.sign π) with h | h <;> simp [h]
  · obtain ⟨i, j, hij, hne⟩ : ∃ i j, σ i = σ j ∧ i ≠ j := by
      simp only [Function.Injective, not_forall] at hσ
      obtain ⟨i, j, h1, h2⟩ := hσ
      exact ⟨i, j, h1, h2⟩
    rw [Matrix.det_zero_of_column_eq hne (fun k => by simp [hij])]
    simp

theorem covol : CovolSt := by
  intro E _ _ _ H X t C _ _ x Λ m u u' g δ hδ htan _hind hΛ hu hdet
  let h : Fin m → Fin m → C := fun j i => if i = j then δ else 0
  have hsum : ∀ (b : Fin m → C) (j : Fin m), ∑ i, h j i * b i = δ * b j := by
    intro b j
    simp [h, ite_mul]
  have hh : ∀ c : Fin m → C, (∀ j, ∑ i, h j i * c i = 0) → c = 0 := fun c hc =>
    funext fun j => by
      have := hc j
      rw [hsum] at this
      simpa [hδ] using this
  have hN : ∀ l, GlobalTheory.ShFam.Pad.grNorm t x Λ u l = sInf {r | ∃ cf : Fin m → C, cf l ≠ 0 ∧
      (∀ l', l < l' → cf l' = 0) ∧ (∀ j, ‖∑ i, h j i * ∑ l', cf l' * g l' i‖ ≤ 1) ∧ r = ‖cf l‖⁻¹} := fun l => by
    rw [GlobalTheory.LineNorm.WedgeMax.grNorm_eq t htan (P := fun b => ∀ i, ‖δ * b i‖ ≤ 1) hΛ hu l]
    simp only [hsum]
  have hli : LinearIndependent C g :=
    Matrix.linearIndependent_rows_of_isUnit ((Matrix.isUnit_iff_isUnit_det g).2 (isUnit_iff_ne_zero.2 hdet))
  obtain ⟨hpos, hprod⟩ := GlobalTheory.LineNorm.Covol.prod_grNorm_eq_iSup_minor C m (Fin m) h hh m g hli
    (fun l => GlobalTheory.ShFam.Pad.grNorm t x Λ u l) hN
  have e := hprod m le_rfl
  have key : ∀ σ : Fin m → Fin m, ‖∑ s : Fin m → Fin m, (∏ i, h (σ i) (s i)) * minor g le_rfl s‖ =
      ‖δ‖ ^ m * ‖(g.submatrix id σ).det‖ := by
    intro σ
    rw [GlobalTheory.LineNorm.Covol.sum_prod_mul_minor (fun i => h (σ i)) g le_rfl]
    have : (Matrix.of fun l i => ∑ t, h (σ i) t * g (Fin.castLE le_rfl l) t) = δ • g.submatrix id σ := by
      ext l i
      rw [Matrix.of_apply, hsum]
      simp
    rw [this, Matrix.det_smul, norm_mul, norm_pow, Fintype.card_fin]
  have hsup : (⨆ σ : Fin m → Fin m, ‖∑ s : Fin m → Fin m, (∏ i, h (σ i) (s i)) * minor g le_rfl s‖) =
      ‖δ‖ ^ m * ‖g.det‖ := by
    haveI : Nonempty (Fin m → Fin m) := ⟨id⟩
    simp only [key]
    refine le_antisymm (ciSup_le fun σ => ?_) (le_ciSup_of_le (Finite.bddAbove_range _) id ?_)
    · exact mul_le_mul_of_nonneg_left (norm_det_col_le g σ) (by positivity)
    · simp
  rw [hsup] at e
  simp only [Fin.castLE_rfl, id] at e
  rw [← Real.log_prod (fun l _ => (hpos l).ne'), e, Real.log_mul (by positivity) (norm_ne_zero_iff.2 hdet),
    Real.log_pow]
  ring

end GlobalTheory.DetHT.Covol
end
end

section
open GlobalTheory.DetHT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.CovolumeStatement : CovolSt := by
  first | exact @GlobalTheory.DetHT.Covol.covol | exact GlobalTheory.DetHT.Covol.covol | (intros; apply GlobalTheory.DetHT.Covol.covol <;> assumption)
end

section
open NumberField Formalism.BasicNotions Formalism.MainNotions GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Cartier CategoryTheory AlgebraicGeometry
open IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.CovolFin

theorem log_valAt_prod {K : Type} [Field K] {Z : Scheme.{0}} [IsIntegral Z] (y : Sp K ⟶ Z) (w : AbsoluteValue K ℝ)
    {ι : Type} (s : Finset ι) (u : ι → Z.functionFieldˣ) (hu : ∀ i ∈ s, UnitAt (below y) (u i : Z.functionField)) :
    UnitAt (below y) ((∏ i ∈ s, u i : Z.functionFieldˣ) : Z.functionField) ∧
      Real.log (w (valAt y ((∏ i ∈ s, u i : Z.functionFieldˣ) : Z.functionField))) =
        ∑ i ∈ s, Real.log (w (valAt y (u i : Z.functionField))) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h₁ : valAt y (1 : Z.functionField) = 1 := by simpa using Base.valAt_stalk y 1
    simp [h₁, unitAt_one]
  | insert a s ha ih =>
    obtain ⟨U, e⟩ := ih fun i hi => hu i (Finset.mem_insert_of_mem hi)
    have Ua := hu a (Finset.mem_insert_self a s)
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Units.val_mul]
    refine ⟨Ua.mul U, ?_⟩
    rw [SmallSec.valAt_mul Ua.regAt U.regAt, map_mul,
      Real.log_mul (w.pos (SmallSec.valAt_ne_zero Ua)).ne' (w.pos (SmallSec.valAt_ne_zero U)).ne', e]

section Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β} {F : Type} [Field F] [NumberField F] {e : F ≃+* c.F} (Y : FlagCpt Z e)

theorem zpow_finsum {G : Type} [CommGroup G] (a : G) {ι : Type} (s : Finset ι) (f : ι → ℤ) :
    a ^ (∑ i ∈ s, f i) = ∏ i ∈ s, a ^ f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.prod_insert hj, zpow_add, ih]

variable (Dw) in

theorem expo_sum {ι : Type} (s : Finset ι) (ρ : ι → Sym E →₀ ℤ) :
    expo Dw (∑ i ∈ s, ρ i) = ∑ i ∈ s, expo Dw (ρ i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [LineTest.expo_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, LineTest.expo_add, ih]

theorem sum_neg_sum {ι : Type} (s : Finset ι) (ρ : ι → Sym E →₀ ℤ) (K : Sym E → ℝ) :
    ((-∑ i ∈ s, ρ i).sum fun a n => (n : ℝ) * K a) = -∑ i ∈ s, (ρ i).sum fun a n => (n : ℝ) * K a := by
  classical
  rw [Finsupp.sum_neg_index (fun _ => by simp)]
  simp only [Int.cast_neg, neg_mul]
  rw [Finsupp.sum_finset_sum_index (fun _ => by simp) (fun _ _ _ => by push_cast; ring)]
  simp [Finsupp.sum, Finset.sum_neg_distrib]

open Classical in

theorem lgOf_neg_sum {ι : Type} (s : Finset ι) (ρ : ι → Sym E →₀ ℤ) (v : HeightOneSpectrum (𝓞 F)) (ε : Ext v)
    (y : AlgPt Y.Y) :
    lgOf Y (-∑ i ∈ s, ρ i) v ε y = Real.log (ε.w (valAt y.1
      (((eqn (divOf Y (expo Dw (-∑ i ∈ s, ρ i))) (below y.1))⁻¹ *
        ∏ i ∈ s, (eqn (divOf Y (expo Dw (ρ i))) (below y.1))⁻¹ : Y.Y.Fnˣ) : Y.Y.Fn))) -
      ∑ i ∈ s, lgOf Y (ρ i) v ε y := by
  have hp := LineTest.residueCharacteristic_prime v
  have UW := GlobalTheory.CombInd.Tens.unitAt_prod Y (-∑ i ∈ s, ρ i) (below y.1)
  have Ui := fun i => GlobalTheory.CombInd.Tens.unitAt_prod Y (ρ i) (below y.1)
  simp only [lgOf, dif_pos hp]
  rw [sum_neg_sum]
  set b := below y.1 with hb
  set t := (Y.gr_spec b).choose_spec.choose_spec.choose with ht
  have hP : (∏ x : Letter Dw, t x.1 x.2 ^ expo Dw (-∑ i ∈ s, ρ i) x) =
      (∏ i ∈ s, ∏ x : Letter Dw, t x.1 x.2 ^ expo Dw (ρ i) x)⁻¹ := by
    rw [GlobalTheory.CombInd.DualComb.expo_neg, expo_sum, Finset.prod_comm, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun x _ => ?_
    rw [Pi.neg_apply, Finset.sum_apply, zpow_neg, zpow_finsum]
  have hprod : ((eqn (divOf Y (expo Dw (-∑ i ∈ s, ρ i))) b)⁻¹ * ∏ i ∈ s, (eqn (divOf Y (expo Dw (ρ i))) b)⁻¹ : Y.Y.Fnˣ) =
      ((∏ x : Letter Dw, t x.1 x.2 ^ expo Dw (-∑ i ∈ s, ρ i) x) * (eqn (divOf Y (expo Dw (-∑ i ∈ s, ρ i))) b)⁻¹) *
        ∏ i ∈ s, ((∏ x : Letter Dw, t x.1 x.2 ^ expo Dw (ρ i) x) * (eqn (divOf Y (expo Dw (ρ i))) b)⁻¹) := by
    rw [hP, Finset.prod_mul_distrib, mul_mul_mul_comm, inv_mul_cancel, one_mul]
  obtain ⟨Us, hs⟩ := GlobalTheory.CovolFin.log_valAt_prod y.1 ε.w s
    (fun i => (∏ x : Letter Dw, t x.1 x.2 ^ expo Dw (ρ i) x) * (eqn (divOf Y (expo Dw (ρ i))) b)⁻¹) fun i _ => Ui i
  rw [hprod, Units.val_mul _ (∏ i ∈ s, _), SmallSec.valAt_mul UW.regAt Us.regAt, map_mul,
    Real.log_mul (ε.w.pos (SmallSec.valAt_ne_zero UW)).ne' (ε.w.pos (SmallSec.valAt_ne_zero Us)).ne', hs,
    Finset.sum_add_distrib, ← Finset.mul_sum]
  simp only [Units.val_mul]
  ring

end Free

theorem detOmSym_eq (E : Type) [Field E] (g : ℕ) :
    detOmSym E g = -∑ k : Fin g, Finsupp.single (ArIn.ind ∅, (none : Option ℝ), (Sum.inr (k : ℕ) : ((E →+* ℂ) × ℕ) ⊕ ℕ)) 1 := by
  have hind : ArIn.ind ∅ = fun _ => false := funext fun q => by simp [ArIn.ind]
  rw [hind, ← Finset.sum_neg_distrib]
  unfold detOmSym
  refine Fintype.sum_equiv Fin.revPerm _ _ fun k => ?_
  simp [wholeSym, Finsupp.single_neg]

theorem lg_detOmSym : ∀ (D : D7) (O : Setup D) (c : O.s.Comp) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.what₂.LL)) (e : GlobalTheory.TrueGeo.Ext v) (y : AlgPt (O.var c)), (O.adl0 c (detOmSym D.host.E (D.R.f * O.N))).lg v e y = Real.log (e.w (valAt y.1 (genAt (O.adl0 c (detOmSym D.host.E (D.R.f * O.N))).D (below y.1) / ∏ k : Fin (D.R.f * O.N), genAt (O.adl0 c (Finsupp.single (ArIn.ind ∅, none, Sum.inr (k : ℕ)) 1)).D (below y.1) ^ (-1 : ℤ)))) - ∑ k : Fin (D.R.f * O.N), (O.adl0 c (Finsupp.single (ArIn.ind ∅, none, Sum.inr (k : ℕ)) 1)).lg v e y := by
  intro D O c v e y
  rw [detOmSym_eq]
  refine (lgOf_neg_sum (O.Φ.C c) Finset.univ _ v e y).trans ?_
  congr 3
  simp only [Setup.adl0, adlOf, genAt, Units.val_mul, Units.coe_prod, zpow_neg, zpow_one, div_eq_mul_inv,
    Finset.prod_inv_distrib, inv_inv, Units.val_inv_eq_inv_val]

end GlobalTheory.CovolFin
end
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.Toroidal
open GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.ShFam.Descent

namespace GlobalTheory.DetHT.FlagNorm

theorem exists_place {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] (σ : K' ≃+* K)
    (w : HeightOneSpectrum (𝓞 K)) : ∃ w' : HeightOneSpectrum (𝓞 K'), ∀ y, w'.valuation K' y = w.valuation K (σ y) := by
  let e := RingOfIntegers.mapRingEquiv σ
  let w' : HeightOneSpectrum (𝓞 K') := HeightOneSpectrum.comap (e : 𝓞 K' →+* 𝓞 K) e.surjective w
  have h : w'.asIdeal = w.asIdeal.comap e := rfl
  have hi : ∀ x, w'.intValuation x = w.intValuation (e x) := fun x => by
    refine GlobalTheory.QNorm.withZero_eq_of_le_exp_iff (w'.intValuation_le_one _) (w.intValuation_le_one _) ?_
    intro n
    rw [HeightOneSpectrum.intValuation_le_pow_iff_mem, HeightOneSpectrum.intValuation_le_pow_iff_mem,
      h, ← Ideal.mem_comap, ← Ideal.map_symm, ← Ideal.map_symm, Ideal.map_pow]
  refine ⟨w', fun y => ?_⟩
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K') y
  have hc : ∀ x : 𝓞 K', σ (algebraMap (𝓞 K') K' x) = algebraMap (𝓞 K) K (e x) := fun x => rfl
  rw [map_div₀ σ, hc, hc, map_div₀, map_div₀]
  simp only [HeightOneSpectrum.valuation_of_algebraMap, hi]

theorem adicAbv_le_one_iff {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (x : K) :
    NumberField.HeightOneSpectrum.adicAbv K v x ≤ 1 ↔ v.valuation K x ≤ 1 := by
  rw [← WithZeroMulInt.toNNReal_le_one_iff (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v), ← NNReal.coe_le_coe]
  rfl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

theorem sum_lnStep {X : Scheme.{0}} (t : SAB H X) (p : ℕ) [Fact p.Prime] (x : Sp ℂ_[p] ⟶ X)
    (u : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber ℂ_[p]) ⟶ t.G.left)) (τ : Psi H) (a : ℕ → Bool) (ha : a p = true)
    (R : Option ℝ) :
    ∑ i : Fin (Dw.p + Dw.q), ((rootSym Dw a R τ.1 i).sum fun b n => (n : ℝ) * lnStep t x u p (b.1 p) b.2.2) =
      lnDet t p x u τ.1 - Dw.p * (vDiff E p * Real.log p) := by
  have hp : Dw.mult τ.1 = Dw.p := if_pos τ.2
  have hq : Dw.mult (conjEmb τ.1) = Dw.q := if_neg (conj_not_mem τ)
  rw [Fin.sum_univ_add, lnDet]
  have h1 : ∀ i : Fin Dw.p, ((rootSym Dw a R τ.1 (Fin.castAdd Dw.q i : Fin (Dw.p + Dw.q))).sum fun b n =>
      (n : ℝ) * lnStep t x u p (b.1 p) b.2.2) =
      Real.log (Pad.grNorm t x (latHT t p x) (u τ.1) (i.cast hp.symm)) - vDiff E p * Real.log p := fun i => by
    have hi : (i : ℕ) < Dw.mult τ.1 := by rw [hp]; exact i.2
    rw [rootSym, if_pos (by simp), Finsupp.sum_single_index (by simp)]
    simp only [lnStep, Fin.val_castAdd, dif_pos hi, ha, τ.2, and_self, if_true, Int.cast_one, one_mul, lat]
    rfl
  have h2 : ∀ j : Fin Dw.q, ((rootSym Dw a R τ.1 (Fin.natAdd Dw.p j : Fin (Dw.p + Dw.q))).sum fun b n =>
      (n : ℝ) * lnStep t x u p (b.1 p) b.2.2) =
      -Real.log (Pad.grNorm t x (latHT t p x) (u (conjEmb τ.1)) (j.rev.cast hq.symm)) := fun j => by
    have hj := j.2
    have e : Dw.p + Dw.q - 1 - (Dw.p + j) = Dw.q - (j + 1) := by omega
    have hi : Dw.q - (j + 1) < Dw.mult (conjEmb τ.1) := by rw [hq]; omega
    rw [rootSym, if_neg (by simp), Finsupp.sum_single_index (by simp)]
    simp only [lnStep, Fin.val_natAdd, e, dif_pos hi, ha, conj_not_mem τ, and_false, if_false, Int.cast_neg, Int.cast_one,
      neg_mul, one_mul, lat, sub_zero]
    rfl
  simp only [h1, h2, Finset.sum_sub_distrib, Finset.sum_neg_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  rw [← (finCongr hp.symm).sum_comp, ← (Fin.revPerm.trans (finCongr hq.symm)).sum_comp]
  simp only [finCongr_apply, Equiv.trans_apply, Fin.revPerm_apply]
  ring

variable {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β} {F : Type} [Field F] [NumberField F] {e : F ≃+* c.F} (Y : FlagCpt Z e)

theorem exists_point {K k : Type} [Field K] [Field k] [Algebra F K] [Algebra c.F k] (y₀ : Y.Y.X)
    (sc : Y.Y.X.presheaf.stalk y₀ →+* K) (hy : spMap sc ≫ stalkPt Y.Y y₀ ≫ Y.Y.str = spMap (algebraMap F K)) (io : K →+* k)
    (hA : ∀ a, algebraMap c.F k a = io (algebraMap F K (e.symm a))) (hb : Y.π y₀ ∉ genBd Z)
    {φ : c.F →+* Y.Y.X.presheaf.stalk y₀} (fr : EigFrame Z φ (stalkPt Y.Y y₀ ≫ Y.π ≫ genι Z))
    {t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Y.Y.Fnˣ}
    (h2 : fr.Tri (algebraMap (Y.Y.X.presheaf.stalk y₀) Y.Y.X.functionField) Y.f0 t)
    {ex : Ix Dw → ℤ} (hex : ex none = 0) {f : Rul Xo c} (hf : f ∈ secZ Xo c ex) (Zc : Formalism.L2.Pj.Comp Xo c)
    (hZ : letI := (constF e Y.Y).toAlgebra; GlobalTheory.AllWt.LiesOn Zc Y.y0) :
    ∃ (P : FrPt Xo c k) (z : Sp K ⟶ Xo.XF c) (r : Y.Y.X.presheaf.stalk y₀),
      GlobalTheory.AllWt.ptF P = spMap io ≫ z ∧ GlobalTheory.AllWt.LiesOn Zc P ∧
      GlobalTheory.AllWt.ptF P ≫ Z.j = spMap (io.comp sc) ≫ stalkPt Y.Y y₀ ≫ Y.π ≫ genι Z ∧
      ((frameOf Z P).v = fun τ i => spMap (dualMap (io.comp sc)) ≫ fr.v τ i) ∧
      algebraMap _ Y.Y.X.functionField r = Y.val f * ((∏ z : Letter Dw, t z.1 z.2 ^ (-ex (some z)) : Y.Y.Fnˣ) : Y.Y.Fn) ∧
      evR Xo c f P = io (sc r) := by
  classical
  have hopen : Y.π y₀ ∈ Set.range Z.jQ := not_not.1 hb
  have hgen : spMap (algebraMap (Y.Y.X.presheaf.stalk y₀) Y.Y.X.functionField) ≫ stalkPt Y.Y y₀ = genericPt Y.Y :=
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk ((genericPoint_spec Y.Y.X).specializes trivial)
  letI : Algebra c.F (Y.Y.X.presheaf.stalk y₀) := φ.toAlgebra
  letI : Algebra c.F Y.Y.X.functionField := (constF e Y.Y).toAlgebra
  haveI := Z.jQ_open
  have hr : Set.range (stalkPt Y.Y y₀ ≫ Y.π) ⊆ Set.range Z.jQ := by
    rintro _ ⟨q, rfl⟩
    have h1 : stalkPt Y.Y y₀ q ⤳ y₀ := by
      have : stalkPt Y.Y y₀ q ∈ Set.range (Y.Y.X.fromSpecStalk y₀) := ⟨q, rfl⟩
      rwa [Scheme.range_fromSpecStalk] at this
    exact (h1.map Y.π.continuous).mem_open Z.jQ.isOpenEmbedding.isOpen_range hopen
  let xF := IsOpenImmersion.lift Z.jQ _ hr
  have hxF : xF ≫ Z.jQ = stalkPt Y.Y y₀ ≫ Y.π := IsOpenImmersion.lift_fac _ _ _
  have hpt0 : GlobalTheory.AllWt.ptF Y.y0 = spMap (algebraMap (Y.Y.X.presheaf.stalk y₀) Y.Y.X.functionField) ≫ xF := by
    rw [← cancel_mono Z.jQ, Category.assoc, hxF, ← Category.assoc, hgen]
    exact Y.y0_x
  have hc : constF e Y.Y = (algebraMap (Y.Y.X.presheaf.stalk y₀) Y.Y.X.functionField).comp φ := h2.2.1
  have hs : xF ≫ pullback.snd _ _ = spMap (algebraMap c.F (Y.Y.X.presheaf.stalk y₀)) := by
    obtain ⟨φ₂, h⟩ := Spec.map_surjective (xF ≫ pullback.snd _ _)
    have k1 : spMap (algebraMap (Y.Y.X.presheaf.stalk y₀) Y.Y.X.functionField) ≫ spMap φ₂.hom =
        spMap (constF e Y.Y) := by
      have h0 : GlobalTheory.AllWt.ptF Y.y0 ≫ pullback.snd _ _ = spMap (constF e Y.Y) := pullback.lift_snd _ _ _
      rw [← h0, hpt0, Category.assoc, ← h]
      rfl
    rw [sp_comp] at k1
    have k2 := sp_inj k1
    have k3 : φ₂.hom = φ := RingHom.ext fun r =>
      IsFractionRing.injective (Y.Y.X.presheaf.stalk y₀) Y.Y.X.functionField
        ((RingHom.congr_fun k2 r).trans (RingHom.congr_fun hc r))
    rw [← h]
    exact congrArg spMap k3
  have hxj : xF ≫ Z.j = stalkPt Y.Y y₀ ≫ Y.π ≫ genι Z := by
    show xF ≫ Z.jQ ≫ pullback.fst _ _ = _
    rw [← Category.assoc, hxF, Category.assoc]
  obtain ⟨P', hP', htie⟩ := exists_tie_point (Z := Z) hs hxj rfl fr
  have tie0 : Comparison₂ Y.y0 Y.f0 := ⟨rfl, by
    show _ ≫ Z.jQ ≫ pullback.fst _ _ = _
    rw [← Category.assoc, Y.y0_x, Category.assoc], Y.flagComponentFramedPoint_frame⟩
  let ι₀ : Y.Y.X.presheaf.stalk y₀ →ₐ[c.F] Y.Y.X.functionField :=
    { algebraMap (Y.Y.X.presheaf.stalk y₀) Y.Y.X.functionField with
      commutes' := fun r => (RingHom.congr_fun hc r).symm }
  have hx1 : Y.y0.x = spMap ι₀.toRingHom ≫ P'.x := by
    rw [← Descent.ptF_fst Y.y0, ← Descent.ptF_fst P', hpt0, hP', Category.assoc]
  obtain ⟨u, hu, hu'⟩ := Comparison₂.bm_of_tri htie tie0 (ψ := ι₀) hx1 h2
  have e1 := BM.evR hu hf
  have hK : (sc.comp φ).comp e.toRingHom = algebraMap F K := by
    apply sp_inj
    rw [← sp_comp, ← sp_comp, ← hy, ← Y.π_str, Category.assoc, ← Category.assoc (stalkPt _ _), ← hxF,
      Category.assoc, ← Category.assoc Z.jQ, Z.jQ_over, ← Category.assoc xF, hs]
  let ψa : Y.Y.X.presheaf.stalk y₀ →ₐ[c.F] k :=
    { io.comp sc with
      commutes' := fun r => by
        rw [hA, ← hK]
        show io (sc (φ r)) = io (sc (φ (e (e.symm r))))
        rw [e.apply_symm_apply] }
  obtain ⟨P, hP⟩ := GlobalTheory.FlagTan.exists_frMap ψa P'
  have hpt : GlobalTheory.AllWt.ptF P = spMap (io.comp sc) ≫ xF := by rw [Descent.ptF_map hP.1, hP']
  refine ⟨P, spMap sc ≫ xF, evR Xo c f P', by rw [hpt, ← Category.assoc, sp_comp], fun s => ?_,
    by rw [hpt, Category.assoc, hxj], ?_, ?_, GlobalTheory.FlagTan.evR_frMap hf.1 hP⟩
  · let s₀ : Sp Y.Y.X.functionField := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum Y.Y.X.functionField)
    have h0 := hZ s₀
    rw [hpt0, Scheme.Hom.comp_apply] at h0
    rw [hpt, Scheme.Hom.comp_apply]
    have hsp : spMap (algebraMap (Y.Y.X.presheaf.stalk y₀) Y.Y.X.functionField) s₀ ⤳ spMap (io.comp sc) s := by
      refine (PrimeSpectrum.le_iff_specializes _ _).1 ?_
      intro a ha
      have h3 : algebraMap (Y.Y.X.presheaf.stalk y₀) Y.Y.X.functionField a = 0 := ha
      rw [(map_eq_zero_iff _ (IsFractionRing.injective (Y.Y.X.presheaf.stalk y₀) Y.Y.X.functionField)).1 h3]
      exact zero_mem _
    exact (hsp.map xF.continuous).mem_closed (isClosed_of_mem_irreducibleComponents _ Zc.2) h0
  · funext τ i
    have k1 := (htie.2.2 τ i).map (io.comp sc)
    rw [hP', ← hpt] at k1
    obtain ⟨w, a1, a2, a3⟩ := k1
    obtain ⟨w', b1, b2, b3⟩ := (tie_frameOf Z P).2.2 τ i
    rw [hP.2.1] at b2
    rw [← a3, ← b3, Z.m0.toSABMap.cart.1.hom_ext (a2.trans b2.symm) (a1.trans b1.symm)]
  · have hchi : GlobalTheory.ShFam.Descent.chi ex u = ∏ z : Letter Dw, t z.1 z.2 ^ ex (some z) := by
      simp only [GlobalTheory.ShFam.Descent.chi, Fintype.prod_option, hex, zpow_zero, one_mul]
      exact Finset.prod_congr rfl fun z _ => by rw [← hu' z.1 z.2]
    have E1 : Y.val f = ((∏ z : Letter Dw, t z.1 z.2 ^ ex (some z) : Y.Y.Fnˣ) : Y.Y.Fn) *
        algebraMap (Y.Y.X.presheaf.stalk y₀) Y.Y.X.functionField (evR Xo c f P') := by
      rw [← hchi]
      exact e1
    have pn : (∏ z : Letter Dw, t z.1 z.2 ^ (-ex (some z))) = (∏ z : Letter Dw, t z.1 z.2 ^ ex (some z))⁻¹ := by
      simp only [zpow_neg, Finset.prod_inv_distrib]
    rw [E1, pn, mul_right_comm, Units.mul_inv, one_mul]

theorem log_quot {K : Type} [Field K] {X : Scheme.{0}} [IsIntegral X] (y : Sp K ⟶ X) (w : AbsoluteValue K ℝ)
    {ι : Type} [Fintype ι] (T G : ι → X.functionFieldˣ)
    (hu : ∀ i, UnitAt (below y) ((T i * G i : X.functionFieldˣ) : X.functionField)) (g : X.functionField)
    (r : X.presheaf.stalk (below y)) (hr0 : (Scheme.stalkClosedPointTo y).hom r ≠ 0)
    (hr : algebraMap _ X.functionField r = g * ((∏ i, T i : X.functionFieldˣ) : X.functionField)) :
    UnitAt (below y) (g / ∏ i, (G i : X.functionField)) ∧
      Real.log (w (TrueGeo.valAt y (g / ∏ i, (G i : X.functionField)))) +
        ∑ i, Real.log (w (TrueGeo.valAt y ((T i * G i : X.functionFieldˣ) : X.functionField))) =
      Real.log (w ((Scheme.stalkClosedPointTo y).hom r)) := by
  obtain ⟨Us, hs⟩ := GlobalTheory.CovolFin.log_valAt_prod y w Finset.univ _ fun i _ => hu i
  have hru : IsUnit r := (isUnit_map_iff (Scheme.stalkClosedPointTo y).hom r).1 (isUnit_iff_ne_zero.2 hr0)
  have Ur : UnitAt (below y) (algebraMap _ X.functionField r) := ⟨r, hru, rfl⟩
  have hq : g / ∏ i, (G i : X.functionField) =
      algebraMap _ X.functionField r * ((∏ i, (T i * G i) : X.functionFieldˣ) : X.functionField)⁻¹ := by
    rw [hr, Finset.prod_mul_distrib, Units.val_mul, mul_inv, ← mul_assoc,
      mul_inv_cancel_right₀ (Units.ne_zero _), div_eq_mul_inv, Units.coe_prod]
  rw [hq]
  refine ⟨Ur.mul Us.inv, ?_⟩
  rw [SmallSec.valAt_mul Ur.regAt Us.inv.regAt, GlobalTheory.LineNorm.Neg.valAt_inv Us, map_mul, map_inv₀,
    Real.log_mul (w.pos (SmallSec.valAt_ne_zero Ur)).ne' (inv_ne_zero (w.pos (SmallSec.valAt_ne_zero Us)).ne'),
    Real.log_inv, hs, Base.valAt_stalk]
  ring

theorem prod_flat {G : Type} [CommGroup G] (t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → G) (τ : Psi H) (a : ℕ → Bool)
    (R : Option ℝ) : (∏ x : Letter Dw, t x.1 x.2 ^ (-exOf Dw (flatWt Dw τ) 0 (some x))) =
      ∏ i : Fin (Dw.p + Dw.q), ∏ x : Letter Dw, t x.1 x.2 ^ expo Dw (rootSym Dw a R τ.1 i) x := by
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun x _ => ?_
  rw [← GlobalTheory.CovolFin.zpow_finsum, ← congrFun (expo_detSym_eq Dw τ a R) x, detSym, GlobalTheory.CovolFin.expo_sum,
    Finset.sum_apply, Finset.sum_range]

theorem lgOf_eq (w : Pad.Sym E →₀ ℤ) (v : HeightOneSpectrum (𝓞 F)) (hp : (resP v).Prime) (ε : TrueGeo.Ext v)
    (y : TrueGeo.AlgPt Y.Y) : haveI := Fact.mk hp
    lgOf Y w v ε y = Real.log (ε.w (TrueGeo.valAt y.1 (((∏ x : Letter Dw,
        (Y.gr_spec (below y.1)).choose_spec.choose_spec.choose x.1 x.2 ^ expo Dw w x) *
        (eqn (divOf Y (expo Dw w)) (below y.1))⁻¹ : Y.Y.Fnˣ) : Y.Y.Fn))) +
      (-Real.log (ε.w (resP v)) / Real.log (resP v)) * w.sum fun b n => (n : ℝ) * lnStep Z.t
          (spMap ((ioOf (resP v) ε).comp (Scheme.stalkClosedPointTo y.1).hom) ≫ stalkPt Y.Y (below y.1) ≫ Y.π ≫ genι Z)
          (fun τ i => spMap (dualMap ((ioOf (resP v) ε).comp (Scheme.stalkClosedPointTo y.1).hom)) ≫
            (Y.gr_spec (below y.1)).choose_spec.choose.v τ i) (resP v) (b.1 (resP v)) b.2.2 :=
  dif_pos hp

theorem sum_lgOf (τ : Psi H) (a : ℕ → Bool) (R : Option ℝ) (v : HeightOneSpectrum (𝓞 F)) (hp : (resP v).Prime)
    (ha : a (resP v) = true) (ε : TrueGeo.Ext v) (y : TrueGeo.AlgPt Y.Y) : haveI := Fact.mk hp
    ∑ i : Fin (Dw.p + Dw.q), lgOf Y (rootSym Dw a R τ.1 i) v ε y =
      ∑ i : Fin (Dw.p + Dw.q), Real.log (ε.w (TrueGeo.valAt y.1 (((∏ x : Letter Dw,
        (Y.gr_spec (below y.1)).choose_spec.choose_spec.choose x.1 x.2 ^ expo Dw (rootSym Dw a R τ.1 i) x) *
        (eqn (divOf Y (expo Dw (rootSym Dw a R τ.1 i))) (below y.1))⁻¹ : Y.Y.Fnˣ) : Y.Y.Fn))) +
      (-Real.log (ε.w (resP v)) / Real.log (resP v)) *
        (lnDet Z.t (resP v)
          (spMap ((ioOf (resP v) ε).comp (Scheme.stalkClosedPointTo y.1).hom) ≫ stalkPt Y.Y (below y.1) ≫ Y.π ≫ genι Z)
          (fun τ i => spMap (dualMap ((ioOf (resP v) ε).comp (Scheme.stalkClosedPointTo y.1).hom)) ≫
            (Y.gr_spec (below y.1)).choose_spec.choose.v τ i) τ.1 - Dw.p * (vDiff E (resP v) * Real.log (resP v))) := by
  letI := Fact.mk hp
  rw [← sum_lnStep _ _ _ _ τ a ha R, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => lgOf_eq Y _ v hp ε y

theorem exists_coord {Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β} (Y : FlagCpt Z e) (Zc : Formalism.L2.Pj.Comp Xo c) (τ : Psi H)
    {f : Rul Xo c} (hf : f ∈ secZ Xo c (exOf Dw (flatWt Dw τ) 0))
    (hZ : letI := (constF e Y.Y).toAlgebra; GlobalTheory.AllWt.LiesOn Zc Y.y0) (hD : DetConst Z Zc τ.1 f)
    (la : HeightOneSpectrum (𝓞 c.F)) (p : ℕ) [Fact p.Prime] : ∃ ρ : ℝ, ∀ (io : AlgebraicClosure F →+* ℂ_[p]),
      (∀ b, ‖io (algebraMap F (AlgebraicClosure F) (e.symm b))‖ ≤ 1 ↔ la.valuation c.F b ≤ 1) →
      ∀ y : TrueGeo.AlgPt Y.Y, Y.π (below y.1) ∉ genBd Z → ∃ r : Y.Y.X.presheaf.stalk (below y.1),
        (Scheme.stalkClosedPointTo y.1).hom r ≠ 0 ∧
        algebraMap _ Y.Y.X.functionField r = Y.val f * ((∏ x : Letter Dw,
          (Y.gr_spec (below y.1)).choose_spec.choose_spec.choose x.1 x.2 ^ (-exOf Dw (flatWt Dw τ) 0 (some x)) :
            Y.Y.Fnˣ) : Y.Y.Fn) ∧
        Real.log ‖io ((Scheme.stalkClosedPointTo y.1).hom r)‖ + lnDet Z.t p
          (spMap (io.comp (Scheme.stalkClosedPointTo y.1).hom) ≫ stalkPt Y.Y (below y.1) ≫ Y.π ≫ genι Z)
          (fun τ i => spMap (dualMap (io.comp (Scheme.stalkClosedPointTo y.1).hom)) ≫
            (Y.gr_spec (below y.1)).choose_spec.choose.v τ i) τ.1 = ρ := by
  obtain ⟨ρ₀, hρ⟩ := hD la p
  refine ⟨ρ₀, fun io hind y hb => ?_⟩
  letI : Algebra c.F ℂ_[p] := ((io.comp (algebraMap F (AlgebraicClosure F))).comp e.symm.toRingHom).toAlgebra
  have hA : ∀ b, algebraMap c.F ℂ_[p] b = io (algebraMap F (AlgebraicClosure F) (e.symm b)) := fun _ => rfl
  have hsc : spMap (Scheme.stalkClosedPointTo y.1).hom ≫ stalkPt Y.Y (below y.1) = y.1 :=
    Scheme.Spec_stalkClosedPointTo_fromSpecStalk y.1
  obtain ⟨P, z, r, p1, p2, p3, p4, p5, p6⟩ := exists_point Y (below y.1) (Scheme.stalkClosedPointTo y.1).hom
    (by rw [← Category.assoc, hsc, y.2]) io hA hb _
    (Y.gr_spec (below y.1)).choose_spec.choose_spec.choose_spec.1 (ex := exOf Dw (flatWt Dw τ) 0) rfl hf Zc hZ
  have halg : IsAlgFr P := by
    haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure F) := Algebra.IsAlgebraic.trans ℚ F _
    exact ⟨AlgebraicClosure F, inferInstance, io, z, fun b =>
      (IsFractionRing.isAlgebraic_iff ℤ ℚ _).2 (Algebra.IsAlgebraic.isAlgebraic b), p1⟩
  obtain ⟨hne, hval⟩ := hρ hind P halg p2
  rw [p4, p3, p6] at hval
  rw [p6] at hne
  exact ⟨r, fun h => hne (by rw [h, map_zero]), p5, hval⟩

theorem real_step {A B κ L D d ρ : ℝ} (h₁ : A + B = κ * L) (h₂ : L + D = ρ) : A + (B + κ * (D - d)) = κ * (ρ - d) := by
  rw [← h₂, ← add_assoc, h₁]
  ring

theorem flagSt_holds : FlagSt := by
  intro E _ _ _ H Dw l Xo c Z F _ _ e Y Zc τ f hf hZ hD N hN a R v ha
  subst hN
  have hp := residueCharacteristic_prime v
  letI := Fact.mk hp
  obtain ⟨la, hla⟩ := exists_place e.symm v
  obtain ⟨ρ₀, hρ⟩ := exists_coord Y Zc τ hf hZ hD la (resP v)
  refine ⟨(-Real.log (NumberField.HeightOneSpectrum.adicAbv F v (resP v)) / Real.log (resP v)) *
    (ρ₀ - Dw.p * (vDiff E (resP v) * Real.log (resP v))), fun ε y hb => ?_⟩
  have hio := ioOf_le_one_iff (resP v) (residueCharacteristic_mem v) ε
  have hκ : NumberField.HeightOneSpectrum.adicAbv F v (resP v) = ε.w (resP v) := by rw [← ε.w_alg, map_natCast]
  obtain ⟨r, hr0, hr, hval⟩ := hρ (ioOf (resP v) ε)
    (fun b => (hio _).trans (by rw [ε.mem_O, ε.w_alg, adicAbv_le_one_iff, hla])) y hb
  rw [prod_flat _ τ a R] at hr
  obtain ⟨U, hU⟩ := log_quot y.1 ε.w _ _
    (fun i : Fin (Dw.p + Dw.q) => GlobalTheory.CombInd.Tens.unitAt_prod Y (rootSym Dw a R τ.1 i) (below y.1)) (Y.val f) r hr0 hr
  refine ⟨U, ?_⟩
  rw [sum_lgOf Y τ a R v hp ha ε y, hκ]
  exact real_step (hU.trans (log_w_eq (resP v) ε _ hio _)) hval

end GlobalTheory.DetHT.FlagNorm

end
end

open GlobalTheory.DetHT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_statement_holds : FlagSt := by
  atlas_forward_decl GlobalTheory.DetHT.FlagNorm.flagSt_holds
end

section
section
set_option autoImplicit false

noncomputable section

section Moduli

open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain
open scoped NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.FlatModel

namespace GlobalTheory.DetHT

theorem detConst_of (hT : TestPtSt) (hX : ExFrameSt) (hP : PointSt) {E : Type} [Field E] [NumberField E] [IsCMField E]
    [IsGalois ℚ E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
    (hpq : 1 ≤ Dw.p + Dw.q) (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c (algebraMap (𝓞 c.F) c.F)) (Zc : Formalism.L2.Pj.Comp Xo c)
    (τ : Psi H) {f : Rul Xo c} (hf : f ∈ secZ Xo c (exOf Dw (flatWt Dw τ) 0))
    (h : ∀ la : HeightOneSpectrum (𝓞 c.F), ∃ ρ : ℝ, ∀ w ∈ htValOn Zc la, w f = (ρ : EReal)) : DetConst Z Zc τ.1 f := by
  intro la p _
  obtain ⟨ρ, hρ⟩ := h la
  obtain ⟨K, hK⟩ := hP E H Dw τ p
  refine ⟨ρ * Real.log ((Valued.v : Valuation ℂ_[p] ℝ≥0) (p : ℂ_[p])) / (vLa la (p : c.F) : ℝ) + K, fun hla P hA hZ => ?_⟩
  obtain ⟨yb, hyb⟩ := hT E H Dw l Xo c Z p P hA
  obtain ⟨y, hy, hyP, Q, π, ψ, z, hQ, hz⟩ := hX E H Dw l Xo c hpq Z Zc la p hla P yb hyb hZ
  have h1 : val_vw la p (Valued.v : Valuation ℂ_[p] ℝ≥0) (evR Xo c f y) = (ρ : EReal) := hρ _ hy
  have h0 : evR Xo c f y ≠ 0 := fun e => by
    rw [e, val_vw_zero] at h1
    exact EReal.coe_ne_top ρ h1.symm
  obtain ⟨h2, h3⟩ := hK l Xo c Z f hf P y z yb hyP Q π ψ hQ hz h0
  refine ⟨h2, h3.trans (congrArg (· + K) ?_)⟩
  rw [val_vw_of_ne la p _ h0, EReal.coe_eq_coe_iff, coe_valued, coe_valued] at h1
  have hp0 : (p : ℂ_[p]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  have hp1 : ‖(p : ℂ_[p])‖ < 1 := by
    rw [← coe_valued]
    exact_mod_cast lt_one_of_not_isUnit (PadicComplexInt.integers p) (PadicComplexHost.not_isUnit_p p)
  have hl : Real.log ‖(p : ℂ_[p])‖ ≠ 0 := (Real.log_neg (norm_pos_iff.2 hp0) hp1).ne
  have hv : (vLa la (p : c.F) : ℝ) ≠ 0 := by
    have hc : (p : c.F) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
    have hne : la.valuation c.F (p : c.F) ≠ 1 := fun e => by
      have := (hla (p : c.F)⁻¹).2 (by rw [map_inv₀, e, inv_one])
      rw [map_inv₀, map_natCast, norm_inv] at this
      exact absurd (one_lt_inv₀ (norm_pos_iff.2 hp0) |>.2 hp1) this.not_gt
    have h0' : la.valuation c.F (p : c.F) ≠ 0 := (Valuation.ne_zero_iff _).2 hc
    rw [Int.cast_ne_zero, vLa, neg_ne_zero]
    intro e
    exact hne (by rw [← WithZero.exp_log h0', e, WithZero.exp_zero])
  rw [coe_valued, ← h1]
  field_simp

end GlobalTheory.DetHT

end Moduli

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.CoverNorm

namespace GlobalTheory.DetHT

theorem valAt_stalk {K : Type} [Field K] {Z : Scheme.{0}} [IsIntegral Z] (y : Sp K ⟶ Z) (a : Z.presheaf.stalk (below y)) :
    valAt y (algebraMap _ Z.functionField a) = (Scheme.stalkClosedPointTo y).hom a := by
  have h : GlobalTheory.Cartier.RegAt (below y) (algebraMap _ Z.functionField a) := ⟨a, rfl⟩
  rw [GlobalTheory.TrueGeo.valAt, dif_pos h, IsFractionRing.injective (Z.presheaf.stalk (below y)) Z.functionField h.choose_spec]

theorem valAt_inv_of_unit {K : Type} [Field K] {Z : Scheme.{0}} [IsIntegral Z] (y : Sp K ⟶ Z) {g : Z.functionField}
    (h : GlobalTheory.Cartier.UnitAt (below y) g) : valAt y g⁻¹ = (valAt y g)⁻¹ := by
  obtain ⟨a, ha, rfl⟩ := h
  obtain ⟨u, rfl⟩ := ha
  rw [← map_units_inv, valAt_stalk, valAt_stalk, map_units_inv]

theorem log_w_valAt_inv {F : Type} [Field F] [NumberField F] {Y : Var F} {v : HeightOneSpectrum (𝓞 F)} (e : Ext v)
    (y : AlgPt Y) {g : Y.Fn} (h : GlobalTheory.Cartier.UnitAt (below y.1) g) :
    Real.log (e.w (valAt y.1 g⁻¹)) = -Real.log (e.w (valAt y.1 g)) := by
  rw [valAt_inv_of_unit y.1 h, map_inv₀, Real.log_inv]

theorem nefOver_det_of (hG : GeoSt) (hA : AnyLevSt) (hT : TestPtSt) (hX : ExFrameSt) (hP : PointSt) (hF : FlagSt) :
    OnObj fun D O _ _ _ _ => ∀ (c : O.s.Comp) (Q : Finset ℕ) (l : ℕ), l ∈ Q → l.Prime → ∀ (V : Cover (O.var c)) (M : DV.Rt D.what₂.Tau O.N → HermLB V.p), (∀ x, Norms V (M x) (fun z => genAt (O.root0 c Q x).D z) (fun σ y => lnAdl (O.root0 c Q x) σ y) (fun v e y => (O.root0 c Q x).lg v e y)) → ∀ τ : D.what₂.Tau, NefOver (ArInt.comb M fun x => if x.1 = τ then 1 else 0) l ∧ NefOver (ArInt.comb M fun x => if x.1 = τ then -1 else 0) l := by
  intro D O _ _ _ _ _ _ c Q l hlQ hl V M hM τ
  haveI : IsGalois ℚ D.host.E := D.host.hostE_isGalois
  have hpq : 1 ≤ O.S.Dw.p + O.S.Dw.q := (one_le_two.trans O.S.two_le).trans O.S.rank_eq.ge
  obtain ⟨q, hq⟩ := GlobalTheory.T.flag_components_biject_moduli_components D O.A O.N O.j O.S O.κ O.s O.Φ
  let τ' : Psi O.A.H := ⟨DV.tauEmb D τ, O.A.cm τ⟩
  obtain ⟨f, hf, hc⟩ := hA _ O.A.H O.S.Dw O.κ.l O.s.Xo O.κ.c hpq O.κ.good
    (GlobalTheory.RankOneDatum.exists_datum_of_rt D O.A.H O.A.rt_eq O.A.cmHost_rootComplex_eq_pm_sqrt) O.κ.curve (q c) τ'
  have hD := detConst_of hT hX hP hpq O.s.T.Z (q c) τ' hf hc
  have key := hF _ O.A.H O.S.Dw O.κ.l O.s.Xo O.κ.c O.s.T.Z _ O.κ.e (O.Φ.C c) (q c) τ' f hf (hq c) hD O.N O.S.rank_eq
    (GlobalTheory.ShFam.Pad.ArIn.ind Q) none
  let W : (O.var c).X.Opens := (O.Φ.C c).π ⁻¹ᵁ (GlobalTheory.Toroidal.genBd O.s.T.Z).compl
  have hW : (W : Set (O.var c).X).Nonempty := by
    letI := (GlobalTheory.ShFam.constF O.κ.e (O.Φ.C c).Y).toAlgebra
    refine ⟨genericPoint _, fun h => h ⟨GlobalTheory.AllWt.ptF (O.Φ.C c).y0 (IsLocalRing.closedPoint _), ?_⟩⟩
    have := congrArg (fun g : Sp (O.var c).Fn ⟶ _ => g (IsLocalRing.closedPoint (O.var c).Fn)) (O.Φ.C c).y0_x
    simp only [Scheme.Hom.comp_apply] at this
    refine this.trans (congrArg (O.Φ.C c).π ?_)
    exact Scheme.fromSpecStalk_closedPoint
  have hv : ∀ v : HeightOneSpectrum (𝓞 D.what₂.LL), (l : 𝓞 D.what₂.LL) ∈ v.asIdeal →
      GlobalTheory.ShFam.Pad.ArIn.ind Q (resP v) = true := fun v hv => by
    simp [GlobalTheory.ShFam.Pad.ArIn.ind, (GlobalTheory.PlaceSum.residueCharacteristic_eq_iff v hl).2 hv, hlQ]
  have e₁ (n : ℤ) (z : (O.var c).X) : ∏ x : DV.Rt D.what₂.Tau O.N, genAt (O.root0 c Q x).D z ^ (if x.1 = τ then n else 0) =
      (∏ i : Fin O.N, genAt (divOf (O.Φ.C c) (expo O.S.Dw (rootSym O.S.Dw (GlobalTheory.ShFam.Pad.ArIn.ind Q) none τ'.1 i))) z) ^ n := by
    rw [Fintype.prod_prod_type, Finset.prod_eq_single τ (fun σ _ hσ => by simp [hσ]) (by simp), ← Finset.prod_zpow]
    simp only [if_true]
    rfl
  have e₂ (n : ℤ) (v e y) : ∑ x : DV.Rt D.what₂.Tau O.N, ((if x.1 = τ then n else 0 : ℤ) : ℝ) * (O.root0 c Q x).lg v e y =
      n * ∑ i : Fin O.N, lgOf (O.Φ.C c) (rootSym O.S.Dw (GlobalTheory.ShFam.Pad.ArIn.ind Q) none τ'.1 i) v e y := by
    rw [Fintype.sum_prod_type, Finset.sum_eq_single τ (fun σ _ hσ => by simp [hσ]) (by simp), Finset.mul_sum]
    simp only [if_true]
    rfl
  constructor
  · refine hG _ _ V _ _ _ _ (norms_comb hM _) ((O.Φ.C c).val f) W hW l hl fun v h => ?_
    obtain ⟨ρ, hρ⟩ := key v (hv v h)
    refine ⟨ρ, fun e y hy => ?_⟩
    rw [e₁, e₂, zpow_one, Int.cast_one, one_mul]
    exact hρ e y hy
  · refine hG _ _ V _ _ _ _ (norms_comb hM _) ((O.Φ.C c).val f)⁻¹ W hW l hl fun v h => ?_
    obtain ⟨ρ, hρ⟩ := key v (hv v h)
    refine ⟨-ρ, fun e y hy => ?_⟩
    obtain ⟨h₁, h₂⟩ := hρ e y hy
    rw [e₁, e₂, zpow_neg_one, inv_div_inv, ← inv_div, Int.cast_neg, Int.cast_one, neg_one_mul]
    refine ⟨h₁.inv, ?_⟩
    rw [log_w_valAt_inv e y h₁]
    linarith

theorem nefOver_det :
    Hypotheses2 → HypothesesH → OnObj fun D O _ _ _ _ => ∀ (c : O.s.Comp) (Q : Finset ℕ) (l : ℕ), l ∈ Q → l.Prime → ∀ (V : Cover (O.var c)) (M : DV.Rt D.what₂.Tau O.N → HermLB V.p), (∀ x, Norms V (M x) (fun z => genAt (O.root0 c Q x).D z) (fun σ y => lnAdl (O.root0 c Q x) σ y) (fun v e y => (O.root0 c Q x).lg v e y)) → ∀ τ : D.what₂.Tau, NefOver (ArInt.comb M fun x => if x.1 = τ then 1 else 0) l ∧ NefOver (ArInt.comb M fun x => if x.1 = τ then -1 else 0) l :=
  fun hP _ => nefOver_det_of (GlobalTheory.T.regular_local_implies_geometric GlobalTheory.T.RegularLocalStatement) (GlobalTheory.T.anyLevSt_of_covering hP) GlobalTheory.T.TestPointStatement GlobalTheory.T.ExistsFrameStatement
    (GlobalTheory.T.point_count_of_eigen_covolume_hypotheses GlobalTheory.T.ConnectingStatement GlobalTheory.T.EigenvalueStatement GlobalTheory.T.CovolumeStatement) GlobalTheory.T.flag_statement_holds

end GlobalTheory.DetHT

end
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.CoverNorm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_norm_nef_indicators : Hypotheses2 → HypothesesH → OnObj fun D O _ _ _ _ => ∀ (c : O.s.Comp) (Q : Finset ℕ) (l : ℕ), l ∈ Q → l.Prime → ∀ (V : Cover (O.var c)) (M : DV.Rt D.what₂.Tau O.N → HermLB V.p), (∀ x, Norms V (M x) (fun z => genAt (O.root0 c Q x).D z) (fun σ y => lnAdl (O.root0 c Q x) σ y) (fun v e y => (O.root0 c Q x).lg v e y)) → ∀ τ : D.what₂.Tau, NefOver (ArInt.comb M fun x => if x.1 = τ then 1 else 0) l ∧ NefOver (ArInt.comb M fun x => if x.1 = τ then -1 else 0) l := by
  atlas_forward_decl GlobalTheory.DetHT.nefOver_det
end
