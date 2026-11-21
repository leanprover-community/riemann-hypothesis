import Mathlib
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.NormComparisonConstants
import Formalism.LocalToGlobal.ProjectiveLattices.DepthTie
import Development.AbelianVarietyTheory.Definitions.Jets.EmbShortThLeThetaPlain
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ShortGenIndepConnection
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ChartIndependenceUnconditional
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsEquivariantFunOnSpanningFamilies
import Formalism.LocalToGlobal.ProjectiveLattices.LevelPb
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLevelMulSplit
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsDeltaDatumHigherLevel
import Development.AbelianVarietyTheory.Proofs.HeightProofs.FunctionFieldAlgClosedLevel
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SameSpaceOfLawsJ
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsPsiTieOfValues
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsSecCharVal

section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.FinalJoin GlobalTheory.CompRat
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem exists_coeff_deltaOK_of_cover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (d : DeltaDat Xo c 0) (p : ℕ) (I : Ideal (𝓞 E)), CoverOK d p I → RootOK d → (∃ ψ, ψ ≠ 1 ∧ d.PsiTie ψ) → ∃ φ : ∀ n, (Fin n → LevQ Dw d.l₂) → c.F, ∀ n, DeltaOK (GlobalTheory.FormTies.withCoeff d (φ n)) p I := by
  intro E _ _ _ H Dw l Xo c d p I hc hr ⟨ψ, hψ, ht⟩
  have key : ∀ n, ∃ φ : (Fin n → LevQ Dw d.l₂) → c.F, DeltaOK (GlobalTheory.FormTies.withCoeff d φ) p I := by
    intro n
    by_cases hn : Dw.p + Dw.q ≤ n
    · obtain ⟨φ, ph, x₀, h⟩ := GlobalTheory.exists_phiPin_of_character E H Dw l Xo c n
        (GlobalTheory.FormTies.withCoeff d (0 : (Fin n → LevQ Dw d.l₂) → c.F)) hc.2.2.1 hn ψ
      exact ⟨φ, hc, hr, fun _ => ⟨ph, ψ, x₀, hψ, h, ht⟩⟩
    · exact ⟨0, hc, hr, fun h => absurd h hn⟩
  choose φ hφ using key
  exact ⟨φ, hφ⟩

end GlobalTheory
end

section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.FinalJoin GlobalTheory.CompRat
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.function_field_alg_closed_level : ∀ (D : D7) (Q : Par D), Q.Pins → Q.Canon → ∀ n : ℕ, 0 < n → CurveOver (hostOfRecord D) (FO D) n → ∀ j, InR D j → ∀ (l₂ : Level Q.H) (Xo₂ : Moduli (Q.Dw j) l₂) (c₂ : Coeff l₂), l₂.A = 1 → l₂.M ∣ n → c₂.F = Q.c.F → FnAlgClosed Xo₂ c₂ := by
  first | exact @GlobalTheory.FinalJoin.FieldAlg.fnAlgClosed_of_pins | exact GlobalTheory.FinalJoin.FieldAlg.fnAlgClosed_of_pins | (intros; apply GlobalTheory.FinalJoin.FieldAlg.fnAlgClosed_of_pins <;> assumption)
end

section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.FinalJoin GlobalTheory.CompRat
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinalJoin.Cover

theorem zeta_mul_mem (F : IntermediateField ℚ ℂ) {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (h : n.Coprime m)
    (h1 : zeta m ∈ F) (h2 : zeta n ∈ F) : zeta (m * n) ∈ F := by
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.2 h
  have huv' : (u : ℂ) * n + v * m = 1 := by exact_mod_cast huv
  have hm' : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  have e : zeta (m * n) = zeta m ^ u * zeta n ^ v := by
    unfold zeta
    rw [← Complex.exp_int_mul, ← Complex.exp_int_mul, ← Complex.exp_add]
    congr 1
    push_cast
    field_simp
    linear_combination (-1 : ℂ) * huv'
  rw [e]
  exact mul_mem (zpow_mem h1 u) (zpow_mem h2 v)

theorem FO_le_coeff {D : D7} (Q : Par D) (h : Q.PinField) : FO D ≤ Q.c.F := by
  rw [FO, IntermediateField.adjoin_le_iff]
  rintro _ ⟨y, rfl⟩
  have e := h (Q.eO.symm y)
  rw [RingEquiv.apply_symm_apply] at e
  have e' : D.what₂.phiO y = ((Q.eO.symm y : Q.c.F) : ℂ) := e
  rw [e']
  exact SetLike.coe_mem _

theorem half_of_split (D : D7) {p : ℕ} (hp : SplitOK D p) (P : HeightOneSpectrum (𝓞 D.host.K))
    (hP : ((p : ℕ) : 𝓞 D.host.K) ∈ P.asIdeal) (I : Ideal (𝓞 D.host.E))
    (hI : I = P.asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E))) :
    I = Ideal.span {a | a ∈ I ∧ a ∈ Algebra.adjoin ℤ {w0E D}} ∧
      I * I.map (bH D) = Ideal.span {(p : 𝓞 D.host.E)} ∧ I ⊔ I.map (bH D) = ⊤ := by
  obtain ⟨e, he1, he2, hpb⟩ := LPb.pb_eq_JK D hp P hP
  rw [hpb, LPb.map_JK] at hI
  subst hI
  refine ⟨fromK_of_gen ⟨_, rfl, ?_⟩, ?_, ?_⟩
  · rintro y (rfl | hy)
    · exact Subalgebra.natCast_mem _ _
    · rw [Set.mem_singleton_iff.1 hy]
      exact Subalgebra.sub_mem _ (Algebra.subset_adjoin (Set.mem_singleton _)) (Subalgebra.intCast_mem _ _)
  · rw [LPb.QE_map_bar, LPb.QE_mul D _ _ he1 he2]
  · rw [LPb.QE_map_bar, ← Ideal.isCoprime_iff_sup_eq]
    exact LPb.QE_cop_self D _ _ he2

theorem exists_cover : ∀ (D : D7) (Q : Par D), Q.Pins → Q.Canon → ∀ p : ℕ, FieldOK D p → jacobiSym (-(D.host.d : ℤ)) p = 1 → ∀ (P : HeightOneSpectrum (𝓞 D.host.K)), ((p : ℕ) : 𝓞 D.host.K) ∈ P.asIdeal → p.Prime ∧ 5 ≤ p ∧ ∀ j, InR D j → ∃ d : DeltaDat (Q.Xo j) Q.c 0, CoverOK d p (P.asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E))) ∧ FnAlgClosed d.Xo₂ d.c₂ := by
  intro D Q hP hC p hK hj P hPp
  have hpp : p.Prime ∧ p % 15 = 1 ∧ ∀ i, p ≠ D.host.g i := by
    rcases hK.own with rfl | rfl
    · exact ⟨D.host.pde_prime, D.host.pde_mod.1, fun i => (D.host.pde_ne_g i).1⟩
    · exact ⟨D.host.pde'_prime, D.host.pde_mod.2, fun i => (D.host.pde_ne_g i).2⟩
  obtain ⟨hp, h15, hg⟩ := hpp
  have h5 : 5 ≤ p := by have := hp.two_le; omega
  refine ⟨hp, h5, fun j hjR => ?_⟩
  have hM : Q.l.M = D.host.g 0 * D.host.g 1 := hP.2.1.1
  have hA : Q.l.A = 1 := hP.2.1.2
  have hcop : p.Coprime Q.l.M := by
    rw [hM]
    exact Nat.Coprime.mul_right ((Nat.coprime_primes hp (D.host.g_prime 0)).2 (hg 0))
      ((Nat.coprime_primes hp (D.host.g_prime 1)).2 (hg 1))
  obtain ⟨h1, h2, h3⟩ := half_of_split D ⟨hp, by omega, hj⟩ P hPp _ rfl
  have hw : Q.H.w0 = w0E D := by rw [hC.1]; rfl
  have hb : (Q.H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) = bH D := by rw [hC.1]; rfl
  rw [← hw] at h1
  rw [← hb] at h2 h3
  obtain ⟨l₂, hd, hM₂, hMb, hA₂⟩ := (GlobalTheory.exists_level_mul_split _ Q.H Q.l).1 p _
    (hp.odd_of_ne_two (by omega)) hcop h1 h2 h3
  obtain ⟨-, hr, -, -⟩ := GlobalTheory.Member.exists_iotaOK D Q hP j hjR
  have hr1 : 1 ≤ (Q.Dw j).p + (Q.Dw j).q := by
    have h1 := D.R.two_le_m; have h2 := D.R.m_add_three_le_k
    rw [hr]; unfold Ranks.r; omega
  obtain ⟨Xo₂⟩ := GlobalTheory.Moduli.moduli_scheme_exists _ Q.H (Q.Dw j) l₂ hr1
  have hz : zeta Q.l.M ∈ Q.c.F := by
    have := Q.c.zeta_mem
    rwa [Level.M', hA, Nat.lcm_one_right] at this
  let c₂ : Coeff l₂ :=
    { F := Q.c.F
      fin := Q.c.fin
      conj := Q.c.conj
      zeta_mem := by
        rw [Level.M', hA₂, hA, Nat.lcm_one_right, hM₂]
        exact zeta_mul_mem _ (by have := Q.l.three_le; omega) hp.pos hcop hz (FO_le_coeff Q hP.2.2.1 hK.zetaP)
      le := by
        have := Q.c.le
        unfold KA at this ⊢
        rwa [hA₂] }
  obtain ⟨d, e1, e2, e3, -, -, -, hlev, hnab⟩ := GlobalTheory.LevelCover.exists_deltaDat_isLev _ Q.H (Q.Dw j) Q.l (Q.Xo j) Q.c
    hr1 0 p _ l₂ Xo₂ c₂ rfl hd hM₂ hcop hMb h3
  have hA' : d.l₂.A = 1 := by rw [e3, hA₂, hA]
  refine ⟨d, ⟨e1, e2, hlev, hA', hnab⟩, ?_⟩
  refine GlobalTheory.T.function_field_alg_closed_level D Q hP hC (D.host.g 0 * D.host.g 1 * p)
    (Nat.mul_pos (Nat.mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos) hp.pos) hK.curve j hjR d.l₂ d.Xo₂ d.c₂
    hA' ?_ d.hF
  rw [e3, hM₂, hM]

theorem exists_cover_of_fieldOK : ∀ (D : D7) (Q : Par D), Q.Pins → Q.Canon → ∀ p : ℕ, FieldOK D p → ∀ (P : HeightOneSpectrum (𝓞 D.host.K)), ((p : ℕ) : 𝓞 D.host.K) ∈ P.asIdeal → p.Prime ∧ 5 ≤ p ∧ ∀ j, InR D j → ∃ d : DeltaDat (Q.Xo j) Q.c 0, CoverOK d p (P.asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E))) ∧ FnAlgClosed d.Xo₂ d.c₂ := by
  intro D Q hP hC p hK
  refine exists_cover D Q hP hC p hK ?_
  have h : D.host.cls p = PrimeClass.splitK := hK.split
  exact ((Formalism.BasicNotions.primeClass_eq_splitK_iff D.host.toHostRaw).1 h).2.2.2

end GlobalTheory.FinalJoin.Cover
end

section
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.RunJoin GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 GlobalTheory.CompRat GlobalTheory.Member
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinalJoin2.Cover

theorem exists_cover : ∀ (D : D7) (Q : Par D), Q.Pins → Q.Canon → ∀ p : ℕ, FieldOK0 D p → jacobiSym (-(D.host.d : ℤ)) p = 1 → ∀ (P : HeightOneSpectrum (𝓞 D.host.K)), ((p : ℕ) : 𝓞 D.host.K) ∈ P.asIdeal → p.Prime ∧ 5 ≤ p ∧ ∀ j, InR D j → ∃ d : DeltaDat (Q.Xo j) Q.c 0, CoverOK d p (P.asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E))) ∧ FnAlgClosed d.Xo₂ d.c₂ := by
  intro D Q hP hC p hK hj P hPp
  have hpp : p.Prime ∧ p % 15 = 1 ∧ ∀ i, p ≠ D.host.g i := by
    rcases hK.own with rfl | rfl
    · exact ⟨D.host.pde_prime, D.host.pde_mod.1, fun i => (D.host.pde_ne_g i).1⟩
    · exact ⟨D.host.pde'_prime, D.host.pde_mod.2, fun i => (D.host.pde_ne_g i).2⟩
  obtain ⟨hp, h15, hg⟩ := hpp
  have h5 : 5 ≤ p := by have := hp.two_le; omega
  refine ⟨hp, h5, fun j hjR => ?_⟩
  have hM : Q.l.M = D.host.g 0 * D.host.g 1 := hP.2.1.1
  have hA : Q.l.A = 1 := hP.2.1.2
  have hcop : p.Coprime Q.l.M := by
    rw [hM]
    exact Nat.Coprime.mul_right ((Nat.coprime_primes hp (D.host.g_prime 0)).2 (hg 0))
      ((Nat.coprime_primes hp (D.host.g_prime 1)).2 (hg 1))
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.FinalJoin.Cover.half_of_split D ⟨hp, by omega, hj⟩ P hPp _ rfl
  have hw : Q.H.w0 = w0E D := by rw [hC.1]; rfl
  have hb : (Q.H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) = bH D := by rw [hC.1]; rfl
  rw [← hw] at h1
  rw [← hb] at h2 h3
  obtain ⟨l₂, hd, hM₂, hMb, hA₂⟩ := (GlobalTheory.exists_level_mul_split _ Q.H Q.l).1 p _
    (hp.odd_of_ne_two (by omega)) hcop h1 h2 h3
  obtain ⟨-, hr, -, -⟩ := GlobalTheory.Member.exists_iotaOK D Q hP j hjR
  have hr1 : 1 ≤ (Q.Dw j).p + (Q.Dw j).q := by
    have h1 := D.R.two_le_m; have h2 := D.R.m_add_three_le_k
    rw [hr]; unfold Ranks.r; omega
  obtain ⟨Xo₂⟩ := GlobalTheory.Moduli.moduli_scheme_exists _ Q.H (Q.Dw j) l₂ hr1
  have hz : zeta Q.l.M ∈ Q.c.F := by
    have := Q.c.zeta_mem
    rwa [Level.M', hA, Nat.lcm_one_right] at this
  let c₂ : Coeff l₂ :=
    { F := Q.c.F
      fin := Q.c.fin
      conj := Q.c.conj
      zeta_mem := by
        rw [Level.M', hA₂, hA, Nat.lcm_one_right, hM₂]
        exact GlobalTheory.FinalJoin.Cover.zeta_mul_mem _ (by have := Q.l.three_le; omega) hp.pos hcop hz (GlobalTheory.FinalJoin.Cover.FO_le_coeff Q hP.2.2.1 hK.zetaP)
      le := by
        have := Q.c.le
        unfold KA at this ⊢
        rwa [hA₂] }
  obtain ⟨d, e1, e2, e3, -, -, -, hlev, hnab⟩ := GlobalTheory.LevelCover.exists_deltaDat_isLev _ Q.H (Q.Dw j) Q.l (Q.Xo j) Q.c
    hr1 0 p _ l₂ Xo₂ c₂ rfl hd hM₂ hcop hMb h3
  have hA' : d.l₂.A = 1 := by rw [e3, hA₂, hA]
  refine ⟨d, ⟨e1, e2, hlev, hA', hnab⟩, ?_⟩
  refine GlobalTheory.FinalJoin.FieldAlg.fnAlgClosed_of_pins D Q hP hC (D.host.g 0 * D.host.g 1 * p)
    (Nat.mul_pos (Nat.mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos) hp.pos) hK.curve j hjR d.l₂ d.Xo₂ d.c₂
    hA' ?_ d.hF
  rw [e3, hM₂, hM]

theorem exists_cover_of_fieldOK : ∀ (D : D7) (Q : Par D), Q.Pins → Q.Canon → ∀ p : ℕ, FieldOK0 D p → ∀ (P : HeightOneSpectrum (𝓞 D.host.K)), ((p : ℕ) : 𝓞 D.host.K) ∈ P.asIdeal → p.Prime ∧ 5 ≤ p ∧ ∀ j, InR D j → ∃ d : DeltaDat (Q.Xo j) Q.c 0, CoverOK d p (P.asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E))) ∧ FnAlgClosed d.Xo₂ d.c₂ := by
  intro D Q hP hC p hK
  refine exists_cover D Q hP hC p hK ?_
  have h : D.host.cls p = PrimeClass.splitK := hK.split
  exact ((primeClass_eq_splitK_iff D.host.toHostRaw).1 h).2.2.2

end GlobalTheory.FinalJoin2.Cover
end

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.RunJoin GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 GlobalTheory.CompRat GlobalTheory.Member
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_specialPrime_levelCover_of_fieldConditions : ∀ (D : D7) (Q : Par D), Q.Pins → Q.Canon → ∀ p : ℕ, FieldOK0 D p → ∀ (P : HeightOneSpectrum (𝓞 D.host.K)), ((p : ℕ) : 𝓞 D.host.K) ∈ P.asIdeal → p.Prime ∧ 5 ≤ p ∧ ∀ j, InR D j → ∃ d : DeltaDat (Q.Xo j) Q.c 0, CoverOK d p (P.asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E))) ∧ FnAlgClosed d.Xo₂ d.c₂ := by
  atlas_forward_decl GlobalTheory.FinalJoin2.Cover.exists_cover_of_fieldOK
end

section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.FinalJoin GlobalTheory.CompRat
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinalJoin

theorem laws_short_of_deltaOK : ∀ (D : D7) (J : CoreJ D) (T : Top D), LawsJ J → LawsP T → T.toCore = J.toCore → 0 ∉ D.host.levelPrimes → ∀ (p : ℕ) (I : Ideal (𝓞 D.host.E)), (p = D.host.pde ∨ p = D.host.pde') → ∀ dd : ∀ j n, DeltaDat (T.Q.Xo j) T.Q.c n, (∀ j, InR D j → ∀ n, DeltaOK (dd j n) p I) → LawsP ({ T with dδ := dd } : Top D) ∧ LawsSh ({ T with dδ := dd } : Top D) := by
  intro D J T hJ h hT h0 p I hp dd hd
  have h' : LawsP ({ T with dδ := dd } : Top D) := { h with }
  have hb : 0 < badN D := by
    have := D.host.qd_big
    unfold badN
    exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos D.host.QS_pos (by omega)) (by omega))
      (Finset.prod_pos fun x hx => Nat.pos_of_ne_zero fun h => h0 (h ▸ hx))
  refine ⟨h', GlobalTheory.ShortLaws.lawsSh_of_pinned GlobalTheory.chartIndependence_unconditional _ h' hb
    (GlobalTheory.ShortLaws.sameSpace_of_lawsJ J T hJ hT) p hp fun j hj n => ?_⟩
  obtain ⟨⟨h1, -, h3, h4, h5⟩, ⟨h6, h7⟩, h8⟩ := hd j hj n
  exact ⟨h1, h3, h4, h5, h6, h7, h8⟩

end GlobalTheory.FinalJoin
end

section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.RunJoin GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 GlobalTheory.CompRat GlobalTheory.Member
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinalJoin2.FullExt

theorem exists_delta_xiAt_noVol (D : D7) (J : CoreJ D) (hJ : LawsJ J) (hP : J.Q.Pins) (hC : J.Q.Canon) (p : ℕ) (hF : FieldOK0 D p)
    (P : HeightOneSpectrum (𝓞 D.host.K)) (hp : ((p : ℕ) : 𝓞 D.host.K) ∈ P.asIdeal) (xi : (AfE D)ˣ →* ℂˣ)
    (hxi : XiOK D p xi) (j : ℕ) (hj : InR D j) :
    ∃ e : ∀ n, DeltaDat (J.Q.Xo j) J.Q.c n, ∀ n, (∃ φ, e n = GlobalTheory.FormTies.withCoeff (e 0) φ) ∧
      DeltaOK (e n) p (P.asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E))) ∧ XiAt J j (e n) xi := by
  obtain ⟨hpr, -, hd⟩ := GlobalTheory.T.exists_specialPrime_levelCover_of_fieldConditions D J.Q hP hC p hF P hp
  obtain ⟨d, hc, ha⟩ := hd j hj
  obtain ⟨f, hc', hr', hx⟩ := GlobalTheory.XiFun.exists_fun_xiAt D J hJ j hj p _ d xi hc ha hxi
  have ht := GlobalTheory.TwistTie.exists_psiTie_of_xiAt D J hJ j hj p _ { d with cδ := f } xi hpr hc' ha hxi hx
  obtain ⟨φ, hφ⟩ := GlobalTheory.exists_coeff_deltaOK_of_cover _ _ _ _ _ _ _ p _ hc' hr' ht
  exact ⟨fun n => GlobalTheory.FormTies.withCoeff { d with cδ := f } (φ n), fun n => ⟨⟨φ n, rfl⟩, hφ n, hx⟩⟩

theorem exists_full_of_xiOK_noVol : ∀ (D : D7) (J : CoreJ D) (T : Top D), LawsJ J → LawsP T → T.toCore = J.toCore → T.Q.Canon → ∀ p : ℕ, FieldOK0 D p → ∀ (P : HeightOneSpectrum (𝓞 D.host.K)), ((p : ℕ) : 𝓞 D.host.K) ∈ P.asIdeal → ∀ xi, XiOK D p xi → ∃ (dd : ∀ j n, DeltaDat (T.Q.Xo j) T.Q.c n) (TF : Full D), LawsFull TF ∧ TF.toTop = { T with dδ := dd } ∧ TF.J = J ∧ TF.xi = xi ∧ TF.half₂ = (P.asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E))) ∧ ∀ j, InR D j → GlobalTheory.FormTies.OneCover TF.toTop j ∧ ∀ n, (TF.dδ j n).pd = p := by
  intro D J T hJ hT hc hC p hF P hp xi hxi
  obtain ⟨C, G, nab, d₀⟩ := T
  obtain ⟨C', cE, chiW, x₀, iota⟩ := J
  dsimp only at hc
  subst hc
  have key : ∀ j, ∃ e : ∀ n, DeltaDat (C.Q.Xo j) C.Q.c n, InR D j → ∀ n, (∃ φ, e n = GlobalTheory.FormTies.withCoeff (e 0) φ) ∧
      DeltaOK (e n) p (P.asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E))) ∧
        XiAt (⟨C, cE, chiW, x₀, iota⟩ : CoreJ D) j (e n) xi := by
    intro j
    by_cases hj : InR D j
    · obtain ⟨e, he⟩ := exists_delta_xiAt_noVol D ⟨C, cE, chiW, x₀, iota⟩ hJ hT.pins hC p hF P hp xi hxi j hj
      exact ⟨e, fun _ => he⟩
    · exact ⟨d₀ j, fun h => absurd h hj⟩
  choose dd hdd using key
  obtain ⟨hLP, hLS⟩ := GlobalTheory.FinalJoin.laws_short_of_deltaOK D ⟨C, cE, chiW, x₀, iota⟩ ⟨C, G, nab, d₀⟩ hJ hT rfl hF.bad p _ hF.own dd
    (fun j hj n => (hdd j hj n).2.1)
  refine ⟨dd, ⟨⟨C, G, nab, dd⟩, cE, chiW, x₀, iota, xi, P.asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E))⟩,
    ⟨hLP, hJ, hLS, hC, fun j hj n => (hdd j hj n).2.1.1.2.2.2.1, fun j hj n => (hdd j hj n).2.1.1.2.1,
      fun j hj n s nab' hn a _ => ?_, fun j hj n => (hdd j hj n).2.2⟩, rfl, rfl, rfl, rfl,
    fun j hj => ⟨fun n => (hdd j hj n).1, fun n => (hdd j hj n).2.1.1.1⟩⟩
  exact GlobalTheory.shortGen_indep_connection GlobalTheory.chartIndependence_unconditional _ _ _ _ _ _ n (dd j n) (nab j) _ _
    (hdd j hj n).2.1.1.2.2.2.2 s nab' hn a

end GlobalTheory.FinalJoin2.FullExt
end
