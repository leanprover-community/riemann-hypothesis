import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
import Development.AutomorphicSpectrum.Proofs.TwistedProofs.MemIntROfFinPart

section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

namespace PositivityTheory.Rg.Rsw.L.LLatBound

variable {D : D7}

theorem tsum_GQ (V : HSp D) (n : ℕ) (γ : GA D V) (hγ : γ ∈ GQ V) (F : Mx D V.rank n → ℝ≥0∞) :
    ∑' x : {x : Matrix (Fin V.rank) (Fin n) D.host.E // x.rank = V.rank}, F (mm (mt V γ) (rat x.1)) =
      ∑' x : {x : Matrix (Fin V.rank) (Fin n) D.host.E // x.rank = V.rank}, F (rat x.1) := by
  obtain ⟨g, hg⟩ := mem_ratMx.1 ((mem_GQ_iff V γ).1 hγ)
  obtain ⟨g', hg'⟩ := mem_ratMx.1 ((mem_GQ_iff V γ⁻¹).1 (inv_mem hγ))
  have h1 : g' * g = 1 := rat_injective (by rw [rat_mul, hg, hg', rat_one]; exact mt_inv_mul V γ)
  have h2 : g * g' = 1 := rat_injective (by rw [rat_mul, hg, hg', rat_one]; exact mt_mul_inv V γ)
  have hu : IsUnit g.det := isUnit_iff_exists_inv.2 ⟨g'.det, by rw [← Matrix.det_mul, h2, Matrix.det_one]⟩
  have hu' : IsUnit g'.det := isUnit_iff_exists_inv.2 ⟨g.det, by rw [← Matrix.det_mul, h1, Matrix.det_one]⟩
  let e : {x : Matrix (Fin V.rank) (Fin n) D.host.E // x.rank = V.rank} ≃
      {x : Matrix (Fin V.rank) (Fin n) D.host.E // x.rank = V.rank} :=
    { toFun := fun x => ⟨g * x.1, by rw [Matrix.rank_mul_eq_right_of_isUnit_det g x.1 hu]; exact x.2⟩
      invFun := fun x => ⟨g' * x.1, by rw [Matrix.rank_mul_eq_right_of_isUnit_det g' x.1 hu']; exact x.2⟩
      left_inv := fun x => Subtype.ext (by simp only [← Matrix.mul_assoc, h1, Matrix.one_mul])
      right_inv := fun x => Subtype.ext (by simp only [← Matrix.mul_assoc, h2, Matrix.one_mul]) }
  rw [← e.tsum_eq (fun x => F (rat x.1))]
  refine tsum_congr fun x => ?_
  show F _ = F (rat (g * x.1))
  rw [rat_mul, hg]

end PositivityTheory.Rg.Rsw.L.LLatBound

end
end

section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

namespace PositivityTheory.Rg.Rsw.L.LLatBound

variable {D : D7}

theorem fullRank_col (D : D7) (a n n₀ : ℕ) (hn₀ : 0 < n₀) (f : SchwartzMap (D.what₂.Tau → Fin a → Fin n → ℂ) ℂ) :
    ∃ C : ℝ, ∀ B : D.what₂.Tau → Matrix (Fin a) (Fin a) ℂ, (∀ τ, ‖(B τ).det‖ = 1) →
      ∑' ξ : {ξ : Matrix (Fin a) (Fin n) D.host.E // ξ.rank = a ∧ ∀ i j, (n₀ : D.host.E) * ξ i j ∈ GlobalTheory.CompanionTheory.Ipf.Bdd.intR D},
        ‖f (fun τ => B τ * ξ.1.map (tauE D τ))‖ₑ ≤ ENNReal.ofReal C := by
  haveI := GlobalTheory.CompanionTheory.Ipf.Bdd.nonempty_tau D
  obtain ⟨e, he⟩ : ∃ e : (D.what₂.Tau → Fin n → Fin a → ℂ) ≃ₗ[ℝ] (D.what₂.Tau → Fin a → Fin n → ℂ),
      ∀ x τ i j, e x τ i j = x τ j i :=
    ⟨{ toFun := fun x τ i j => x τ j i
       invFun := fun y τ j i => y τ i j
       map_add' := fun _ _ => rfl
       map_smul' := fun _ _ => rfl
       left_inv := fun _ => rfl
       right_inv := fun _ => rfl }, fun _ _ _ _ => rfl⟩
  obtain ⟨C, hC⟩ := GlobalTheory.CompanionTheory.Twist.FullRank.tsum_schwartz_fullRank_le D.host.E (GlobalTheory.CompanionTheory.Ipf.Bdd.intR D)
    D.what₂.Tau (tauE D) (fun z hz h0 => GlobalTheory.CompanionTheory.Ipf.Bdd.one_le_prod_tauE z hz h0) a n n₀ hn₀
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℝ e.toContinuousLinearEquiv f)
  refine ⟨C, fun B hB => ?_⟩
  have hBt : ∀ τ, ‖(B τ)ᵀ.det‖ = 1 := fun τ => by
    rw [Matrix.det_transpose]
    exact hB τ
  obtain ⟨T, hT⟩ : ∃ T : {γ : Matrix (Fin n) (Fin a) D.host.E //
        γ.rank = a ∧ ∀ i j, (n₀ : D.host.E) * γ i j ∈ GlobalTheory.CompanionTheory.Ipf.Bdd.intR D} ≃
      {ξ : Matrix (Fin a) (Fin n) D.host.E //
        ξ.rank = a ∧ ∀ i j, (n₀ : D.host.E) * ξ i j ∈ GlobalTheory.CompanionTheory.Ipf.Bdd.intR D},
      ∀ γ, (T γ).1 = γ.1ᵀ :=
    ⟨{ toFun := fun γ => ⟨γ.1ᵀ, by rw [Matrix.rank_transpose]; exact γ.2.1, fun i j => γ.2.2 j i⟩
       invFun := fun ξ => ⟨ξ.1ᵀ, by rw [Matrix.rank_transpose]; exact ξ.2.1, fun i j => ξ.2.2 j i⟩
       left_inv := fun γ => Subtype.ext (Matrix.transpose_transpose _)
       right_inv := fun ξ => Subtype.ext (Matrix.transpose_transpose _) }, fun _ => rfl⟩
  rw [← T.tsum_eq]
  refine le_trans (le_of_eq (tsum_congr fun γ => ?_)) (hC (fun τ => (B τ)ᵀ) hBt)
  simp only [SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply]
  congr 2
  funext τ i j
  rw [LinearEquiv.coe_toContinuousLinearEquiv']
  refine Eq.trans ?_ (he _ τ i j).symm
  rw [hT]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, mul_comm]

end PositivityTheory.Rg.Rsw.L.LLatBound

end
end

section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

namespace PositivityTheory.Rg.Rsw.L.LLatBound

variable {D : D7}

theorem mtL_mul (V : HSp D) (g h : GA D V) : mt V (g * h) = mt V g * mt V h := rfl

theorem mtL_one (V : HSp D) : mt V 1 = 1 := rfl

theorem finPart_mtL {V : HSp D} {a : GA D V} (ha : a ∈ GinfC V) : (mt V a).map (finPart D) = 1 := by
  have h0 : finHom V a = 1 := ha
  have h1 : (finHom V a).1 = 1 := by rw [h0]; rfl
  exact h1

theorem den_finL {ι : Type} [Fintype ι] (z : ι → Af D.host.F ⊗[D.host.F] D.host.E) :
    ∃ N : ℕ, 0 < N ∧ ∀ i, N • z i ∈ intAE D := by
  classical
  choose N hN hNz using fun i => GlobalTheory.CompanionTheory.Ipf.Bdd.den_one (D := D) (z i)
  refine ⟨∏ i, N i, Finset.prod_pos fun i _ => hN i, fun i => ?_⟩
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i), mul_comm, mul_smul]
  exact AddSubgroup.nsmul_mem _ (hNz i) _

theorem compAt_mt_GfC (θ : InfFam D) (V : HSp D) {k : GA D V} (hk : k ∈ GfC V) (τ : D.what₂.Tau) :
    compAt θ τ (mt V k) = 1 := by
  have h0 : infHom V k = 1 := hk
  have h : (mt V k).map (infPart D) = 1 := by
    have h1 : (infHom V k).1 = 1 := by rw [h0]; rfl
    exact h1
  ext i j
  have hij := congrFun (congrFun h i) j
  simp only [Matrix.map_apply] at hij
  simp only [compAt, Matrix.map_apply, hij, Matrix.one_apply]
  split_ifs <;> simp

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem gen_bound_col {θ : InfFam D} (hθ : IsInfFam θ) (V : HSp D) (n : ℕ) (y : GA D V)
    (f : SchwartzMap (D.what₂.Tau → Fin V.rank → Fin n → ℂ) ℂ)
    (g : (Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ)
    (hg : g ∈ GlobalTheory.WeilM.SB (Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E)) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ a ∈ GinfC V, ∀ k ∈ GfC V, (∀ i j, finPart D (mt V k⁻¹ i j) ∈ intAE D) →
      ∑' x : {x : Matrix (Fin V.rank) (Fin n) D.host.E // x.rank = V.rank},
        ‖f (fun τ i j => compAt θ τ (mm (mt V (k * a * y)) (rat x.1)) i j) *
          g (fun i j => finPart D ((mm (mt V (k * a * y)) (rat x.1)) i j))‖ₑ ≤ C := by
  obtain ⟨Mg, hMg⟩ := hg.1.continuous.bounded_above_of_compact_support hg.2
  obtain ⟨N, hN, hNK⟩ := GlobalTheory.CompanionTheory.Ipf.Bdd.exists_den_matrix (D := D) (a := V.rank) (b := n) (K := tsupport g) hg.2
  obtain ⟨M, hM, hMy⟩ := den_finL (D := D)
    (fun p : Fin V.rank × Fin V.rank => finPart D (mt V y⁻¹ p.1 p.2))
  obtain ⟨C₀, hC₀⟩ := fullRank_col D V.rank n (N * M) (Nat.mul_pos hN hM) f
  refine ⟨ENNReal.ofReal C₀ * ENNReal.ofReal Mg, ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top,
    fun a ha k hk hki => ?_⟩
  set B : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ := fun τ => compAt θ τ (mt V (a * y)) with hBdef
  have hB : ∀ τ, ‖(B τ).det‖ = 1 := fun τ => GlobalTheory.CompanionTheory.Ipf.Bdd.norm_det_compAt hθ τ V (a * y)
  have hmt : mt V (k * a * y) = mt V k * mt V (a * y) := by
    rw [mul_assoc, mtL_mul]

  have hinf : ∀ x : Matrix (Fin V.rank) (Fin n) D.host.E,
      (fun τ i j => compAt θ τ (mm (mt V (k * a * y)) (rat x)) i j) = fun τ => B τ * x.map (tauE D τ) := by
    intro x
    funext τ i j
    have e1 := GlobalTheory.CompanionTheory.Ipf.Bdd.compAt_mulM θ τ (mt V (k * a * y)) (rat x)
    have e2 := GlobalTheory.CompanionTheory.Ipf.Bdd.compAt_mulM θ τ (mt V k) (mt V (a * y))
    have e0 : compAt θ τ (rat x) = x.map (tauE D τ) := GlobalTheory.CompanionTheory.Ipf.Bdd.compAt_rat hθ τ x
    rw [e0] at e1
    rw [compAt_mt_GfC θ V hk τ, Matrix.one_mul] at e2
    have e4 : compAt θ τ (mt V (k * a * y)) = B τ := by
      rw [hmt]; exact e2
    have e3 : compAt θ τ (mm (mt V (k * a * y)) (rat x)) = B τ * x.map (tauE D τ) := by
      rw [← e4]; exact e1
    rw [e3]

  set Yf : Matrix (Fin V.rank) (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E) := (mt V y).map (finPart D) with hYf
  set Yi : Matrix (Fin V.rank) (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E) := (mt V y⁻¹).map (finPart D) with hYi
  set Kf : Matrix (Fin V.rank) (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E) := (mt V k).map (finPart D) with hKf
  set Ki : Matrix (Fin V.rank) (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E) := (mt V k⁻¹).map (finPart D) with hKi
  have hYY : Yi * Yf = 1 := by
    rw [hYi, hYf, ← Matrix.map_mul, ← mtL_mul, inv_mul_cancel, mtL_one]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have hKK : Ki * Kf = 1 := by
    rw [hKi, hKf, ← Matrix.map_mul, ← mtL_mul, inv_mul_cancel, mtL_one]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have hfin : ∀ x : Matrix (Fin V.rank) (Fin n) D.host.E,
      (mm (mt V (k * a * y)) (rat x)).map (finPart D) = Kf * Yf * x.map (fun c => finPart D (incA D c)) := by
    intro x
    have : (mt V (a * y)).map (finPart D) = Yf := by
      rw [mtL_mul, Matrix.map_mul, finPart_mtL ha, Matrix.one_mul]
    show (mt V (k * a * y) * rat x).map (finPart D) = _
    rw [Matrix.map_mul, hmt, Matrix.map_mul, this]
    rfl

  have hden : ∀ x : Matrix (Fin V.rank) (Fin n) D.host.E,
      g (fun i j => finPart D ((mm (mt V (k * a * y)) (rat x)) i j)) ≠ 0 →
        ∀ i j, ((N * M : ℕ) : D.host.E) * x i j ∈ GlobalTheory.CompanionTheory.Ipf.Bdd.intR D := by
    intro x hx i j
    set Z : Matrix (Fin V.rank) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E) :=
      (mm (mt V (k * a * y)) (rat x)).map (finPart D) with hZ
    have hZK : Z ∈ tsupport g := subset_tsupport _ hx
    have hxZ : x.map (fun c => finPart D (incA D c)) = Yi * (Ki * Z) := by
      rw [hZ, hfin x, ← Matrix.mul_assoc Ki, ← Matrix.mul_assoc Ki, hKK, Matrix.one_mul, ← Matrix.mul_assoc,
        hYY, Matrix.one_mul]
    refine GlobalTheory.CompanionTheory.Ipf.Bdd.mem_intR_of_finPart ?_
    have e : finPart D (incA D (((N * M : ℕ) : D.host.E) * x i j)) =
        ∑ l, ∑ m, (M • Yi i l) * (Ki l m * (N • Z m j)) := by
      have hij : finPart D (incA D (x i j)) = (Yi * (Ki * Z)) i j := by
        rw [← hxZ]; rfl
      rw [map_mul, map_mul, hij, Matrix.mul_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [Matrix.mul_apply, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      simp only [map_natCast, nsmul_eq_mul]
      push_cast
      ring
    rw [e]
    refine sum_mem fun l _ => sum_mem fun m _ => ?_
    exact GlobalTheory.CompanionTheory.Ipf.Bdd.mul_mem_int (hMy (i, l)) (GlobalTheory.CompanionTheory.Ipf.Bdd.mul_mem_int (hki l m) (hNK Z hZK m j))

  set S₁ : Set (Matrix (Fin V.rank) (Fin n) D.host.E) := {x | x.rank = V.rank} with hS₁
  set S₂ : Set (Matrix (Fin V.rank) (Fin n) D.host.E) :=
    {x | x.rank = V.rank ∧ ∀ i j, ((N * M : ℕ) : D.host.E) * x i j ∈ GlobalTheory.CompanionTheory.Ipf.Bdd.intR D} with hS₂
  set F : Matrix (Fin V.rank) (Fin n) D.host.E → ℝ≥0∞ := fun x =>
    ‖f (fun τ i j => compAt θ τ (mm (mt V (k * a * y)) (rat x)) i j) *
      g (fun i j => finPart D ((mm (mt V (k * a * y)) (rat x)) i j))‖ₑ with hF
  set G : Matrix (Fin V.rank) (Fin n) D.host.E → ℝ≥0∞ := fun x =>
    ‖f (fun τ => B τ * x.map (tauE D τ))‖ₑ * ENNReal.ofReal Mg with hG
  have e1 : ∑' x : {x : Matrix (Fin V.rank) (Fin n) D.host.E // x.rank = V.rank}, F x.1 = ∑' x, S₁.indicator F x :=
    tsum_subtype S₁ F
  have e2 : ∑' x : S₂, G x.1 = ∑' x, S₂.indicator G x := tsum_subtype S₂ G
  have hle : ∀ x, S₁.indicator F x ≤ S₂.indicator G x := by
    intro x
    by_cases h1 : x ∈ S₁
    · rw [Set.indicator_of_mem h1]
      by_cases h0 : g (fun i j => finPart D ((mm (mt V (k * a * y)) (rat x)) i j)) = 0
      · have : F x = 0 := by simp only [hF, h0, mul_zero, enorm_zero]
        rw [this]; exact zero_le
      · have h2 : x ∈ S₂ := ⟨h1, hden x h0⟩
        rw [Set.indicator_of_mem h2]
        simp only [hF, hG]
        rw [hinf x, enorm_mul]
        gcongr
        rw [← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (hMg _)
    · rw [Set.indicator_of_notMem h1]; exact zero_le
  show ∑' x : {x : Matrix (Fin V.rank) (Fin n) D.host.E // x.rank = V.rank}, F x.1 ≤ _
  rw [e1]
  calc ∑' x, S₁.indicator F x ≤ ∑' x, S₂.indicator G x := ENNReal.tsum_le_tsum hle
    _ = ∑' x : S₂, G x.1 := e2.symm
    _ = (∑' x : S₂, ‖f (fun τ => B τ * x.1.map (tauE D τ))‖ₑ) * ENNReal.ofReal Mg := ENNReal.tsum_mul_right
    _ ≤ ENNReal.ofReal C₀ * ENNReal.ofReal Mg := by
        gcongr
        exact hC₀ B hB

end PositivityTheory.Rg.Rsw.L.LLatBound

end
end

section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

namespace PositivityTheory.Rg.Rsw.L.LLatBound

variable {D : D7}

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem exists_intOpen (V : HSp D) : ∃ U : Subgroup (GA D V), IsOpen (U : Set (GA D V)) ∧
    ∀ k ∈ U, ∀ i j, finPart D (mt V k i j) ∈ intAE D := by
  have hfc : Continuous (finPart D) := GlobalTheory.Member.continuous_finPart D
  have hint : ∀ (A B : Mx D V.rank V.rank), (∀ i j, finPart D (A i j) ∈ intAE D) → (∀ i j, finPart D (B i j) ∈ intAE D) →
      ∀ i j, finPart D ((A * B) i j) ∈ intAE D := by
    intro A B hA hB i j
    rw [Matrix.mul_apply, map_sum]
    exact sum_mem fun l _ => by rw [map_mul]; exact GlobalTheory.CompanionTheory.Ipf.Bdd.mul_mem_int (hA i l) (hB l j)
  have hone : ∀ i j, finPart D ((1 : Mx D V.rank V.rank) i j) ∈ intAE D := by
    intro i j
    rw [Matrix.one_apply]
    split_ifs
    · rw [map_one]; exact (by simpa using GlobalTheory.IwaPlace.SdComap.natCast_mem_intAE (D := D) 1)
    · rw [map_zero]; exact zero_mem _
  let U : Subgroup (GA D V) :=
    { carrier := {k | (∀ i j, finPart D (mt V k i j) ∈ intAE D) ∧ ∀ i j, finPart D (mt V k⁻¹ i j) ∈ intAE D}
      one_mem' := by
        refine ⟨fun i j => ?_, fun i j => ?_⟩
        · rw [show mt V 1 = 1 from rfl]; exact hone i j
        · rw [inv_one, show mt V 1 = 1 from rfl]; exact hone i j
      mul_mem' := by
        rintro k l ⟨hk, hk'⟩ ⟨hl, hl'⟩
        refine ⟨fun i j => ?_, fun i j => ?_⟩
        · rw [show mt V (k * l) = mt V k * mt V l from rfl]; exact hint _ _ hk hl i j
        · rw [mul_inv_rev, show mt V (l⁻¹ * k⁻¹) = mt V l⁻¹ * mt V k⁻¹ from rfl]; exact hint _ _ hl' hk' i j
      inv_mem' := by
        rintro k ⟨hk, hk'⟩
        exact ⟨hk', by simpa using hk⟩ }
  refine ⟨U, ?_, fun k hk => hk.1⟩
  have hmt : Continuous (mt V) := GlobalTheory.MixModel.continuous_mt V
  have hmti : Continuous fun k : GA D V => mt V k⁻¹ := hmt.comp continuous_inv
  have hopen : IsOpen {z : Af D.host.F ⊗[D.host.F] D.host.E | z ∈ intAE D} := by
    have h1 := GlobalTheory.CompanionTheory.Ipf.Bdd.isOpen_nsmul_mem (D := D) 1
    simp only [one_nsmul] at h1
    exact h1
  have e : (U : Set (GA D V)) = (⋂ i, ⋂ j, (fun k : GA D V => finPart D (mt V k i j)) ⁻¹' {z | z ∈ intAE D}) ∩
      ⋂ i, ⋂ j, (fun k : GA D V => finPart D (mt V k⁻¹ i j)) ⁻¹' {z | z ∈ intAE D} := by
    ext k; simp [U]
  rw [e]
  refine IsOpen.inter (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_)
    (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_)
  · exact hopen.preimage (hfc.comp ((continuous_apply j).comp ((continuous_apply i).comp hmt)))
  · exact hopen.preimage (hfc.comp ((continuous_apply j).comp ((continuous_apply i).comp hmti)))

end PositivityTheory.Rg.Rsw.L.LLatBound

end
end

section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

namespace PositivityTheory.Rg.Rsw.L.LLatBound

variable {D : D7}

theorem gen_all {θ : InfFam D} (hθ : IsInfFam θ) (V : HSp D) (n : ℕ)
    (f : SchwartzMap (D.what₂.Tau → Fin V.rank → Fin n → ℂ) ℂ)
    (g : (Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ)
    (hg : g ∈ GlobalTheory.WeilM.SB (Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E)) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ h : GA D V,
      ∑' x : {x : Matrix (Fin V.rank) (Fin n) D.host.E // x.rank = V.rank},
        ‖(fun X : Mx D V.rank n => f (fun τ i j => compAt θ τ X i j) * g (fun i j => finPart D (X i j)))
          (mm (mt V h⁻¹) (rat x.1))‖ₑ ≤ C := by
  obtain ⟨U, hUo, hU⟩ := exists_intOpen V
  obtain ⟨S, -, hS⟩ := GlobalTheory.Size.exists_finset_doubleCosets V U hUo
  choose C hC hb using fun x₀ : GA D V => gen_bound_col hθ V n x₀⁻¹ f g hg
  refine ⟨∑ x₀ ∈ S, C x₀, ENNReal.sum_lt_top.2 fun x _ => hC x, fun h => ?_⟩
  obtain ⟨γ, hγ, x₀, hx₀, a, ha, k, hk, hkf, rfl⟩ := hS h
  have e : (γ * x₀ * a * k)⁻¹ = (k⁻¹ * a⁻¹ * x₀⁻¹) * γ⁻¹ := by group
  have e2 : ∀ X : Mx D V.rank n, mm (mt V (γ * x₀ * a * k)⁻¹) X = mm (mt V (k⁻¹ * a⁻¹ * x₀⁻¹)) (mm (mt V γ⁻¹) X) := by
    intro X
    rw [e, mtL_mul]
    exact Matrix.mul_assoc _ _ _
  simp_rw [e2]
  rw [tsum_GQ V n γ⁻¹ (inv_mem hγ) (fun X => ‖f (fun τ i j => compAt θ τ (mm (mt V (k⁻¹ * a⁻¹ * x₀⁻¹)) X) i j) *
    g (fun i j => finPart D ((mm (mt V (k⁻¹ * a⁻¹ * x₀⁻¹)) X) i j))‖ₑ)]
  refine (hb x₀ a⁻¹ (inv_mem ha) k⁻¹ (inv_mem hkf) ?_).trans
    (Finset.single_le_sum (f := C) (fun _ _ => zero_le) hx₀)
  simpa using hU k hk

end PositivityTheory.Rg.Rsw.L.LLatBound

namespace PositivityTheory.Rg.Rsw.L

theorem latBound : LatBound := by
  intro D θ hθ V n M hM
  suffices h : ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ h : GA D V,
      ∑' x : {x : Matrix (Fin V.rank) (Fin n) D.host.E // x.rank = V.rank}, ‖M (mm (mt V h⁻¹) (rat x.1))‖ₑ ≤ C by
    obtain ⟨C, hC, h⟩ := h
    exact ⟨C.toNNReal, fun g => (h g).trans (by rw [ENNReal.coe_toNNReal hC.ne])⟩
  induction hM using Submodule.span_induction with
  | mem Φ hΦ =>
    obtain ⟨f, g, hg, rfl⟩ := hΦ
    exact LLatBound.gen_all hθ V n f g hg
  | zero => exact ⟨0, by simp, fun _ => by simp⟩
  | add f g _ _ hf hg =>
    obtain ⟨C₁, h₁, hf⟩ := hf
    obtain ⟨C₂, h₂, hg⟩ := hg
    refine ⟨C₁ + C₂, ENNReal.add_lt_top.2 ⟨h₁, h₂⟩, fun h => ?_⟩
    calc _ ≤ ∑' x : {x : Matrix (Fin V.rank) (Fin n) D.host.E // x.rank = V.rank},
          (‖f (mm (mt V h⁻¹) (rat x.1))‖ₑ + ‖g (mm (mt V h⁻¹) (rat x.1))‖ₑ) :=
          ENNReal.tsum_le_tsum fun x => enorm_add_le _ _
      _ = _ := ENNReal.tsum_add
      _ ≤ _ := add_le_add (hf h) (hg h)
  | smul c f _ hf =>
    obtain ⟨C₁, h₁, hf⟩ := hf
    refine ⟨‖c‖ₑ * C₁, ENNReal.mul_lt_top enorm_lt_top h₁, fun h => ?_⟩
    calc _ = ∑' x : {x : Matrix (Fin V.rank) (Fin n) D.host.E // x.rank = V.rank}, ‖c‖ₑ * ‖f (mm (mt V h⁻¹) (rat x.1))‖ₑ :=
          tsum_congr fun x => by simp [enorm_mul]
      _ = _ := ENNReal.tsum_mul_left
      _ ≤ _ := by gcongr; exact hf h

end PositivityTheory.Rg.Rsw.L

end
end
