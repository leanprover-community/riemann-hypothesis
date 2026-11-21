import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4GeometricSide.InnerEq
import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.UnitaryCurves.StarMulOfPlaces
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.ActEig
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.KerReg
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.InfinitesimalCharacterGL.HasInfCharGLIff
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.PActLoc
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsMulRightInvariantOfCenter

section
noncomputable section

open NumberField Matrix Finset GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.WigAlg PositivityTheory.RgBcC PositivityTheory.RgBcC.RealD PositivityTheory.RgBcC.Bridge PositivityTheory.Rg.BcB.Desc PositivityTheory.Rg.Cz PositivityTheory.Rg.Cz.GK
open scoped InnerProductSpace ComplexConjugate

namespace UpperTheory.V.Z.GSp4Splitting.CompactSubgroupTangentSkew

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

private def kW (w : InfinitePlace E) (k : Un n) : Kinf E n :=
  ⟨Matrix.of (atW w k.1), by
    classical
    refine (Matrix.mem_unitaryGroup_iff').2 ?_
    have h := star_mul_of_places (E := E) (a := n) (fun v => if v = w then k.1 else 1) (fun v => by
      split_ifs
      · exact (Matrix.mem_unitaryGroup_iff').1 k.2
      · simp)
    convert h using 3
    · ext i j v
      simp only [atW, Matrix.of_apply]
      split_ifs <;> rfl
    · ext i j v
      simp only [atW, Matrix.of_apply]
      split_ifs <;> rfl⟩

private theorem continuous_kW (w : InfinitePlace E) : Continuous (kW (n := n) w) := by
  classical
  refine Continuous.subtype_mk (continuous_matrix fun i j => continuous_pi fun v => ?_) _
  simp only [atW, Matrix.of_apply]
  split_ifs
  · exact (continuous_apply_apply i j).comp continuous_subtype_val
  · exact continuous_const

private theorem kW_one (w : InfinitePlace E) : kW (n := n) w 1 = 1 := by
  classical
  apply Subtype.ext
  ext i j v
  simp only [kW, atW, Matrix.of_apply]
  split_ifs <;> simp [Matrix.one_apply] <;> split_ifs <;> rfl

private theorem along_eq (w : InfinitePlace E) (k : Un n) (φ : GA E n → ℂ) (g : GA E n) :
    along w g φ k.1 = φ (g * infGL E n (Unitary.toUnits (kW w k))) :=
  chart_val φ g (Unitary.toUnits (kW w k))

private theorem exp_entry (X : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    HasDerivAt (fun t : ℝ => (NormedSpace.exp ((t : ℂ) • X) : Matrix (Fin n) (Fin n) ℂ) i j) (X i j) 0 := by
  letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
  let _ : NormedAlgebra ℝ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
  let _ : NormedAlgebra ℚ (Matrix (Fin n) (Fin n) ℂ) := NormedAlgebra.restrictScalars ℚ ℝ _
  have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) X (0 : ℝ)
  simp only [zero_smul, NormedSpace.exp_zero, one_mul] at h
  let L : Matrix (Fin n) (Fin n) ℂ →L[ℝ] ℂ :=
    LinearMap.toContinuousLinearMap
      { toFun := fun M => M i j, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have h2 := L.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h
  have e : (fun t : ℝ => (NormedSpace.exp ((t : ℂ) • X) : Matrix (Fin n) (Fin n) ℂ) i j) =
      (L ∘ fun t : ℝ => NormedSpace.exp (t • X)) := by
    funext t
    simp only [Function.comp, Complex.coe_smul]
    rfl
  rw [e]
  exact h2

private theorem skew_of_curve (X : Matrix (Fin n) (Fin n) ℂ) (γ : ℝ → Un n)
    (hγ : ∀ t : ℝ, (γ t).1 = NormedSpace.exp ((t : ℂ) • X)) : Xᴴ = -X := by
  ext i j
  have hc : ∀ a b, HasDerivAt (fun t : ℝ => (γ t).1 a b) (X a b) 0 := fun a b => by
    simpa only [hγ] using exp_entry X a b
  have h0 : (γ 0).1 = 1 := by rw [hγ]; simp
  have hs : HasDerivAt (fun t : ℝ => ∑ k, star ((γ t).1 k i) * (γ t).1 k j)
      (∑ k, (star (X k i) * (γ 0).1 k j + star ((γ 0).1 k i) * X k j)) 0 :=
    HasDerivAt.fun_sum fun k _ => (hc k i).star.mul (hc k j)
  have hconst : (fun t : ℝ => ∑ k, star ((γ t).1 k i) * (γ t).1 k j) = fun _ => (1 : Matrix (Fin n) (Fin n) ℂ) i j := by
    funext t
    have := congrFun (congrFun ((Matrix.mem_unitaryGroup_iff').1 (γ t).2) i) j
    simpa [Matrix.mul_apply, Matrix.star_apply] using this
  rw [hconst] at hs
  have h := hs.unique (hasDerivAt_const _ _)
  simp only [h0, Matrix.one_apply, mul_ite, mul_one, mul_zero, ite_mul, one_mul, zero_mul, Finset.sum_add_distrib,
    Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true] at h
  have e : ∑ x, star (if x = i then (1 : ℂ) else 0) * X x j = X i j := by
    simp only [apply_ite star, star_one, star_zero, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.sum_ite_eq,
      Finset.mem_univ, if_true]
  rw [e] at h
  show star (X j i) = -X i j
  exact eq_neg_of_add_eq_zero_left h

variable (π : CuspSub E n)

private theorem hd (c : ℝ → Kinf E n) (Z : Lie E n) (h0 : c 0 = 1) (hZ : HasDerivAt (fun t => toL (c t).1) Z 0)
    (y : π.V) (lam : π.V →ₗ[ℂ] ℂ) :
    HasDerivAt (fun t => lam (π.op (.cpt (c t)) y)) (lam (lieOp π Z y)) 0 := by
  let S := Submodule.span ℂ (Set.range fun γ => π.op (.cpt γ) y) ⊔ Submodule.span ℂ {lieOp π Z y}
  have := fin_orbit π y
  have : FiniteDimensional ℂ S := Submodule.finiteDimensional_sup _ _
  obtain ⟨s, cc, hc⟩ := exists_eval S lam
  rw [hc _ (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))]
  have e : (fun t => lam (π.op (.cpt (c t)) y)) =
      fun t => ∑ g ∈ s, cc g * y.1.1 (g * infGL E n (Unitary.toUnits (c t))) :=
    funext fun t => hc _ (Submodule.mem_sup_left (Submodule.subset_span ⟨c t, rfl⟩))
  rw [e]
  have h0' : Unitary.toUnits (c 0) = 1 := by rw [h0, map_one]
  exact HasDerivAt.fun_sum fun g _ =>
    (hasDerivAt_curve y.1 g (fun t => Unitary.toUnits (c t)) Z h0' hZ).const_mul (cc g)

private theorem lie_mem (T : Submodule ℂ π.V) (hT : ∀ γ, ∀ y ∈ T, π.op (.cpt γ) y ∈ T)
    (c : ℝ → Kinf E n) (Z : Lie E n) (h0 : c 0 = 1) (hZ : HasDerivAt (fun t => toL (c t).1) Z 0)
    {y : π.V} (hy : y ∈ T) : lieOp π Z y ∈ T := by
  by_contra hn
  obtain ⟨lam, h1, h2⟩ := Submodule.exists_le_ker_of_notMem hn
  have h := hd π c Z h0 hZ y lam
  have e : (fun t => lam (π.op (.cpt (c t)) y)) = fun _ => 0 :=
    funext fun t => h2 (hT _ _ hy)
  rw [e] at h
  exact h1 (h.unique (hasDerivAt_const _ _))

private def Kop (τ : E →+* ℂ) (a b : Fin n) : Module.End ℂ π.V :=
  cx τ (lieOp π) a b - cx (barE E τ) (lieOp π) b a

private theorem sum_skew {M : Type} [AddCommGroup M] [Module ℂ M] (X : Matrix (Fin n) (Fin n) ℂ) (hX : Xᴴ = -X)
    (A C : Fin n → Fin n → M) :
    ∑ i, ∑ j, (X i j • A i j + star (X i j) • C i j) = ∑ a, ∑ b, X a b • (A a b - C b a) := by
  have e : ∀ i j, star (X i j) = - X j i := fun i j => congrFun (congrFun hX j) i
  calc ∑ i, ∑ j, (X i j • A i j + star (X i j) • C i j)
      = ∑ i, ∑ j, (X i j • A i j - X j i • C i j) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
          rw [e, sub_eq_add_neg]; exact congrArg _ (neg_smul _ _)
    _ = ∑ i, ∑ j, X i j • A i j - ∑ i, ∑ j, X j i • C i j := by
        simp only [Finset.sum_sub_distrib]
    _ = ∑ i, ∑ j, X i j • A i j - ∑ i, ∑ j, X i j • C j i := by
        rw [Finset.sum_comm (f := fun i j => X j i • C i j)]
    _ = ∑ a, ∑ b, X a b • (A a b - C b a) := by
        simp only [smul_sub, Finset.sum_sub_distrib]

private theorem lieOp_skew (τ : E →+* ℂ) (X : Matrix (Fin n) (Fin n) ℂ) (hX : Xᴴ = -X) :
    lieOp π (fun i j => atEmb τ (X i j)) = ∑ a, ∑ b, X a b • Kop π τ a b := by
  rw [lieOp_atEmb]
  exact sum_skew X hX _ _

private theorem Kop_mem (τ : E →+* ℂ) (T : Submodule ℂ π.V)
    (hT : ∀ X : Matrix (Fin n) (Fin n) ℂ, Xᴴ = -X → ∀ y ∈ T, (∑ a, ∑ b, X a b • Kop π τ a b) y ∈ T)
    (a b : Fin n) {y : π.V} (hy : y ∈ T) : Kop π τ a b y ∈ T := by
  classical
  let A : Matrix (Fin n) (Fin n) ℂ := Matrix.single a b 1 - Matrix.single b a 1
  let B : Matrix (Fin n) (Fin n) ℂ := Complex.I • (Matrix.single a b 1 + Matrix.single b a 1)
  have hA : Aᴴ = -A := by
    simp [A, Matrix.conjTranspose_sub, Matrix.conjTranspose_single]
  have hB : Bᴴ = -B := by
    simp only [B]
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_single, Matrix.conjTranspose_single,
      star_one, Complex.star_def, Complex.conj_I, neg_smul, add_comm]
  have hs : ∀ c d, (∑ p, ∑ q, (Matrix.single c d (1 : ℂ)) p q • Kop π τ p q) = Kop π τ c d := by
    intro c d
    simp [Matrix.single_apply, Finset.sum_ite_eq, ite_and]
  have h1 : (∑ p, ∑ q, A p q • Kop π τ p q) = Kop π τ a b - Kop π τ b a := by
    rw [← hs a b, ← hs b a]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun q _ => ?_
    show (Matrix.single a b (1 : ℂ) p q - Matrix.single b a (1 : ℂ) p q) • Kop π τ p q = _
    exact sub_smul (Matrix.single a b (1 : ℂ) p q) (Matrix.single b a (1 : ℂ) p q) (Kop π τ p q)
  have h2 : (∑ p, ∑ q, B p q • Kop π τ p q) = Complex.I • (Kop π τ a b + Kop π τ b a) := by
    rw [← hs a b, ← hs b a]
    simp only [B, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul, mul_smul, add_smul, Finset.sum_add_distrib,
      Finset.smul_sum, smul_add]
  have h3 := hT A hA y hy
  have h4 := hT B hB y hy
  rw [h1] at h3
  rw [h2] at h4
  have e : Kop π τ a b y = (1 / 2 : ℂ) • ((Kop π τ a b - Kop π τ b a) y) +
      (-Complex.I / 2 : ℂ) • ((Complex.I • (Kop π τ a b + Kop π τ b a)) y) := by
    simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply, smul_add, smul_sub, smul_smul]
    have : -Complex.I / 2 * Complex.I = 1 / 2 := by
      rw [div_mul_eq_mul_div, neg_mul, Complex.I_mul_I]; norm_num
    rw [this]
    module
  rw [e]
  exact T.add_mem (T.smul_mem _ h3) (T.smul_mem _ h4)

private theorem hasDerivAt_of_dual {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
    (f : ℝ → F) (d : F) (h : ∀ l : F →ₗ[ℂ] ℂ, HasDerivAt (fun t => l (f t)) (l d) 0) : HasDerivAt f d 0 := by
  let b := Module.finBasis ℂ F
  let e : F ≃L[ℂ] (Fin (Module.finrank ℂ F) → ℂ) := b.equivFun.toContinuousLinearEquiv
  have h1 : HasDerivAt (fun t => e (f t)) (e d) 0 := by
    rw [hasDerivAt_pi]
    intro i
    exact h ((LinearMap.proj i : (Fin (Module.finrank ℂ F) → ℂ) →ₗ[ℂ] ℂ) ∘ₗ
      (e : F →ₗ[ℂ] (Fin (Module.finrank ℂ F) → ℂ)))
  have h2 := ((e.symm : _ →L[ℂ] F).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1
  simpa [Function.comp_def] using h2

section Data

variable {π} {K : Subgroup (GL (Fin n) (Af E))} [MeasurableSpace (GL (Fin n) (Af E))]
  {μf : MeasureTheory.Measure (GL (Fin n) (Af E))} (D : Rl π K μf) (w : InfinitePlace E)

private theorem i_σ (k : Un n) (u : D.U) : D.i (D.σ w k u) = π.op (.cpt (kW w k)) (D.i u) :=
  Subtype.ext (Subtype.ext (funext fun g => (D.hσ w k u g).trans (along_eq w k _ g)))

private theorem iso (k : Un n) (x y : D.U) : ⟪D.σ w k x, D.σ w k y⟫_ℂ = ⟪x, y⟫_ℂ := by
  rw [D.inner_eq, D.inner_eq]
  exact D.pet.2.2.2.1 (infGL E n (Unitary.toUnits (kW w k))) _ _ _ _ (fun g => by rw [i_σ]; rfl)
    (fun g => by rw [i_σ]; rfl)

private def orb (v : D.U) : Submodule ℂ π.V := Submodule.span ℂ (Set.range fun γ => π.op (.cpt γ) (D.i v))

private theorem orb_stable (v : D.U) (γ : Kinf E n) (y : π.V) (hy : y ∈ orb D v) : π.op (.cpt γ) y ∈ orb D v := by
  have hm : ∀ γ δ, π.op (.cpt (γ * δ)) = π.op (.cpt γ) * π.op (.cpt δ) := (gkData_holds E n π).mul
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨δ, rfl⟩ := hx
    exact Submodule.subset_span ⟨γ * δ, by simp only [hm]; rfl⟩
  | zero => simp
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ _ ha

private theorem fin_comap (v : D.U) : FiniteDimensional ℂ ((orb D v).comap D.i) := by
  haveI : FiniteDimensional ℂ (orb D v) := fin_orbit π (D.i v)
  let f : ((orb D v).comap D.i) →ₗ[ℂ] orb D v := (D.i.comp (Submodule.subtype _)).codRestrict _ fun x => x.2
  refine Module.Finite.of_injective f fun x y h => Subtype.ext (D.inj ?_)
  exact congrArg Subtype.val h

private theorem self_mem (v : D.U) : v ∈ (orb D v).comap D.i := by
  have h1 : π.op (.cpt (1 : Kinf E n)) = 1 := (gkData_holds E n π).one
  exact Submodule.subset_span ⟨1, by simp only [h1]; rfl⟩

private theorem σ_mem (v : D.U) (k : Un n) (u : D.U) (hu : u ∈ (orb D v).comap D.i) :
    D.σ w k u ∈ (orb D v).comap D.i := by
  show D.i (D.σ w k u) ∈ orb D v
  rw [i_σ]
  exact orb_stable D v _ _ hu

private theorem i_K (a b : Fin n) (u : D.U) :
    D.i (kF (D.E1 w) (D.E2 w) a b u) = Kop π w.embedding a b (D.i u) := by
  have key : ∀ (τ : E →+* ℂ) i j (ψ : π.V), ((cx τ (lieOp π) i j) ψ).1 = Eop τ i j ψ.1 := fun τ i j ψ => by
    rw [← GlobalTheory.WigCap.res_Eop]; rfl
  apply Subtype.ext
  show (D.i (D.E1 w a b u + D.E2 w a b u)).1 = (cx w.embedding (lieOp π) a b (D.i u)).1 -
    (cx (barE E w.embedding) (lieOp π) b a (D.i u)).1
  rw [map_add, Submodule.coe_add, D.hE1, D.hE2, key, key, sub_eq_add_neg]
  simp [eopW]

private theorem K_mem (v : D.U) (a b : Fin n) (u : D.U) (hu : u ∈ (orb D v).comap D.i) :
    kF (D.E1 w) (D.E2 w) a b u ∈ (orb D v).comap D.i := by
  show D.i _ ∈ orb D v
  rw [i_K]
  refine Kop_mem π _ _ (fun X hX y hy => ?_) a b hu
  obtain ⟨c, h0, -, -, hZ⟩ := exists_curve w.embedding X hX
  rw [← lieOp_skew π _ X hX]
  exact lie_mem π _ (orb_stable D v) c _ h0 hZ hy

private theorem curve_deriv (X : Matrix (Fin n) (Fin n) ℂ) (γ : ℝ → Un n)
    (hγ : ∀ t : ℝ, (γ t).1 = NormedSpace.exp ((t : ℂ) • X)) :
    HasDerivAt (fun t => toL (kW w (γ t)).1) (fun i j => atEmb w.embedding (X i j)) 0 := by
  classical
  rw [hasDerivAt_pi]; intro i
  rw [hasDerivAt_pi]; intro j
  rw [hasDerivAt_pi]; intro v
  show HasDerivAt (fun t => atW w (γ t).1 i j v) (atEmb w.embedding (X i j) v) 0
  rw [atEmb_apply]
  by_cases hv : v = w
  · subst hv
    simp only [atW, InfinitePlace.mk_embedding, if_true]
    simpa only [hγ] using exp_entry X i j
  · simp only [atW, InfinitePlace.mk_embedding, if_neg hv]
    exact hasDerivAt_const _ _

private theorem deriv_σ (v : D.U) (X : Matrix (Fin n) (Fin n) ℂ) (γ : ℝ → Un n)
    (hγ : ∀ t : ℝ, (γ t).1 = NormedSpace.exp ((t : ℂ) • X)) (u : D.U) (hu : u ∈ (orb D v).comap D.i) :
    HasDerivAt (fun t : ℝ => D.σ w (γ t) u) (∑ a, ∑ b, X a b • kF (D.E1 w) (D.E2 w) a b u) 0 := by
  haveI := fin_comap D v
  have hX := skew_of_curve X γ hγ
  have hZ := curve_deriv w X γ hγ
  have h0 : kW w (γ 0) = 1 := by
    have : γ 0 = 1 := Subtype.ext (by rw [hγ]; simp)
    rw [this, kW_one]
  set Z : Lie E n := fun i j => atEmb w.embedding (X i j) with hZd
  set d : D.U := ∑ a, ∑ b, X a b • kF (D.E1 w) (D.E2 w) a b u with hd'
  have hdi : D.i d = lieOp π Z (D.i u) := by
    rw [hZd, lieOp_skew π _ X hX, hd']
    simp only [map_sum, map_smul, i_K, LinearMap.sum_apply, LinearMap.smul_apply]
  have hdS : d ∈ (orb D v).comap D.i := by
    show D.i d ∈ orb D v
    rw [hdi]
    exact lie_mem π _ (orb_stable D v) (fun t => kW w (γ t)) Z h0 hZ hu
  let S := (orb D v).comap D.i
  let f : ℝ → S := fun t => ⟨D.σ w (γ t) u, σ_mem D w v _ u hu⟩
  have hf : HasDerivAt f (⟨d, hdS⟩ : S) 0 := by
    refine hasDerivAt_of_dual f _ fun l => ?_
    let j : S →ₗ[ℂ] π.V := D.i.comp S.subtype
    have hj : LinearMap.ker j = ⊥ :=
      LinearMap.ker_eq_bot.2 fun x y h => Subtype.ext (D.inj h)
    obtain ⟨g, hg⟩ := j.exists_leftInverse_of_injective hj
    have hl : ∀ s : S, l s = (l ∘ₗ g) (j s) := fun s => by
      show l s = l ((g ∘ₗ j) s)
      rw [hg]; rfl
    have h := hd π (fun t => kW w (γ t)) Z h0 hZ (D.i u) (l ∘ₗ g)
    have e1 : (fun t => l (f t)) = fun t => (l ∘ₗ g) (π.op (.cpt (kW w (γ t))) (D.i u)) := by
      funext t
      rw [hl, ← i_σ]
      rfl
    have e2 : l (⟨d, hdS⟩ : S) = (l ∘ₗ g) (lieOp π Z (D.i u)) := by
      rw [hl, ← hdi]
      rfl
    rw [e1, e2]
    exact h
  exact (S.subtypeL.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hf

private theorem cont_σ (v x : D.U) : Continuous fun k : Un n => ⟪x, D.σ w k v⟫_ℂ := by
  have e : (fun k : Un n => ⟪x, D.σ w k v⟫_ℂ) = fun k => D.H (D.i x) (π.op (.cpt (kW w k)) (D.i v)) := by
    funext k
    rw [D.inner_eq, i_σ]
  rw [e]
  exact ((gkData_holds E n π).cont (D.i v) (D.H (D.i x))).comp (continuous_kW w)

end Data

end UpperTheory.V.Z.GSp4Splitting.CompactSubgroupTangentSkew

open UpperTheory.V.Z.GSp4Splitting UpperTheory.V.Z.GSp4Splitting.CompactSubgroupTangentSkew in
theorem UpperTheory.V.Z.GSp4Splitting.rlK :
    RlK := by
  intro E _ _ _ n _ π _ K _ _ _ _ _ μf _ D w
  refine ⟨⟨iso D w, fun v => ⟨_, fin_comap D v, self_mem D v, fun k x hx => σ_mem D w v k x hx⟩, fun v x => cont_σ D w v x⟩,
    iso D w, fun v => ⟨_, fin_comap D v, self_mem D v, fun k x hx => σ_mem D w v k x hx,
      fun a b x hx => K_mem D w v a b x hx, fun X γ hγ x hx => deriv_σ D w v X γ hγ x hx⟩⟩
end
end

section
open UpperTheory.V.Z.GSp4Splitting PositivityTheory.RgBcC PositivityTheory.RgBcC.RealD PositivityTheory.Rg.BcB.Desc

noncomputable section

namespace UpperTheory.V.Z.GSp4Splitting

open MeasureTheory Matrix Finset NumberField
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC.Bridge (along)
open scoped InnerProductSpace ContDiff

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

private theorem val_mem (y : G n) : y.val ∈ GLs n := ((UpperTheory.RealTr.basic n).2.1 y.val).2 y.isUnit

private theorem mul_mem {x y : Mat n} (hx : x ∈ GLs n) (hy : y ∈ GLs n) : x * y ∈ GLs n := by
  show (x * y).det ≠ 0
  rw [Matrix.det_mul]
  exact mul_ne_zero hx hy

private def trR (M : KMod n) (T : M.V →L[ℂ] M.V) : (M.V →L[ℂ] M.V) →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap
    (((LinearMap.trace ℂ M.V).comp (ContinuousLinearMap.coeLM ℂ)).comp (LinearMap.mulRight ℂ T))

private theorem trR_apply (M : KMod n) (T X : M.V →L[ℂ] M.V) :
    trR M T X = LinearMap.trace ℂ M.V ((X * T : M.V →L[ℂ] M.V) : M.V →ₗ[ℂ] M.V) := rfl

section Abs

variable [MeasurableSpace (Un n)] [BorelSpace (Un n)] (ν : Measure (Un n)) [ν.IsHaarMeasure] (M : KMod n)
  {ι : Type} [Fintype ι] {c : ι → Un n → ℂ} {F : ι → Mat n → ℂ} {F0 : Mat n → ℂ}

private theorem integrable_c (hc : ∀ j, Continuous (c j)) (j : ι) : Integrable (fun κ => c j κ • M.ρ κ) ν := by
  haveI : CompactSpace (Un n) := GlobalTheory.compactSpace_unitaryGroup (Fin n) ℂ
  exact ((hc j).smul M.cont).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

private theorem sec_eq (hc : ∀ j, Continuous (c j))
    (hF : ∀ y ∈ GLs n, ∀ κ : Un n, F0 (y * κ.1) = ∑ j, c j κ * F j y) {y : Mat n} (hy : y ∈ GLs n) :
    ∑ j, F j y • ∫ κ, c j κ • M.ρ κ ∂ν = ∫ κ, F0 (y * κ.1) • M.ρ κ ∂ν := by
  have h1 : ∀ κ : Un n, F0 (y * κ.1) • M.ρ κ = ∑ j, F j y • (c j κ • M.ρ κ) := by
    intro κ
    rw [hF y hy κ, Finset.sum_smul]
    exact Finset.sum_congr rfl fun j _ => by rw [smul_smul, mul_comm]
  simp only [h1]
  rw [integral_finset_sum (f := fun j κ => F j y • (c j κ • M.ρ κ)) _ fun j _ => (integrable_c ν M hc j).smul (F j y)]
  simp only [integral_smul]

private theorem sec_equiv (hc : ∀ j, Continuous (c j))
    (hF : ∀ y ∈ GLs n, ∀ κ : Un n, F0 (y * κ.1) = ∑ j, c j κ * F j y) {y : Mat n} (hy : y ∈ GLs n) (a : Un n) :
    ∑ j, F j (y * a.1) • ∫ κ, c j κ • M.ρ κ ∂ν = M.ρ a⁻¹ * ∑ j, F j y • ∫ κ, c j κ • M.ρ κ ∂ν := by
  haveI := FiniteDimensional.complete ℂ M.V
  have ha : a.1 ∈ GLs n := val_mem (Unitary.toUnits a)
  rw [sec_eq ν M hc hF (mul_mem hy ha), sec_eq ν M hc hF hy]
  have hint : Integrable (fun κ : Un n => F0 (y * κ.1) • M.ρ κ) ν := by
    have h1 : (fun κ : Un n => F0 (y * κ.1) • M.ρ κ) = fun κ => ∑ j, F j y • (c j κ • M.ρ κ) := by
      funext κ
      rw [hF y hy κ, Finset.sum_smul]
      exact Finset.sum_congr rfl fun j _ => by rw [smul_smul, mul_comm]
    rw [h1]
    exact integrable_finset_sum _ fun j _ => (integrable_c ν M hc j).smul (F j y)
  have h2 := (ContinuousLinearMap.mul ℂ (M.V →L[ℂ] M.V) (M.ρ a⁻¹)).integral_comp_comm hint
  simp only [ContinuousLinearMap.mul_apply'] at h2
  rw [← h2, ← integral_mul_left_eq_self (fun κ : Un n => M.ρ a⁻¹ * (F0 (y * κ.1) • M.ρ κ)) a]
  refine integral_congr_ae (Filter.Eventually.of_forall fun κ => ?_)
  simp only [mul_smul_comm, ← map_mul, inv_mul_cancel_left, Submonoid.coe_mul, mul_assoc]

variable [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure]
  {k : Mat n → (M.V →L[ℂ] M.V)} {val : Inf n → ℂ} {T' : ℝ}

omit [MeasurableSpace (Un n)] [BorelSpace (Un n)] in
private theorem integrable_k (hk : IsMult μ M k val T') {f : Mat n → ℂ} (hf : ContinuousOn f (GLs n)) :
    Integrable (fun y : G n => f y.val • k y.val) μ := by
  obtain ⟨h1, h2, -⟩ := UpperTheory.RealTr.kerReg n μ M k val T' hk
  have h3 : Continuous fun y : G n => f y.val := hf.comp_continuous Units.continuous_val val_mem
  exact (h3.smul h1).integrable_of_hasCompactSupport (h2.mono fun y hy h0 => hy (by simp [h0]))

private theorem ker_avg (hν : ν Set.univ = 1) (hk : IsMult μ M k val T') (hc : ∀ j, Continuous (c j))
    (hs : ∀ j, ContinuousOn (F j) (GLs n))
    (hF : ∀ y ∈ GLs n, ∀ κ : Un n, F0 (y * κ.1) = ∑ j, c j κ * F j y) :
    ∫ y : G n, F0 y.val • k y.val ∂μ = ∑ j, (∫ y : G n, F j y.val • k y.val ∂μ) * ∫ κ, c j κ • M.ρ κ ∂ν := by
  haveI := FiniteDimensional.complete ℂ M.V
  haveI := GlobalTheory.CompanionTheory.QuotVan.isMulRightInvariant_GL n μ
  have he := (UpperTheory.RealTr.kerReg n μ M k val T' hk).2.2
  have h1 : ∀ κ : Un n, ∫ y : G n, F0 y.val • k y.val ∂μ =
      ∑ j, (∫ y : G n, F j y.val • k y.val ∂μ) * (c j κ • M.ρ κ) := by
    intro κ
    rw [← integral_mul_right_eq_self (fun y : G n => F0 y.val • k y.val) (Unitary.toUnits κ)]
    have h2 : ∀ y : G n, F0 (y * Unitary.toUnits κ : G n).val • k (y * Unitary.toUnits κ : G n).val =
        ∑ j, (F j y.val • k y.val) * (c j κ • M.ρ κ) := by
      intro y
      have h3 := he y.val (val_mem y) 1 κ
      simp only [OneMemClass.coe_one, one_mul, map_one] at h3
      show F0 (y.val * κ.1) • k (y.val * κ.1) = _
      rw [hF _ (val_mem y) κ, h3, Finset.sum_smul]
      exact Finset.sum_congr rfl fun j _ => by rw [smul_mul_smul_comm, mul_comm (c j κ)]
    simp only [h2]
    have h4 := fun j => ((ContinuousLinearMap.mul ℂ (M.V →L[ℂ] M.V)).flip (c j κ • M.ρ κ)).integral_comp_comm
      (integrable_k M μ hk (hs j))
    simp only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.mul_apply'] at h4
    rw [integral_finset_sum _ fun j _ => (integrable_k M μ hk (hs j)).mul_const _]
    exact Finset.sum_congr rfl fun j _ => h4 j
  have h5 : ∫ y : G n, F0 y.val • k y.val ∂μ = ∫ _κ : Un n, (∫ y : G n, F0 y.val • k y.val ∂μ) ∂ν := by
    simp [Measure.real, hν]
  rw [h5, integral_congr_ae (Filter.Eventually.of_forall h1),
    integral_finset_sum _ fun j _ => (integrable_c ν M hc j).const_mul _]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h6 := (ContinuousLinearMap.mul ℂ (M.V →L[ℂ] M.V) (∫ y : G n, F j y.val • k y.val ∂μ)).integral_comp_comm
    (integrable_c ν M hc j)
  simpa only [ContinuousLinearMap.mul_apply'] using h6

private theorem ker_val (hk : IsMult μ M k val T') (hc : ∀ j, Continuous (c j)) (χ : Inf n)
    (hs : ∀ j, ContDiffOn ℝ ∞ (F j) (GLs n)) (he : ∀ j, IsEig χ (F j))
    (hF : ∀ y ∈ GLs n, ∀ κ : Un n, F0 (y * κ.1) = ∑ j, c j κ * F j y) :
    ∑ j, (∫ y : G n, F j y.val • k y.val ∂μ) * ∫ κ, c j κ • M.ρ κ ∂ν =
      val χ • ∑ j, F j 1 • ∫ κ, c j κ • M.ρ κ ∂ν := by
  haveI := FiniteDimensional.complete ℂ M.V
  ext e
  set B : ι → (M.V →L[ℂ] M.V) := fun j => ∫ κ, c j κ • M.ρ κ ∂ν with hB
  have hCE : (fun x => ∑ j, F j x • B j e) ∈ CE M := by
    refine ⟨ContDiffOn.sum fun j _ => (hs j).smul contDiffOn_const, fun y hy a => ?_⟩
    have h := congrArg (fun X : M.V →L[ℂ] M.V => X e) (sec_equiv ν M hc hF hy a)
    simpa only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.mul_apply] using h
  have h := UpperTheory.RealTr.actEig n μ M k val T' hk χ _ hCE
    (PositivityTheory.Rg.BcB.CG.isEig_sum χ F (fun j => B j e) hs he) 1 (val_mem 1)
  have hI := fun j => integrable_k M μ hk (hs j).continuousOn
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.mul_apply]
  rw [← h]
  simp only [act, one_mul, map_sum, map_smul]
  rw [integral_finset_sum (f := fun j (y : PositivityTheory.RgTw.G n) => F j y.val • k y.val (B j e)) _
    fun j _ => (hI j).apply_continuousLinearMap (B j e)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [ContinuousLinearMap.integral_apply (hI j)]
  rfl

private theorem abs_act (hν : ν Set.univ = 1) (hk : IsMult μ M k val T') (T : M.V →L[ℂ] M.V)
    (hc : ∀ j, Continuous (c j)) (χ : Inf n) (h0 : ContinuousOn F0 (GLs n))
    (hs : ∀ j, ContDiffOn ℝ ∞ (F j) (GLs n)) (he : ∀ j, IsEig χ (F j))
    (hF : ∀ y ∈ GLs n, ∀ κ : Un n, F0 (y * κ.1) = ∑ j, c j κ * F j y) :
    ∫ y : G n, phiOf M T k y * F0 y.val ∂μ = val χ * ∑ j,
      (∫ κ, LinearMap.trace ℂ M.V ((M.ρ κ * T : M.V →L[ℂ] M.V) : M.V →ₗ[ℂ] M.V) * c j κ ∂ν) * F j 1 := by
  haveI := FiniteDimensional.complete ℂ M.V
  have h1 := (trR M T).integral_comp_comm (integrable_k M μ hk h0)
  rw [ker_avg ν M μ hν hk hc (fun j => (hs j).continuousOn) hF, ker_val ν M μ hk hc χ hs he hF] at h1
  have h2 : ∀ y : G n, phiOf M T k y * F0 y.val = trR M T (F0 y.val • k y.val) := by
    intro y
    rw [map_smul, smul_eq_mul, mul_comm]
    rfl
  simp only [h2]
  rw [h1, map_smul, map_sum, smul_eq_mul]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, smul_eq_mul, mul_comm, ← (trR M T).integral_comp_comm (integrable_c ν M hc j)]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun κ => ?_)
  simp only [map_smul, smul_eq_mul, trR_apply, mul_comm]

end Abs

private theorem along_right {E : Type} [Field E] [NumberField E] [IsCMField E] (w : InfinitePlace E)
    (g : GlobalTheory.CuspRep.GA E n) (φ ψ : GlobalTheory.CuspRep.GA E n → ℂ) (κ : Un n) (h : ∀ x, ψ x = along w x φ κ.1) {y : Mat n}
    (hy : y ∈ GLs n) : along w g φ (y * κ.1) = along w g ψ y := by
  classical
  obtain ⟨t, rfl⟩ := ((UpperTheory.RealTr.basic n).2.1 y).1 hy
  have e1 : t.val * κ.1 = (t * Unitary.toUnits κ : G n).val := rfl
  have e2 : κ.1 = (Unitary.toUnits κ : G n).val := rfl
  rw [e1, PositivityTheory.Rg.BcB.CG.along_val, PositivityTheory.Rg.BcB.CG.along_val, h, e2, PositivityTheory.Rg.BcB.CG.along_val, Pi.mulSingle_mul,
    PositivityTheory.Rg.BcB.CG.infinitePart_mul, mul_assoc]

end UpperTheory.V.Z.GSp4Splitting

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open MeasureTheory PositivityTheory.RgBcC.Bridge in
open scoped InnerProductSpace in
theorem UpperTheory.V.Z.GSp4Splitting.locAct :
    LocAct := by
  intro E _ _ _ n hn π hθ K hKo hKc hKθ _ _ μf _ D w lam hch _ _ ν _ hν _ _ μC _ M T P hP k val T' hk u g
  have hK := (rlK E n hn π hθ K hKo hKc hKθ μf D w).1
  obtain ⟨S, hfd, hu, hS⟩ := hK.fin u
  let b := stdOrthonormalBasis ℂ S
  have hexp : ∀ x ∈ S, x = ∑ j, ⟪((b j : S) : D.U), x⟫_ℂ • ((b j : S) : D.U) := by
    intro x hx
    have h := congrArg Subtype.val (b.sum_repr' (⟨x, hx⟩ : S))
    simpa [Submodule.coe_sum, Submodule.coe_inner] using h.symm
  have hPu : P u ∈ S := by
    rw [← S.orthogonal_orthogonal, Submodule.mem_orthogonal]
    intro v hv
    rw [hP u v]
    have h0 : ∀ κ, ⟪v, D.σ w κ u⟫_ℂ = 0 := fun κ => (Submodule.mem_orthogonal' _ _).1 hv _ (hS κ u hu)
    simp [h0]
  have hev : ∀ x ∈ S, (D.i x).1.1 = ∑ j, ⟪((b j : S) : D.U), x⟫_ℂ • (D.i (b j : S)).1.1 := by
    intro x hx
    conv_lhs => rw [hexp x hx]
    simp only [map_sum, map_smul, Submodule.coe_sum, Submodule.coe_smul]
  have heig := (bridge E n π.V w (infOf lam)).2 hch
  have h := abs_act ν M μC (c := fun j κ => ⟪((b j : S) : D.U), D.σ w κ u⟫_ℂ)
    (F := fun j => along w g (D.i (b j : S)).1.1) (F0 := along w g (D.i u).1.1) hν hk T (fun j => hK.cont _ _) (infOf lam)
    (PositivityTheory.Rg.BcB.CG.contDiffOn_along w g (D.i u).1.2).continuousOn
    (fun j => PositivityTheory.Rg.BcB.CG.contDiffOn_along w g (D.i _).1.2) (fun j => heig _ (D.i _).2 g)
    (fun y hy κ => by
      rw [along_right w g _ _ κ (D.hσ w κ u) hy, hev _ (hS κ u hu), along_sum, Finset.sum_apply]
      simp only [along_smul, Pi.smul_apply, smul_eq_mul])
  rw [h, hev _ hPu, Finset.sum_apply]
  simp only [along_one, Pi.smul_apply, smul_eq_mul, hP u]
end
end
