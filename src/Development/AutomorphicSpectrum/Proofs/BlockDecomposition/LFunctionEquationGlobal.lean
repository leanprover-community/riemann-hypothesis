import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.RationalPrimesBelowPlaces
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GlobalRankinSelbergBasicFacts
import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocalWhittakerDuality.LocalFunctionalEquationFinite

section
noncomputable section
open MeasureTheory GroundTheory.LocalField GroundTheory.Automorphic Ad3
open scoped ValuativeRel Topology NNReal

namespace GlobalTheory.CompanionTheory.GamEquiv

variable {F F' : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [Field F'] [ValuativeRel F'] [TopologicalSpace F'] [IsNonarchimedeanLocalField F']

theorem ord_pow_nat {x : F} (hx : x ≠ 0) (n : ℕ) : ord (x ^ n) = n * ord x := by
  induction n with
  | zero => simp [ord_one]
  | succ k ih => rw [pow_succ, ord_mul (pow_ne_zero _ hx) hx, ih]; push_cast; ring

theorem ord_zpow' {x : F} (hx : x ≠ 0) (k : ℤ) : ord (x ^ k) = k * ord x := by
  have := ord_units_zpow (Units.mk0 x hx) k
  simpa [Units.val_zpow_eq_zpow_val] using this

theorem ord_pos_iff_tendsto {x : F} (hx : x ≠ 0) :
    0 < ord x ↔ Filter.Tendsto (fun n : ℕ => x ^ n) Filter.atTop (𝓝 0) := by
  constructor
  · intro h
    rw [(hasBasis_nhds_zero_valBall (K := F)).tendsto_right_iff]
    intro i _
    filter_upwards [Filter.eventually_ge_atTop i.toNat] with n hn
    rw [SetLike.mem_coe, mem_valBall_iff_le_ord (pow_ne_zero _ hx), ord_pow_nat hx]
    have : (i.toNat : ℤ) ≤ n := by exact_mod_cast hn
    have h2 : i ≤ n := by omega
    nlinarith
  · intro h
    by_contra hc
    have hm := h (valBall_mem_nhds (K := F) 1)
    obtain ⟨n, hn⟩ := (Filter.eventually_atTop.mp (Filter.mem_map.mp hm))
    have := hn (n + 1) (by omega)
    simp only [Set.mem_preimage, SetLike.mem_coe] at this
    rw [mem_valBall_iff_le_ord (pow_ne_zero _ hx), ord_pow_nat hx] at this
    push_cast at this
    nlinarith

section Tr

variable (φ : F ≃+* F') (h1 : Continuous φ) (h2 : Continuous φ.symm)
include h1 h2

theorem ord_pos_iff {x : F} (hx : x ≠ 0) : 0 < ord (φ x) ↔ 0 < ord x := by
  have hx' : φ x ≠ 0 := by simpa using hx
  rw [ord_pos_iff_tendsto hx, ord_pos_iff_tendsto hx']
  constructor
  · intro h
    simpa [Function.comp_def, map_pow] using ((h2.tendsto' _ _ (by simp)).comp h)
  · intro h
    simpa [Function.comp_def, map_pow] using ((h1.tendsto' _ _ (by simp)).comp h)

theorem ord_eq_zero_iff {x : F} (hx : x ≠ 0) : ord (φ x) = 0 ↔ ord x = 0 := by
  have hx' : φ x ≠ 0 := by simpa using hx
  have a := ord_pos_iff φ h1 h2 hx
  have b := ord_pos_iff φ h1 h2 (inv_ne_zero hx)
  rw [map_inv₀, ord_inv hx, ord_inv hx'] at b
  omega

theorem ord_map {x : F} (hx : x ≠ 0) : ord (φ x) = ord x := by
  obtain ⟨π, hπ0, hπ⟩ := exists_ord_eq F 1
  obtain ⟨π', hπ0', hπ'⟩ := exists_ord_eq F' 1
  set ρ := φ.symm π' with hρ
  have hρ0 : ρ ≠ 0 := by simpa [hρ] using hπ0'
  have hφρ : φ ρ = π' := by simp [hρ]
  have hφπ0 : φ π ≠ 0 := by simpa using hπ0
  have hm : 0 < ord (φ π) := (ord_pos_iff φ h1 h2 hπ0).mpr (by omega)
  have hn : 0 < ord ρ := (ord_pos_iff φ h1 h2 hρ0).mp (by rw [hφρ]; omega)
  set m := ord (φ π) with hmdef
  have hz : ord (π * ρ ^ (-m)) = 0 := by
    refine (ord_eq_zero_iff φ h1 h2 (mul_ne_zero hπ0 (zpow_ne_zero _ hρ0))).mp ?_
    rw [map_mul, map_zpow₀, hφρ, ord_mul hφπ0 (zpow_ne_zero _ hπ0'), ord_zpow' hπ0', hπ', ← hmdef]
    ring
  rw [ord_mul hπ0 (zpow_ne_zero _ hρ0), ord_zpow' hρ0, hπ] at hz
  have hm1 : m = 1 := by
    have hmn : m * ord ρ = 1 := by linarith
    nlinarith
  have hw : ord (x * π ^ (-ord x)) = 0 := by
    rw [ord_mul hx (zpow_ne_zero _ hπ0), ord_zpow' hπ0, hπ]
    ring
  have hw' := (ord_eq_zero_iff φ h1 h2 (mul_ne_zero hx (zpow_ne_zero _ hπ0))).mpr hw
  have hx' : φ x ≠ 0 := by simpa using hx
  rw [map_mul, map_zpow₀, ord_mul hx' (zpow_ne_zero _ hφπ0), ord_zpow' hφπ0, ← hmdef, hm1] at hw'
  linarith

theorem map_mem_valBall_iff (n : ℤ) {x : F} : φ x ∈ valBall F' n ↔ x ∈ valBall F n := by
  by_cases hx : x = 0
  · simp [hx, zero_mem]
  have hx' : φ x ≠ 0 := by simpa using hx
  rw [mem_valBall_iff_le_ord hx, mem_valBall_iff_le_ord hx', ord_map φ h1 h2 hx]

theorem preimage_valBall (n : ℤ) : φ ⁻¹' (valBall F' n : Set F') = valBall F n := by
  ext x
  exact map_mem_valBall_iff φ h1 h2 n

section Meas

variable [MeasurableSpace F] [BorelSpace F] [MeasurableSpace F'] [BorelSpace F']

theorem map_haarIntegers : Measure.map φ (haarIntegers F) = haarIntegers F' := by
  let e : F ≃ₜ+ F' := { φ.toAddEquiv with continuous_toFun := h1, continuous_invFun := h2 }
  have : (Measure.map e (haarIntegers F)).IsAddHaarMeasure := e.isAddHaarMeasure_map _
  have h : (Measure.map φ (haarIntegers F)).IsAddHaarMeasure := this
  have h3 := eq_smul_haarIntegers (Measure.map φ (haarIntegers F))
  rw [← coe_valBall_zero, Measure.map_apply h1.measurable (measurableSet_valBall 0),
    preimage_valBall φ h1 h2, coe_valBall_zero, haarIntegers_integers, one_smul] at h3
  exact h3

theorem residueCard_eq : residueCard F = residueCard F' := by
  have h : Measure.map φ (haarIntegers F) (valBall F' 1 : Set F') = haarIntegers F' (valBall F' 1 : Set F') := by
    rw [map_haarIntegers φ h1 h2]
  rw [Measure.map_apply h1.measurable (measurableSet_valBall 1), preimage_valBall φ h1 h2,
    haarIntegers_valBall, haarIntegers_valBall] at h
  have h' : ((residueCard F : ℝ≥0) ^ (-1 : ℤ)) = ((residueCard F' : ℝ≥0) ^ (-1 : ℤ)) := by
    exact_mod_cast h
  rw [zpow_neg_one, zpow_neg_one, inv_inj] at h'
  exact_mod_cast h'


omit [MeasurableSpace F] [BorelSpace F] [MeasurableSpace F'] [BorelSpace F'] in
theorem addCharConductor_comp (ψ : AddChar F' Circle) :
    addCharConductor (ψ.compAddMonoidHom (φ : F →+ F')) = addCharConductor ψ := by
  unfold addCharConductor
  congr 1
  ext n
  constructor
  · intro h y hy
    have := h (φ.symm y) ((map_mem_valBall_iff φ h1 h2 n).mp (by simpa using hy))
    simpa using this
  · intro h x hx
    exact h (φ x) ((map_mem_valBall_iff φ h1 h2 n).mpr hx)


end Meas

section Char

abbrev um : Fˣ →* F'ˣ := Units.map (φ : F →* F')

omit h1 h2 in
theorem um_surjective (v : F'ˣ) : ∃ u : Fˣ, um φ u = v :=
  ⟨Units.map (φ.symm : F' →* F) v, by ext; simp⟩






variable [MeasurableSpace F] [BorelSpace F] [MeasurableSpace F'] [BorelSpace F']


omit h1 h2 [MeasurableSpace F] [BorelSpace F] [MeasurableSpace F'] [BorelSpace F'] in
theorem quasiCharExt_comp (μ : F'ˣ →* ℂˣ) (x : F) :
    quasiCharExt (μ.comp (um φ))⁻¹ x = quasiCharExt μ⁻¹ (φ x) := by
  by_cases hx : x = 0
  · simp [quasiCharExt, hx]
  have e : φ x = ((um φ (Units.mk0 x hx) : F'ˣ) : F') := rfl
  rw [e, quasiCharExt_units]
  conv_lhs => rw [show x = ((Units.mk0 x hx : Fˣ) : F) from rfl, quasiCharExt_units]
  rfl


end Char

end Tr


end GlobalTheory.CompanionTheory.GamEquiv
end
end

section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.BaseChangeFunctionalEquation

section Trace

variable {K : Type} [Field K] [NumberField K]

abbrev aQ (p : Pl) (q : ℚ) : p.adicCompletion ℚ :=
  @algebraMap ℚ (p.adicCompletion ℚ) _ _ (HeightOneSpectrum.instAlgebraAdicCompletion (𝓞 ℚ) ℚ p) q

end Trace

section Deg

variable {K : Type} [Field K] [NumberField K]

theorem finrank_pos' (v : Pl) (w : PlK K) [w.asIdeal.LiesOver v.asIdeal] :
    0 < Module.finrank (Qv v) (Kv K w) := by
  have : Module.Finite (Qv v) (Kv K w) := inferInstance
  exact Module.finrank_pos

theorem sum_finrank' (h2 : Module.finrank ℚ K = 2) (v : Pl) :
    ∑ u : SemiLocal.PlacesOver K v, Module.finrank (Qv v) (Kv K u.1) = 2 :=
  (SemiLocal.sum_finrank_eq K v).trans h2

theorem places_split (h2 : Module.finrank ℚ K = 2) (v : Pl) (w₁ w₂ : PlK K)
    [i₁ : w₁.asIdeal.LiesOver v.asIdeal] [i₂ : w₂.asIdeal.LiesOver v.asIdeal] (hne : w₁ ≠ w₂) :
    (∀ w : PlK K, w.asIdeal.LiesOver v.asIdeal → w = w₁ ∨ w = w₂) ∧
      Module.finrank (Qv v) (Kv K w₁) = 1 ∧ Module.finrank (Qv v) (Kv K w₂) = 1 := by
  classical
  have hs := sum_finrank' h2 v
  set a : SemiLocal.PlacesOver K v := ⟨w₁, i₁⟩
  set b : SemiLocal.PlacesOver K v := ⟨w₂, i₂⟩
  have hab : a ≠ b := fun h => hne (congrArg Subtype.val h)
  have p₁ := finrank_pos' v w₁
  have p₂ := finrank_pos' v w₂
  have h3 : Module.finrank (Qv v) (Kv K w₁) + Module.finrank (Qv v) (Kv K w₂) ≤ 2 := by
    have := Finset.sum_le_sum_of_subset (f := fun u : SemiLocal.PlacesOver K v => Module.finrank (Qv v) (Kv K u.1))
      (Finset.subset_univ ({a, b} : Finset (SemiLocal.PlacesOver K v)))
    rw [Finset.sum_pair hab, hs] at this
    exact this
  refine ⟨fun w hw => ?_, by omega, by omega⟩
  by_contra hc
  push_neg at hc
  set c : SemiLocal.PlacesOver K v := ⟨w, hw⟩
  have hca : c ≠ a := fun h => hc.1 (congrArg Subtype.val h)
  have hcb : c ≠ b := fun h => hc.2 (congrArg Subtype.val h)
  have p₃ : 0 < Module.finrank (Qv v) (Kv K w) := by
    haveI := hw
    exact finrank_pos' v w
  have := Finset.sum_le_sum_of_subset (f := fun u : SemiLocal.PlacesOver K v => Module.finrank (Qv v) (Kv K u.1))
    (Finset.subset_univ ({c, a, b} : Finset (SemiLocal.PlacesOver K v)))
  rw [Finset.sum_insert (by simp [hca, hcb]), Finset.sum_pair hab, hs] at this
  have e : Module.finrank (Qv v) (Kv K w) + (Module.finrank (Qv v) (Kv K w₁) + Module.finrank (Qv v) (Kv K w₂)) ≤ 2 := this
  omega

theorem places_nonsplit (h2 : Module.finrank ℚ K = 2) (v : Pl) (w : PlK K)
    [i : w.asIdeal.LiesOver v.asIdeal] (hu : ∀ w' : PlK K, w'.asIdeal.LiesOver v.asIdeal → w' = w) :
    Module.finrank (Qv v) (Kv K w) = 2 := by
  haveI : Unique (SemiLocal.PlacesOver K v) := ⟨⟨⟨w, i⟩⟩, fun x => Subtype.ext (hu x.1 x.2)⟩
  have hs := sum_finrank' h2 v
  rw [Fintype.sum_unique] at hs
  have : (default : SemiLocal.PlacesOver K v) = ⟨w, i⟩ := Subsingleton.elim _ _
  rw [this] at hs
  exact hs

end Deg

section Places

variable {K : Type} [Field K] [NumberField K]

theorem isUnit1_localCharK (c : HeckeCharacter K) (w : PlK K) : IsUnit1 (localChar c w) :=
  ⟨GroundTheory.Automorphic.GodementSection.continuous_localChar c w, fun x => by
    rw [GroundTheory.Automorphic.GodementSection.coe_localChar]; exact Circle.norm_coe _⟩

theorem isUnit1_cAt (c : HeckeCharacter K) (v : Pl) (w : PlK K) [w.asIdeal.LiesOver v.asIdeal] :
    IsUnit1 (cAt c v w) :=
  ⟨(isUnit1_localCharK c w).1.comp (Continuous.units_map _ (_root_.continuous_algebraMap (Qv v) (Kv K w))),
    fun x => (isUnit1_localCharK c w).2 _⟩

theorem algebraMap_bijective (v : Pl) (w : PlK K) [w.asIdeal.LiesOver v.asIdeal]
    (h1 : Module.finrank (Qv v) (Kv K w) = 1) : Function.Bijective (algebraMap (Qv v) (Kv K w)) := by
  refine ⟨(algebraMap (Qv v) (Kv K w)).injective, fun y => ?_⟩
  have hy : y ∈ (⊥ : Subalgebra (Qv v) (Kv K w)) := by
    rw [Subalgebra.bot_eq_top_of_finrank_eq_one h1]; trivial
  exact Algebra.mem_bot.1 hy

end Places

theorem continuous_charInv {A : Type} [AddCommGroup A] [TopologicalSpace A] (ψ : AddChar A Circle) (h : Continuous ψ) :
    Continuous (⇑(ψ⁻¹ : AddChar A Circle)) := by
  have : (⇑(ψ⁻¹ : AddChar A Circle)) = fun x => (ψ x)⁻¹ := by
    funext x; rw [AddChar.inv_apply, AddChar.map_neg_eq_inv]
  rw [this]
  exact h.inv

end GlobalTheory.CompanionTheory.BaseChangeFunctionalEquation
end
end
