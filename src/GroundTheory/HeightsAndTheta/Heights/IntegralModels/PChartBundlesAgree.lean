import Mathlib
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Statements

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

noncomputable section

theorem mem_away_of_heightOne (hHOI : HeightOneIntersection.Statement)
    (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    (Ω : Type) [Field Ω] [Algebra A Ω] (hinj : Function.Injective (algebraMap A Ω))
    (h : A) (hh : h ≠ 0) (a : Ω)
    (hs : ∃ s : A, s ≠ 0 ∧ ∃ (n : ℕ) (g : A), algebraMap A Ω (h ^ n * s) * a = algebraMap A Ω g)
    (hP : ∀ P : Ideal A, P.IsPrime → P.height = 1 → h ∉ P →
      ∃ t : A, t ∉ P ∧ ∃ (n : ℕ) (g : A), algebraMap A Ω (h ^ n * t) * a = algebraMap A Ω g) :
    ∃ (n : ℕ) (g : A), algebraMap A Ω (h ^ n) * a = algebraMap A Ω g := by
  let K := FractionRing A
  let φ : K →+* Ω := IsFractionRing.lift hinj
  have hφ : ∀ y : A, φ (algebraMap A K y) = algebraMap A Ω y := fun y =>
    IsFractionRing.lift_algebraMap hinj y
  have hφinj : Function.Injective φ := φ.injective
  obtain ⟨s, hs0, n, g, hg⟩ := hs
  have hns : h ^ n * s ≠ 0 := mul_ne_zero (pow_ne_zero _ hh) hs0
  have hnsΩ : algebraMap A Ω (h ^ n * s) ≠ 0 := by
    rw [Ne, ← map_zero (algebraMap A Ω)]
    exact fun e => hns (hinj e)
  let k : K := algebraMap A K g / algebraMap A K (h ^ n * s)
  have hk : φ k = a := by
    simp only [k, map_div₀, hφ]
    rw [← hg, mul_div_cancel_left₀ _ hnsΩ]

  have back : ∀ y z : A, algebraMap A Ω y * a = algebraMap A Ω z →
      algebraMap A K y * k = algebraMap A K z := by
    intro y z e
    apply hφinj
    rw [map_mul, hk, hφ, hφ, e]
  have hS : Submonoid.powers h ≤ nonZeroDivisors A :=
    powers_le_nonZeroDivisors_of_noZeroDivisors hh
  let A' : Subalgebra A K := Localization.subalgebra.ofField K (Submonoid.powers h) hS
  have : IsLocalization (Submonoid.powers h) A' :=
    Localization.subalgebra.isLocalization_ofField K (Submonoid.powers h) hS
  have : IsNoetherianRing A' :=
    IsLocalization.isNoetherianRing (Submonoid.powers h) A' inferInstance
  have : IsIntegrallyClosed A' :=
    isIntegrallyClosed_of_isLocalization A' (Submonoid.powers h) hS
  have key := hHOI A' K
  have hkmem : k ∈ Subalgebra.toSubmodule (⊥ : Subalgebra A' K) := by
    rw [key, Submodule.mem_iInf]
    intro P
    rw [Submodule.mem_iInf]
    intro hP1
    let Q : Ideal A := P.asIdeal.comap (algebraMap A A')
    have : Q.IsPrime := Ideal.comap_isPrime _ _
    have hQ1 : Q.height = 1 := by
      rw [← hP1]
      exact IsLocalization.height_under (Submonoid.powers h) P.asIdeal
    have hhQ : h ∉ Q := by
      intro hq
      have hu : IsUnit (algebraMap A A' h) :=
        IsLocalization.map_units A' (⟨h, Submonoid.mem_powers h⟩ : Submonoid.powers h)
      exact P.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hq hu)
    obtain ⟨t, htQ, m, z, hz⟩ := hP Q inferInstance hQ1 hhQ
    refine ⟨algebraMap A A' (h ^ m * t), ?_, ?_⟩
    · intro hmem
      have hmem' : h ^ m * t ∈ Q := hmem
      rcases (inferInstance : Q.IsPrime).mem_or_mem hmem' with h1 | h1
      · exact hhQ ((inferInstance : Q.IsPrime).mem_of_pow_mem _ h1)
      · exact htQ h1
    · rw [Subalgebra.mem_toSubmodule, Algebra.mem_bot]
      refine ⟨algebraMap A A' z, ?_⟩
      rw [← IsScalarTower.algebraMap_apply, Algebra.smul_def, ← IsScalarTower.algebraMap_apply]
      exact (back _ _ hz).symm
  rw [Subalgebra.mem_toSubmodule, Algebra.mem_bot] at hkmem
  obtain ⟨y, hy⟩ := hkmem
  obtain ⟨b, u, hu, hyb⟩ : ∃ (b u : A) (_ : u ∈ Submonoid.powers h),
      (y : K) = algebraMap A K b * (algebraMap A K u)⁻¹ := y.2
  obtain ⟨m, rfl⟩ := hu
  have hu0 : algebraMap A K (h ^ m) ≠ 0 := by
    rw [Ne, ← map_zero (algebraMap A K)]
    exact fun e => pow_ne_zero m hh (IsFractionRing.injective A K e)
  have hyk : (y : K) = k := hy
  refine ⟨m, b, ?_⟩
  have e1 : algebraMap A K (h ^ m) * k = algebraMap A K b := by
    rw [← hyk, hyb, mul_comm, mul_assoc, inv_mul_cancel₀ hu0, mul_one]
  have e2 := congrArg φ e1
  rwa [map_mul, hk, hφ, hφ] at e2

end

end GroundTheory.Heights₂.Heights.Model
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

theorem ChartBundlesAgree.lat_le (hHOI : HeightOneIntersection.Statement)
    {o : Type} [CommRing o] {Ω : Type} [Field Ω] [Algebra o Ω] {τ : Type} {x : τ → Ω} {r : ℕ}
    {E : Type} [AddCommGroup E] [Module Ω E] (B B' : ChartBundle o x r E) (i : τ) (hi : x i ≠ 0)
    (hN : IsNoetherianRing (chartRing o x i)) (hIC : IsIntegrallyClosed (chartRing o x i))
    (h1 : ∀ v ∈ B.lat i, ∃ s : chartRing o x i, s ≠ 0 ∧ (s : Ω) • v ∈ B'.lat i)
    (hq : ∀ q : Ideal (chartRing o x i), q.IsPrime → q.height = 1 → ∀ v : E,
      (∃ s : chartRing o x i, s ∉ q ∧ (s : Ω) • v ∈ B.lat i) →
        ∃ s : chartRing o x i, s ∉ q ∧ (s : Ω) • v ∈ B'.lat i) :
    B.lat i ≤ B'.lat i := by
  intro v hv
  let A := chartRing o x i
  let J : Ideal A :=
    { carrier := {a | (a : Ω) • v ∈ B'.lat i}
      add_mem' := fun {a b} ha hb => by
        change ((a + b : A) : Ω) • v ∈ B'.lat i
        rw [Subalgebra.coe_add, add_smul]
        exact add_mem ha hb
      zero_mem' := by
        change ((0 : A) : Ω) • v ∈ B'.lat i
        rw [Subalgebra.coe_zero, zero_smul]
        exact zero_mem _
      smul_mem' := fun c a ha => by
        change ((c * a : A) : Ω) • v ∈ B'.lat i
        rw [Subalgebra.coe_mul, mul_smul]
        exact B'.stable i c c.2 _ ha }
  have hJ : ∀ a : A, a ∈ J ↔ (a : Ω) • v ∈ B'.lat i := fun _ => Iff.rfl
  obtain ⟨k, f, c, hf, hc, hsum, hb⟩ := B'.frame i hi
  have hfJ : ∀ l, (⟨f l, hf l⟩ : A) ∈ J.radical := by
    intro l
    obtain ⟨b, hli, hsp, hiff⟩ := hb l
    obtain ⟨n, hn⟩ : ∃ n : ℕ, f l ^ n • v ∈ B'.lat i := by
      by_cases hf0 : f l = 0
      · exact ⟨1, by rw [hf0, pow_one, zero_smul]; exact zero_mem _⟩
      · let bs := Module.Basis.mk hli (by rw [hsp])
        have hbs : ∀ q, bs q = b q := fun q => Module.Basis.mk_apply hli _ q
        let a := bs.equivFun v

        have coord : ∀ t : A, (t : Ω) • v ∈ B'.lat i →
            ∀ q, ∃ n : ℕ, f l ^ n * ((t : Ω) * a q) ∈ A := by
          intro t ht q
          obtain ⟨a', ha', he⟩ := (hiff ((t : Ω) • v)).1 ⟨0, by rw [pow_zero, one_smul]; exact ht⟩
          have e1 : bs.equivFun ((t : Ω) • v) = a' := by
            rw [he]
            simp_rw [← hbs]
            rw [← Module.Basis.equivFun_symm_apply, LinearEquiv.apply_symm_apply]
          have e2 : a' q = (t : Ω) * a q := by
            rw [← e1, LinearEquiv.map_smul]
            rfl
          rw [← e2]
          exact ha' q
        refine (hiff v).2 ⟨a, fun q => ?_, ?_⟩
        · have hh : (⟨f l, hf l⟩ : A) ≠ 0 := fun e => hf0 (congrArg Subtype.val e)
          obtain ⟨m, g, hg⟩ := mem_away_of_heightOne hHOI A Ω Subtype.val_injective
            ⟨f l, hf l⟩ hh (a q)
            (by
              obtain ⟨s, hs0, hs⟩ := h1 v hv
              obtain ⟨n, hn⟩ := coord s hs q
              refine ⟨s, hs0, n, ⟨_, hn⟩, ?_⟩
              change f l ^ n * (s : Ω) * a q = f l ^ n * ((s : Ω) * a q)
              ring)
            (fun P hP hP1 _ => by
              have hv1 : ∃ s : A, s ∉ P ∧ (s : Ω) • v ∈ B.lat i :=
                ⟨1, fun h => hP.ne_top ((Ideal.eq_top_iff_one _).2 h), by
                  rw [OneMemClass.coe_one, one_smul]; exact hv⟩
              obtain ⟨t, htP, ht⟩ := hq P hP hP1 v hv1
              obtain ⟨n, hn⟩ := coord t ht q
              refine ⟨t, htP, n, ⟨_, hn⟩, ?_⟩
              change f l ^ n * (t : Ω) * a q = f l ^ n * ((t : Ω) * a q)
              ring)
          refine ⟨m, ?_⟩
          have hg' : f l ^ m * a q = (g : Ω) := hg
          rw [hg']
          exact g.2
        · rw [← bs.sum_equivFun v]
          simp_rw [hbs]
          rfl
    exact ⟨n, (hJ _).2 (by rw [SubmonoidClass.coe_pow]; exact hn)⟩
  have h1J : (1 : A) ∈ J.radical := by
    have e : (1 : A) = ∑ l, (⟨c l, hc l⟩ : A) * ⟨f l, hf l⟩ := by
      apply Subtype.ext
      rw [OneMemClass.coe_one, ← hsum, AddSubmonoidClass.coe_finsetSum]
      rfl
    rw [e]
    exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (hfJ l)
  have hJtop : J = ⊤ := Ideal.radical_eq_top.1 ((Ideal.eq_top_iff_one _).2 h1J)
  have h1 : (1 : A) ∈ J := hJtop ▸ Submodule.mem_top
  have h1' := (hJ 1).1 h1
  rwa [OneMemClass.coe_one, one_smul] at h1'

theorem ChartBundlesAgree.proof (hHOI : HeightOneIntersection.Statement) :
    ChartBundlesAgree.Statement := by
  intro o _ Ω _ _ τ x r E _ _ B B' i hi hN hIC h1 h2 hq
  exact le_antisymm
    (ChartBundlesAgree.lat_le hHOI B B' i hi hN hIC h1 fun q hq' hq1 v => (hq q hq' hq1 v).1)
    (ChartBundlesAgree.lat_le hHOI B' B i hi hN hIC h2 fun q hq' hq1 v => (hq q hq' hq1 v).2)

end

end GroundTheory.Heights₂.Heights.Model
end
