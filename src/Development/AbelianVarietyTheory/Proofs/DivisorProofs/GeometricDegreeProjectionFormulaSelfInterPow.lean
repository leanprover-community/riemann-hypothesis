import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericDegreePullbackFormula
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralMultipleExtensionStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CombPowIsometric

section
open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ArInt GlobalTheory.Mean4 GlobalTheory.Mean4O

set_option autoImplicit false
noncomputable section
open GlobalTheory.CxPts
open scoped ContDiff

namespace GlobalTheory.Mean4O.OnModelCInf

theorem cInfAt_of_manIs {F : Type} [Field F] {Y : Var F} {e : ℕ} {M : Man e} (I : ManIs M Y)
    {u : M.Fun} (hu : M.Smooth u) (a : Fin (M.n + 1)) (y : Pts Y (I.ε a)) :
    CInfAt (fun w => u a ((I.pt a).symm w)) y := by
  obtain ⟨j, hj⟩ := (M.A a).cover ((I.pt a).symm y)
  obtain ⟨c, hc⟩ := I.alg a j
  have h := hu a j
  rw [hc, Homeomorph.transOpenPartialHomeomorph_symm_apply, Homeomorph.transOpenPartialHomeomorph_target] at h
  rw [hc, Homeomorph.transOpenPartialHomeomorph_source] at hj
  have h' : ContDiffOn ℝ ∞ ((fun w => u a ((I.pt a).symm w)) ∘ c.finChart.symm)
      (c.finChart.target ∩ c.finChart.symm ⁻¹' Set.univ) := by
    simpa [Function.comp_def] using h
  refine cInfAt_of_chart isOpen_univ c ((c.contDiffOn_finChart_iff _ _ _).1 h') ?_ trivial
  simpa using hj

theorem baseChange_cInfAt : ∀ (F : Type) [Field F] [NumberField F] (X G : Scheme.{0}) (p : X ⟶ Sp (𝓞 F))
    (q : G ⟶ Sp F) (j : G ⟶ X), IsPullback j q p (spMap (algebraMap (𝓞 F) F)) →
    ∀ (τ : F →+* ℂ) (σ : 𝓞 F →+* ℂ) (m : CxPts q τ → CxPts p σ), (∀ z, (m z).1 = z.1 ≫ j) →
    ∀ (f : CxPts p σ → ℝ) (z : CxPts q τ), CInfAt (fun w => f (m w)) z → CInfAt f (m z) := by
  intro F _ _ X G p q j H τ σ m hm f z hz
  obtain ⟨W, ι, _, g, Φ, O, h₁, h₂, h₃, h₄, h₅⟩ := hz
  obtain ⟨W', hle, hx, n, g', hn, hg⟩ := GlobalTheory.T.exists_integral_multiple_extension F X G p q j H W _ (mem_ptsIn.1 h₁) ι g
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn
  have hval (w : CxPts q τ) (hw : w ∈ ptsIn q τ (j ⁻¹ᵁ W')) (a : ι) :
      ev p σ W' (g' a) (m w) = n * ev q τ W (g a) w := by
    rw [ev_of_comp hm, ← hg a, ev_mul, ev_res hle hw]
    congr 1
    rw [ev_eq hw, map_natCast]
  have hστ : spMap σ = spMap τ ≫ spMap (algebraMap (𝓞 F) F) := by
    rw [← (m z).2, hm, Category.assoc, H.w, ← Category.assoc, z.2]
  let s : CxPts p σ → CxPts q τ := fun y => ⟨H.lift y.1 (spMap τ) (y.2.trans hστ), H.lift_snd _ _ _⟩
  have hms (y : CxPts p σ) : m (s y) = y := Subtype.ext ((hm _).trans (H.lift_fst _ _ _))
  have hsm : s (m z) = z := Subtype.ext (H.hom_ext ((H.lift_fst _ _ _).trans (hm z))
    ((H.lift_snd _ _ _).trans z.2.symm))
  have hs : Continuous s := by
    refine Continuous.subtype_mk ?_ _
    rw [(Points.isEmbedding_of_isPullback H).continuous_iff]
    refine (continuous_subtype_val.prodMk (continuous_const (y := spMap τ))).congr fun y => ?_
    exact (Prod.ext (H.lift_fst _ _ _) (H.lift_snd _ _ _)).symm
  have hz' : z ∈ ptsIn q τ (j ⁻¹ᵁ W') := mem_ptsIn.2 hx
  have hmW : m z ∈ ptsIn p σ W' := by
    rw [mem_ptsIn, hm]
    exact hx
  have hd : ContDiff ℝ ∞ fun v : ι → ℂ => fun a => v a / (n : ℂ) :=
    contDiff_pi.2 fun a => (contDiff_apply ℝ ℂ a).div_const _
  refine ⟨W', ι, inferInstance, g', fun v => Φ fun a => v a / n, (fun v : ι → ℂ => fun a => v a / (n : ℂ)) ⁻¹' O,
    hmW, h₂.preimage hd.continuous, ?_, h₄.comp hd.contDiffOn fun v hv => hv, ?_⟩
  · show (fun a => ev p σ W' (g' a) (m z) / n) ∈ O
    simpa only [hval z hz', mul_div_cancel_left₀ _ hn'] using h₃
  · have ht : Filter.Tendsto s (nhds (m z)) (nhds z) := by
      have := hs.continuousAt (x := m z)
      rwa [ContinuousAt, hsm] at this
    filter_upwards [ht.eventually h₅, ht.eventually ((isOpen_ptsIn _).mem_nhds hz')] with y e hy
    have hv (a : ι) : ev p σ W' (g' a) y = n * ev q τ W (g a) (s y) := by
      have := hval (s y) hy a
      rwa [hms] at this
    calc f y = f (m (s y)) := by rw [hms]
      _ = Φ (fun a => ev q τ W (g a) (s y)) := e
      _ = Φ (fun a => ev p σ W' (g' a) y / n) := by
        congr 1
        funext a
        rw [hv, mul_div_cancel_left₀ _ hn']

theorem cInfAt_pull : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V : Cover Y) (e : ℕ) (M : Man e) (I : ManIs M Y) (ε : (𝓞 F →+* ℂ) → Fin (M.n + 1)) (π : ∀ σ, CxPts V.p σ → M.X (ε σ)), V.IsDown I ε π → ∀ u : M.Fun, M.Smooth u → ∀ σ (z : CxPts V.p σ), CxPts.CInfAt (M.pull ε π u σ) z := by
  intro F _ _ Y V e M I ε π hD u hu σ z
  obtain ⟨hσ, hw⟩ := hD σ
  have hm0 (w : CxPts (V.π ≫ Y.str) (I.ε (ε σ))) : (w.1 ≫ V.j) ≫ V.p = spMap σ := by
    rw [Category.assoc, V.pb.w, ← Category.assoc, w.2, show spMap σ = _ from congrArg spMap hσ.symm, spMap, spMap, spMap,
      ← Spec.map_comp]
    rfl
  let m : CxPts (V.π ≫ Y.str) (I.ε (ε σ)) → CxPts V.p σ := fun w => ⟨w.1 ≫ V.j, hm0 w⟩
  obtain ⟨w, hw1, hw2⟩ := hw z
  let z' : CxPts (V.π ≫ Y.str) (I.ε (ε σ)) := ⟨w, by rw [← Category.assoc, hw2]; exact (I.pt _ (π σ z)).2⟩
  have hz : m z' = z := Subtype.ext hw1
  have key (w' : CxPts (V.π ≫ Y.str) (I.ε (ε σ))) : M.pull ε π u σ (m w') =
      u (ε σ) ((I.pt (ε σ)).symm (Points.PtsOver.map V.π rfl _ w')) := by
    obtain ⟨w'', h1, h2⟩ := hw (m w')
    have e : w'' = w'.1 := V.pb.hom_ext h1 (by
      rw [← Category.assoc, h2, (I.pt _ (π σ (m w'))).2]
      exact w'.2.symm)
    show u (ε σ) (π σ (m w')) = _
    congr 1
    apply (I.pt (ε σ)).injective
    rw [Homeomorph.apply_symm_apply]
    exact Subtype.ext (h2.symm.trans (by rw [e]; rfl))
  have hY := CInfAt.pull V.π rfl (cInfAt_of_manIs I hu (ε σ) (Points.PtsOver.map V.π rfl _ z'))
  rw [← hz]
  exact baseChange_cInfAt F V.X V.G V.p (V.π ≫ Y.str) V.j V.pb _ σ m (fun _ => rfl) _ z'
    (hY.congr (.of_forall key))

end GlobalTheory.Mean4O.OnModelCInf
end
end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical

noncomputable section

namespace GlobalTheory.PolarDeg

theorem lin_coeff_eq {ι κ : Type} (s : Finset ι) (s' : Finset κ) (a : ι → ℝ) (e : ι → ℕ) (b : κ → ℝ) (e' : κ → ℕ)
    (h : ∀ t : ℝ, ∑ i ∈ s, a i * t ^ e i = ∑ j ∈ s', b j * t ^ e' j) :
    ∑ i ∈ s, (if e i = 1 then a i else 0) = ∑ j ∈ s', (if e' j = 1 then b j else 0) := by
  have hP : (∑ i ∈ s, Polynomial.C (a i) * Polynomial.X ^ e i) =
      ∑ j ∈ s', Polynomial.C (b j) * Polynomial.X ^ e' j := by
    apply Polynomial.funext
    intro t
    simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
      Polynomial.eval_X]
    exact h t
  have := congrArg (fun p => Polynomial.coeff p 1) hP
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow] at this
  simpa [eq_comm] using this

theorem num_expand {V : Type} [AddCommGroup V] [Module ℝ V] {n : ℕ}
    (f : MultilinearMap ℝ (fun _ : Fin (n + 1) => V) ℝ)
    (hf : ∀ (v : Fin (n + 1) → V) (π : Equiv.Perm (Fin (n + 1))), f (v ∘ π) = f v) (x y : V) (t : ℝ) :
    f (fun _ => x + t • y) =
      ∑ s : Finset (Fin (n + 1)), f (s.piecewise (fun _ => y) (fun _ => x)) * t ^ s.card := by
  have h1 : (fun _ : Fin (n + 1) => x + t • y) = (fun _ => t • y) + (fun _ => x) := by
    funext i; simp [add_comm]
  rw [h1, MultilinearMap.map_add_univ]
  refine Finset.sum_congr rfl fun s _ => ?_
  have h2 : s.piecewise (fun _ : Fin (n + 1) => t • y) (fun _ => x) =
      s.piecewise (fun i => (fun _ : Fin (n + 1) => t) i • (s.piecewise (fun _ => y) (fun _ => x)) i)
        (s.piecewise (fun _ => y) (fun _ => x)) := by
    funext i
    by_cases hi : i ∈ s <;> simp [Finset.piecewise, hi]
  rw [h2, MultilinearMap.map_piecewise_smul, Finset.prod_const, smul_eq_mul, mul_comm]

theorem num_lin {V : Type} [AddCommGroup V] [Module ℝ V] {n : ℕ}
    (f : MultilinearMap ℝ (fun _ : Fin (n + 1) => V) ℝ)
    (hf : ∀ (v : Fin (n + 1) → V) (π : Equiv.Perm (Fin (n + 1))), f (v ∘ π) = f v) (x y : V) :
    ∑ s : Finset (Fin (n + 1)), (if s.card = 1 then f (s.piecewise (fun _ => y) (fun _ => x)) else 0) =
      ((n : ℝ) + 1) * f (Fin.cons y fun _ => x) := by
  rw [← Finset.sum_filter]
  have hS : (Finset.univ.filter fun s : Finset (Fin (n + 1)) => s.card = 1) =
      Finset.univ.map ⟨fun i => {i}, Finset.singleton_injective⟩ := by
    ext s
    rw [Finset.mem_filter, Finset.mem_map, Finset.card_eq_one]
    simp only [Finset.mem_univ, true_and, Function.Embedding.coeFn_mk]
    constructor <;> rintro ⟨a, h⟩ <;> exact ⟨a, h.symm⟩
  rw [hS, Finset.sum_map]
  have h3 : ∀ i : Fin (n + 1), f (({i} : Finset (Fin (n + 1))).piecewise (fun _ => y) (fun _ => x)) =
      f (Fin.cons y fun _ => x) := by
    intro i
    rw [Finset.piecewise_singleton]
    have h4 : Function.update (fun _ : Fin (n + 1) => x) i y ∘ (Equiv.swap 0 i) =
        (Fin.cons y fun _ => x : Fin (n + 1) → V) := by
      rw [Function.update_comp_equiv]
      funext j
      refine Fin.cases ?_ (fun k => ?_) j
      · simp
      · simp [Function.update, Equiv.swap_apply_def]
    rw [← h4, hf]
  simp only [Function.Embedding.coeFn_mk, h3, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

end GlobalTheory.PolarDeg

namespace GlobalTheory.PolarDeg

open MvPolynomial in

theorem linRoot_add_smul {ι : Type} [Fintype ι] {N : ℕ} (u w : ι → Fin N → ℝ) (t : ℝ) :
    Formalism.DegreeFormula.linRoot (u + t • w) = C t * Formalism.DegreeFormula.linRoot w + Formalism.DegreeFormula.linRoot u := by
  simp only [Formalism.DegreeFormula.linRoot, Pi.add_apply, Pi.smul_apply, smul_eq_mul, C_add, C_mul, add_mul,
    Finset.sum_add_distrib, Finset.mul_sum, mul_neg, mul_assoc]
  ring

open MvPolynomial in

theorem arDeg_lin_mul_pow (D : D7) (Y : DV.ShimX D.what₂.Tau) (T : Real0 Y) (hT : TieDeg T) (B : ℝ) (hB : 2 ≤ B)
    (R : ℝ) (hR : Real.exp 2 ≤ R) (w u : Wt Y) :
    Y.arDeg (GlobalTheory.FlagAr.setB Y B) R (Formalism.DegreeFormula.linRoot w * Formalism.DegreeFormula.linRoot u ^ Formalism.MainNotions.WeightThresholdDefs.dimY Y) =
      ∑ c, (T.K B c).num (Fin.cons (T.L B c w + (T.K B c).ar ((T.F c).phR R w))
        fun _ => T.L B c u + (T.K B c).ar ((T.F c).phR R u)) := by
  set A := Y.arDeg (GlobalTheory.FlagAr.setB Y B) R with hA
  set lw := Formalism.DegreeFormula.linRoot w
  set lu := Formalism.DegreeFormula.linRoot u
  have hf : ∀ t : ℝ, A (Formalism.DegreeFormula.linRoot (u + t • w) ^ (Formalism.MainNotions.WeightThresholdDefs.dimY Y + 1)) =
      ∑ m ∈ Finset.range (Formalism.MainNotions.WeightThresholdDefs.dimY Y + 1 + 1), ((Formalism.MainNotions.WeightThresholdDefs.dimY Y + 1).choose m * A (lw ^ m * lu ^ (Formalism.MainNotions.WeightThresholdDefs.dimY Y + 1 - m))) * t ^ m := by
    intro t
    rw [linRoot_add_smul, add_pow, map_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    have h1 : (C t * lw) ^ m * lu ^ (Formalism.MainNotions.WeightThresholdDefs.dimY Y + 1 - m) * ((Formalism.MainNotions.WeightThresholdDefs.dimY Y + 1).choose m : MvPolynomial _ ℝ) =
        (t ^ m * ((Formalism.MainNotions.WeightThresholdDefs.dimY Y + 1).choose m : ℝ)) • (lw ^ m * lu ^ (Formalism.MainNotions.WeightThresholdDefs.dimY Y + 1 - m)) := by
      rw [MvPolynomial.smul_eq_C_mul, mul_pow, ← map_pow, C_mul, ← map_natCast (C : ℝ →+* MvPolynomial _ ℝ)]
      ring
    rw [h1, map_smul, smul_eq_mul]
    ring
  have hg : ∀ t : ℝ, ∑ c, T.fR B c (u + t • w) 0 R =
      ∑ p : Y.Comp × Finset (Fin (Formalism.MainNotions.WeightThresholdDefs.dimY Y + 1)),
        (T.K B p.1).num (p.2.piecewise (fun _ => T.L B p.1 w + (T.K B p.1).ar ((T.F p.1).phR R w))
          (fun _ => T.L B p.1 u + (T.K B p.1).ar ((T.F p.1).phR R u))) * t ^ p.2.card := by
    intro t
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun c _ => ?_
    have h2 : T.L B c (u + t • w) + (0 : ℝ) • T.a B c + (T.K B c).ar ((T.F c).phR R (u + t • w)) =
        (T.L B c u + (T.K B c).ar ((T.F c).phR R u)) + t • (T.L B c w + (T.K B c).ar ((T.F c).phR R w)) := by
      simp only [map_add, map_smul, zero_smul, add_zero, smul_add]
      abel
    rw [Real0.fR, Calc.top, h2]
    exact num_expand (T.K B c).num (T.K B c).symm _ _ t
  have hfg : ∀ t : ℝ,
      ∑ m ∈ Finset.range (Formalism.MainNotions.WeightThresholdDefs.dimY Y + 1 + 1), ((Formalism.MainNotions.WeightThresholdDefs.dimY Y + 1).choose m * A (lw ^ m * lu ^ (Formalism.MainNotions.WeightThresholdDefs.dimY Y + 1 - m))) * t ^ m =
      ∑ p : Y.Comp × Finset (Fin (Formalism.MainNotions.WeightThresholdDefs.dimY Y + 1)),
        (T.K B p.1).num (p.2.piecewise (fun _ => T.L B p.1 w + (T.K B p.1).ar ((T.F p.1).phR R w))
          (fun _ => T.L B p.1 u + (T.K B p.1).ar ((T.F p.1).phR R u))) * t ^ p.2.card := by
    intro t
    rw [← hf, ← hg]
    exact hT B hB R hR (u + t • w)
  have hc := lin_coeff_eq _ _ _ (fun m => m) _ (fun p : Y.Comp × Finset (Fin (Formalism.MainNotions.WeightThresholdDefs.dimY Y + 1)) => p.2.card) hfg
  rw [Fintype.sum_prod_type] at hc
  simp only [Finset.sum_ite_eq', Finset.mem_range] at hc
  have hsum : ∀ c, (∑ s : Finset (Fin (Formalism.MainNotions.WeightThresholdDefs.dimY Y + 1)), if s.card = 1 then
      (T.K B c).num (s.piecewise (fun _ => T.L B c w + (T.K B c).ar ((T.F c).phR R w))
        (fun _ => T.L B c u + (T.K B c).ar ((T.F c).phR R u))) else 0) =
      ((Formalism.MainNotions.WeightThresholdDefs.dimY Y : ℝ) + 1) * (T.K B c).num (Fin.cons (T.L B c w + (T.K B c).ar ((T.F c).phR R w))
        fun _ => T.L B c u + (T.K B c).ar ((T.F c).phR R u)) := fun c => by
    convert num_lin (T.K B c).num (T.K B c).symm _ _ using 5
  replace hc := hc.trans (Finset.sum_congr rfl fun c _ => hsum c)
  have hn1 : (0 : ℝ) < (Formalism.MainNotions.WeightThresholdDefs.dimY Y : ℝ) + 1 := by positivity
  rw [if_pos (by omega), Nat.choose_one_right, pow_one, Nat.add_sub_cancel, ← Finset.mul_sum] at hc
  push_cast at hc
  exact mul_left_cancel₀ hn1.ne' hc

end GlobalTheory.PolarDeg
end
end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open scoped ENNReal Classical
open MvPolynomial GlobalTheory.ArInt
open CategoryTheory AlgebraicGeometry GlobalTheory GlobalTheory.Mean4O GlobalTheory.HermLB

open GlobalTheory.Points ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi

noncomputable section

namespace GlobalTheory.SelfInterPow

theorem isSelfInter_pow : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → ∀ (L : HermLB p) (a : ℝ), L.IsSelfInter a → ∀ e : ℕ,
      (L.pow e).IsSelfInter ((e : ℝ) ^ (D + 1) * a) := by
  intro hC k _ X _ p D hX L a ha e
  obtain ⟨Φ, hΦ⟩ := ((hC.arExists k X p D hX).2 Unit fun _ => L).1
  have h₁ := (((hC.arIso k X p D hX).2 Unit _ Φ hΦ).1 ()).unique hX ha
  obtain ⟨H, hH, he⟩ := hΦ.1 fun _ => (e : ℤ)
  refine ⟨H, (hC.arIso k X p D hX).1 _ _ H (GlobalTheory.ArInt.isometric_comb_unit_pow k X p L e) hH, he.trans ?_⟩
  rw [← h₁, ← smul_eq_mul, ← map_smul, ArInt.lin, Fintype.sum_unique, mul_pow, ← map_pow, MvPolynomial.smul_eq_C_mul]
  simp

end GlobalTheory.SelfInterPow
end
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSAmp.PullPow

theorem gdeg_pull_and_isSelfInter_pow : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → (∀ (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp k), IsArithVar q D → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q), π (genericPoint Y) = genericPoint X → π.residueDegree (genericPoint Y) ≠ 0 → ∀ L : HermLB p, gdeg (L.pull π hπ) D = (π.residueDegree (genericPoint Y) : ℝ) * gdeg L D) ∧ ∀ (L : HermLB p) (n : ℕ) (a : ℝ), L.IsSelfInter a → (L.pow n).IsSelfInter ((n : ℝ) ^ (D + 1) * a) := by
  intro hC k _ X _ p D hX
  refine ⟨fun Y _ q hY π hπ hη hδ L => GlobalTheory.CovTest.gdegPull k X Y p q D hX hY π hπ hη hδ L, ?_⟩
  intro L n a ha
  exact GlobalTheory.SelfInterPow.isSelfInter_pow hC k X p D hX L a ha n

end GlobalTheory.HSAmp.PullPow

end
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.geometricDegree_projectionFormula_selfInter_pow : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → (∀ (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp k), IsArithVar q D → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q), π (genericPoint Y) = genericPoint X → π.residueDegree (genericPoint Y) ≠ 0 → ∀ L : HermLB p, gdeg (L.pull π hπ) D = (π.residueDegree (genericPoint Y) : ℝ) * gdeg L D) ∧ ∀ (L : HermLB p) (n : ℕ) (a : ℝ), L.IsSelfInter a → (L.pow n).IsSelfInter ((n : ℝ) ^ (D + 1) * a) := by
  atlas_forward_decl GlobalTheory.HSAmp.PullPow.gdeg_pull_and_isSelfInter_pow
end
