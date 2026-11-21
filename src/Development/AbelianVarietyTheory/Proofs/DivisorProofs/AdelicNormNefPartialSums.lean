import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.DualRef
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemConeOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsComb
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitKOfIsAlgClosed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsUnitRescaling
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsPullbackAlongCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticHeightTensorAdditiveOnCurves
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsModelPresentingDivisor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicNormNefIndicators
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InducedMetricShiftElement
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteExtensionSplittingTorsionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HessRelFnB
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KrullDimOneOfFiniteGeneric
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JGenSpecializes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommonRefinementCoversStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NefOverOfGeneratedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionSplitNormalBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentBasisTorsionCountStatement

section
open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Cartier GlobalTheory.ProjVar Formalism.BasicNotions GlobalTheory.TrueGeo

namespace GlobalTheory.TrueGeo

theorem Ext.w_add_le_max (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (e : Ext v)
    (x y : AlgebraicClosure F) : e.w (x + y) ≤ max (e.w x) (e.w y) := by
  have key : ∀ a b : AlgebraicClosure F, e.w a ≤ e.w b → e.w (a + b) ≤ e.w b := by
    intro a b hab
    by_cases hb : b = 0
    · subst hb
      have ha : a = 0 := e.w.eq_zero.1 (le_antisymm (by simpa using hab) (e.w.nonneg a))
      simp [ha]
    · have hwb : 0 < e.w b := e.w.pos hb
      have h1 : a / b ∈ e.O := by
        rw [e.mem_O, map_div₀]
        exact (div_le_one hwb).2 hab
      have h2 : 1 + a / b ∈ e.O := e.O.add_mem _ _ e.O.one_mem h1
      have h3 : e.w (1 + a / b) ≤ 1 := (e.mem_O _).1 h2
      have h4 : a + b = b * (1 + a / b) := by field_simp; ring
      rw [h4, map_mul]
      exact mul_le_of_le_one_right (e.w.nonneg b) h3
  rcases le_total (e.w x) (e.w y) with h | h
  · exact (key x y h).trans (le_max_right _ _)
  · rw [add_comm]; exact (key y x h).trans (le_max_left _ _)

example : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (e : Ext v) (x y : AlgebraicClosure F),
    e.w (x + y) ≤ max (e.w x) (e.w y) := Ext.w_add_le_max

end GlobalTheory.TrueGeo
end

section
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.ArInt GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.Mean4O GlobalTheory.LineNorm GlobalTheory.CoverNorm GlobalTheory.VertForm GlobalTheory.HtGen
open Formalism.MainNotions.DIV.Cons (intO)
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HtGen

theorem w_pow_succ_sub_le {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)} (e : TrueGeo.Ext v)
    (α β : AlgebraicClosure F) {E : ℝ} (hE : 0 ≤ E) (hα : e.w α * E ≤ 1) (hβ : e.w β * E ≤ 1) (k : ℕ) :
    e.w (α ^ (k + 1) - β ^ (k + 1)) * E ^ (k + 1) ≤ e.w (α - β) * E := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h : α ^ (k + 1 + 1) - β ^ (k + 1 + 1) = α ^ (k + 1) * (α - β) + (α ^ (k + 1) - β ^ (k + 1)) * β := by ring
    rw [h]
    have hmax := TrueGeo.Ext.w_add_le_max F v e (α ^ (k + 1) * (α - β)) ((α ^ (k + 1) - β ^ (k + 1)) * β)
    have hEk : 0 ≤ E ^ (k + 1 + 1) := pow_nonneg hE _
    refine (mul_le_mul_of_nonneg_right hmax hEk).trans ?_
    rw [max_mul_of_nonneg _ _ hEk]
    refine max_le ?_ ?_
    · rw [map_mul, map_pow]
      have e1 : e.w α ^ (k + 1) * e.w (α - β) * E ^ (k + 1 + 1) = (e.w α * E) ^ (k + 1) * (e.w (α - β) * E) := by ring
      rw [e1]
      exact mul_le_of_le_one_left (mul_nonneg (e.w.nonneg _) hE) (pow_le_one₀ (mul_nonneg (e.w.nonneg _) hE) hα)
    · rw [map_mul]
      have e1 : e.w (α ^ (k + 1) - β ^ (k + 1)) * e.w β * E ^ (k + 1 + 1) =
          (e.w (α ^ (k + 1) - β ^ (k + 1)) * E ^ (k + 1)) * (e.w β * E) := by ring
      rw [e1]
      exact (mul_le_of_le_one_right (mul_nonneg (e.w.nonneg _) (pow_nonneg hE _)) hβ).trans ih

theorem w_pow_sub_le {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)} (e : TrueGeo.Ext v)
    (α β : AlgebraicClosure F) {E : ℝ} (hE : 0 ≤ E) (hα : e.w α * E ≤ 1) (hβ : e.w β * E ≤ 1) {m : ℕ} (hm : 0 < m) :
    e.w (α ^ m - β ^ m) * E ^ m ≤ e.w (α - β) * E := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
  exact w_pow_succ_sub_le e α β hE hα hβ k

theorem unitAt_zpow' {X : Scheme.{0}} [IsIntegral X] {x : X} {f : X.functionField} (h : UnitAt x f) (a : ℤ) :
    UnitAt x (f ^ a) := by
  obtain ⟨_, ⟨u, rfl⟩, rfl⟩ := h
  refine ⟨((u ^ a : _ˣ) : X.presheaf.stalk x), Units.isUnit _, ?_⟩
  exact (congrArg Units.val (map_zpow (Units.map (algebraMap (X.presheaf.stalk x) X.functionField).toMonoidHom) u a)).trans
    (Units.val_zpow_eq_zpow_val _ _)

theorem regAt_sub' {X : Scheme.{0}} [IsIntegral X] {x : X} {f g : X.functionField} (hf : RegAt x f) (hg : RegAt x g) :
    RegAt x (f - g) :=
  have ⟨a, ha⟩ := hf; have ⟨b, hb⟩ := hg; ⟨a - b, by rw [map_sub, ha, hb]⟩

theorem valAt_sub' {K : Type} [Field K] {X : Scheme.{0}} [IsIntegral X] {y : Sp K ⟶ X} {f g : X.functionField}
    (hf : RegAt (below y) f) (hg : RegAt (below y) g) : TrueGeo.valAt y (f - g) = TrueGeo.valAt y f - TrueGeo.valAt y g := by
  obtain ⟨a, rfl⟩ := hf
  obtain ⟨b, rfl⟩ := hg
  rw [← map_sub, TrueGeo.Res.valAt_algebraMap, TrueGeo.Res.valAt_algebraMap, TrueGeo.Res.valAt_algebraMap, map_sub]

theorem genOver_pow_div : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V : Cover Y) (f : Y.X → Y.Fn)
    (ψ φ : ∀ v : HeightOneSpectrum (𝓞 F), TrueGeo.Ext v → AlgPt Y → ℝ) (l m : ℕ) (a : ℤ), l ≠ 0 → 0 < m →
    (∀ v e y, (l : 𝓞 F) ∈ v.asIdeal → φ v e y = m * ψ v e y + a * Real.log (e.w (l : AlgebraicClosure F))) →
    GenOver V f ψ l → GenOver V (fun y => f y ^ m) φ l := by
  intro F _ _ Y V f ψ φ l m a hl hm hφ ⟨n, U, s, hU, hreg, hnorm⟩
  have hlF : (l : F) ≠ 0 := Nat.cast_ne_zero.2 hl
  have hl1 : ∀ z : V.G, UnitAt z (l : V.G.functionField) := fun z => by
    have := TrueGeo.IndScale.unitAt_constFn (V.π ≫ Y.str) z hlF
    rwa [map_natCast] at this
  have hlu : ∀ z : V.G, UnitAt z ((l : V.G.functionField) ^ (-a)) := fun z => unitAt_zpow' (hl1 z) (-a)
  have key : ∀ (p : Y.X) (x : V.X) (J : Fin n), (s x J ^ m * (l : V.G.functionField) ^ (-a)) / V.φ (f p ^ m) =
      (s x J / V.φ (f p)) ^ m * (l : V.G.functionField) ^ (-a) := by
    intro p x J
    rw [map_pow, div_pow, div_mul_eq_mul_div]
  have keyd : ∀ (p : Y.X) (x x' : V.X) (J : Fin n),
      (s x J ^ m * (l : V.G.functionField) ^ (-a) - s x' J ^ m * (l : V.G.functionField) ^ (-a)) / V.φ (f p ^ m) =
      ((s x J / V.φ (f p)) ^ m - (s x' J / V.φ (f p)) ^ m) * (l : V.G.functionField) ^ (-a) := by
    intro p x x' J
    rw [map_pow, div_pow, div_pow, sub_mul, div_mul_eq_mul_div, div_mul_eq_mul_div, sub_div]
  refine ⟨n, U, fun x J => s x J ^ m * (l : V.G.functionField) ^ (-a), hU, fun x J z hz => ?_, ?_⟩
  · beta_reduce
    rw [key]
    exact (TrueGeo.Res.regAt_pow (hreg x J z hz) m).mul (hlu z).regAt
  · intro v e y z yt hlv hzy hyt x hx
    beta_reduce
    have hπ : V.π (below z) = below y.1 := by rw [← hzy]; rfl
    have hmem : ∀ x', ⊤ ≤ yt ⁻¹ᵁ U x' → V.j (below z) ∈ U x' := fun x' h => by
      have h1 : (z ≫ V.j) (IsLocalRing.closedPoint _) ∈ U x' := by rw [← hyt]; exact h (Set.mem_univ _)
      exact h1
    have hα : ∀ x', ⊤ ≤ yt ⁻¹ᵁ U x' → ∀ J, RegAt (below z) (s x' J / V.φ (f (below y.1))) := fun x' h J => by
      have := hreg x' J (below z) (hmem x' h)
      rwa [hπ] at this
    have hl0 : (l : AlgebraicClosure F) ≠ 0 := by
      have := (algebraMap F (AlgebraicClosure F)).injective.ne hlF
      rwa [map_natCast, map_zero] at this
    have hwl : 0 < e.w (l : AlgebraicClosure F) := e.w.pos hl0
    have hvl : TrueGeo.valAt z ((l : V.G.functionField) ^ (-a)) = (l : AlgebraicClosure F) ^ (-a) := by
      rw [(TrueGeo.Base.valAt_zpow z (hl1 (below z))).2 (-a)]
      congr 1
      rw [← map_natCast (algebraMap (V.G.presheaf.stalk (below z)) V.G.functionField), TrueGeo.Res.valAt_algebraMap,
        map_natCast]
    have hE : Real.exp (φ v e y) = Real.exp (ψ v e y) ^ m * e.w (l : AlgebraicClosure F) ^ a := by
      rw [hφ v e y hlv, Real.exp_add, Real.exp_nat_mul, mul_comm (a : ℝ), ← Real.rpow_def_of_pos hwl, Real.rpow_intCast]
    have hscale : ∀ β, RegAt (below z) β → e.w (TrueGeo.valAt z (β * (l : V.G.functionField) ^ (-a))) *
        Real.exp (φ v e y) = e.w (TrueGeo.valAt z β) * Real.exp (ψ v e y) ^ m := by
      intro β hβ
      rw [TrueGeo.Res.valAt_mul hβ (hlu _).regAt, hvl, map_mul, map_zpow₀, hE]
      have h1 : e.w (l : AlgebraicClosure F) ^ (-a) * e.w (l : AlgebraicClosure F) ^ a = 1 := by
        rw [zpow_neg, inv_mul_cancel₀ (zpow_ne_zero _ hwl.ne')]
      linear_combination (e.w (TrueGeo.valAt z β) * Real.exp (ψ v e y) ^ m) * h1
    obtain ⟨h1, ⟨J₀, h2⟩, h3⟩ := hnorm v e y z yt hlv hzy hyt x hx
    have hE0 : 0 ≤ Real.exp (ψ v e y) := (Real.exp_pos _).le
    refine ⟨fun J => ?_, ⟨J₀, ?_⟩, fun x' hx' J => ?_⟩
    · rw [key, hscale _ (TrueGeo.Res.regAt_pow (hα x hx J) m), TrueGeo.Res.valAt_pow (hα x hx J), map_pow, ← mul_pow]
      exact pow_le_one₀ (mul_nonneg (e.w.nonneg _) hE0) (h1 J)
    · rw [key, hscale _ (TrueGeo.Res.regAt_pow (hα x hx J₀) m), TrueGeo.Res.valAt_pow (hα x hx J₀), map_pow,
        ← mul_pow, h2, one_pow]
    · have h1' := (hnorm v e y z yt hlv hzy hyt x' hx').1 J
      have h3' := h3 x' hx' J
      rw [sub_div, valAt_sub' (hα x hx J) (hα x' hx' J)] at h3'
      rw [keyd, hscale _ (regAt_sub' (TrueGeo.Res.regAt_pow (hα x hx J) m) (TrueGeo.Res.regAt_pow (hα x' hx' J) m)),
        valAt_sub' (TrueGeo.Res.regAt_pow (hα x hx J) m) (TrueGeo.Res.regAt_pow (hα x' hx' J) m),
        TrueGeo.Res.valAt_pow (hα x hx J), TrueGeo.Res.valAt_pow (hα x' hx' J)]
      exact (w_pow_sub_le e _ _ hE0 (h1 J) h1' hm).trans_lt h3'

end GlobalTheory.HtGen
end
end

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.ArInt GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.Mean4O GlobalTheory.LineNorm GlobalTheory.CoverNorm GlobalTheory.VertForm GlobalTheory.HtGen
open Formalism.MainNotions.DIV.Cons (intO)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_over_power : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V : Cover Y) (f : Y.X → Y.Fn) (ψ φ : ∀ v : HeightOneSpectrum (𝓞 F), TrueGeo.Ext v → AlgPt Y → ℝ) (l m : ℕ) (a : ℤ), l ≠ 0 → 0 < m → (∀ v e y, (l : 𝓞 F) ∈ v.asIdeal → φ v e y = m * ψ v e y + a * Real.log (e.w (l : AlgebraicClosure F))) → GenOver V f ψ l → GenOver V (fun y => f y ^ m) φ l := by
  atlas_forward_decl GlobalTheory.HtGen.genOver_pow_div
end

section
open CategoryTheory AlgebraicGeometry

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.NormFnField

variable {Z : Scheme.{0}} [IsIntegral Z] {K : Type} [Field K] [Algebra Z.functionField K]

theorem stalkIso_germ_app (g : Spec (CommRingCat.of K) ⟶ Z)
    (hg : g = Spec.map (CommRingCat.ofHom (algebraMap Z.functionField K)) ≫
      Z.fromSpecStalk (genericPoint Z))
    (U : Z.Opens) (hU : g (IsLocalRing.closedPoint K) ∈ U) (a : Γ(Z, U)) :
    (stalkClosedPointIso (CommRingCat.of K)).hom
        ((Spec (CommRingCat.of K)).presheaf.germ (g ⁻¹ᵁ U) (IsLocalRing.closedPoint K) hU
          (g.app U a)) =
      algebraMap Z.functionField K
        (Z.presheaf.germ U (genericPoint Z) ((genericPoint_specializes _).mem_open U.isOpen hU) a) := by
  subst hg
  have e := Scheme.germ_stalkClosedPointTo_Spec_fromSpecStalk
    (CommRingCat.ofHom (algebraMap Z.functionField K)) U hU
  refine Eq.trans ?_ (congrArg (fun q => q.hom a) e)
  change _ = (stalkClosedPointIso (CommRingCat.of K)).hom.hom ((Scheme.Hom.stalkMap _ _).hom
    ((Z.presheaf.germ U _ hU).hom a))
  congr 1
  exact (Scheme.Hom.germ_stalkMap_apply _ _ _ _ _).symm

end GlobalTheory.NormFnField

namespace GlobalTheory.NormFnField

theorem normalization_functionField : ∀ (Z : AlgebraicGeometry.Scheme.{0}) [AlgebraicGeometry.IsIntegral Z] (K : Type) [Field K] [Algebra Z.functionField K] [FiniteDimensional Z.functionField K] (g : AlgebraicGeometry.Spec (CommRingCat.of K) ⟶ Z) [AlgebraicGeometry.QuasiCompact g] [AlgebraicGeometry.QuasiSeparated g], g = AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap Z.functionField K)) ≫ Z.fromSpecStalk (genericPoint Z) → ∃ (hη : g.fromNormalization (genericPoint g.normalization) ⤳ genericPoint Z) (ψ : K →+* g.normalization.functionField), ψ.comp (algebraMap Z.functionField K) = GlobalTheory.TrueGeo.SmallSec.fnMap g.fromNormalization hη := by
  intro Z _ K _ _ _ g _ _ hg
  set cp : Spec (CommRingCat.of K) := IsLocalRing.closedPoint K with hcp
  set j := g.toNormalization with hj
  set π := g.fromNormalization with hπ
  have hjπ : j ≫ π = g := g.toNormalization_fromNormalization
  have h1 : j cp ⤳ genericPoint g.normalization := by
    rw [specializes_iff_mem_closure]
    have hr : Set.range j = {j cp} :=
      Set.ext fun y => ⟨fun ⟨z, hz⟩ => hz ▸ congrArg j (Subsingleton.elim z cp),
        fun hy => ⟨cp, hy.symm⟩⟩
    rw [← hr, g.toNormalization.denseRange.closure_range]
    trivial
  have hgcp : g cp ⤳ genericPoint Z := by
    have : g cp ∈ Set.range (Z.fromSpecStalk (genericPoint Z)) := by
      rw [hg, Scheme.Hom.comp_apply]; exact ⟨_, rfl⟩
    rwa [Scheme.range_fromSpecStalk] at this
  have hη : π (genericPoint g.normalization) ⤳ genericPoint Z := by
    have := (genericPoint_specializes (j cp)).map π.continuous
    rw [← Scheme.Hom.comp_apply, hjπ] at this
    exact this.trans hgcp
  refine ⟨hη, ?_⟩
  let φ : g.normalization.functionField ⟶ CommRingCat.of K :=
    g.normalization.presheaf.stalkSpecializes h1 ≫ Scheme.stalkClosedPointTo j

  have hφ : ∀ (V : g.normalization.Opens) (hV : genericPoint g.normalization ∈ V) (s : Γ(g.normalization, V)),
      φ.hom (g.normalization.presheaf.germ V _ hV s) =
        (stalkClosedPointIso (CommRingCat.of K)).hom
          ((Spec (CommRingCat.of K)).presheaf.germ (j ⁻¹ᵁ V) cp (h1.mem_open V.isOpen hV) (j.app V s)) := by
    intro V hV s
    change (Scheme.stalkClosedPointTo j).hom ((g.normalization.presheaf.stalkSpecializes h1).hom
      (g.normalization.presheaf.germ V _ hV s)) = _
    rw [TopCat.Presheaf.germ_stalkSpecializes_apply]
    change (stalkClosedPointIso (CommRingCat.of K)).hom.hom ((Scheme.Hom.stalkMap j cp).hom _) = _
    congr 1
    exact Scheme.Hom.germ_stalkMap_apply _ _ _ _ _

  have hφf : ∀ z, φ.hom (GlobalTheory.TrueGeo.SmallSec.fnMap π hη z) = algebraMap Z.functionField K z := by
    intro z
    obtain ⟨U, hU, a, rfl⟩ := Z.presheaf.exists_germ_eq z
    have e1 : GlobalTheory.TrueGeo.SmallSec.fnMap π hη (Z.presheaf.germ U _ hU a) =
        g.normalization.presheaf.germ (π ⁻¹ᵁ U) _ (hη.mem_open U.isOpen hU) (π.app U a) := by
      change (π.stalkMap _).hom ((Z.presheaf.stalkSpecializes hη).hom (Z.presheaf.germ U _ hU a)) = _
      rw [TopCat.Presheaf.germ_stalkSpecializes_apply]
      exact Scheme.Hom.germ_stalkMap_apply _ _ _ _ _
    rw [e1]
    refine (hφ _ _ _).trans ?_
    exact stalkIso_germ_app (j ≫ π) (hjπ.trans hg) U
      ((h1.map π.continuous).mem_open U.isOpen (hη.mem_open U.isOpen hU)) a
  have hinj : Function.Injective φ.hom := φ.hom.injective
  have hsurj : Function.Surjective φ.hom := by
    intro k
    obtain ⟨_, ⟨U, hU, rfl⟩, hηU, -⟩ :=
      Z.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (genericPoint Z)) isOpen_univ
    haveI : Nonempty U := ⟨⟨_, hηU⟩⟩
    haveI := functionField_isFractionRing_of_isAffineOpen Z U hU
    letI : Algebra Γ(Z, U) K :=
      ((algebraMap Z.functionField K).comp (algebraMap Γ(Z, U) Z.functionField)).toAlgebra
    haveI : IsScalarTower Γ(Z, U) Z.functionField K := .of_algebraMap_eq' rfl
    have hAinj : Function.Injective (algebraMap Γ(Z, U) K) :=
      (algebraMap Z.functionField K).injective.comp (IsFractionRing.injective Γ(Z, U) Z.functionField)
    have halg : IsAlgebraic Γ(Z, U) k :=
      (IsFractionRing.isAlgebraic_iff Γ(Z, U) Z.functionField K).mpr (Algebra.IsAlgebraic.isAlgebraic k)
    obtain ⟨y, hy0, hc⟩ := halg.exists_integral_multiple
    have hcU : g cp ∈ U := hgcp.mem_open U.isOpen hηU
    letI : Algebra Γ(Z, U) Γ(Spec (CommRingCat.of K), g ⁻¹ᵁ U) := (g.app U).hom.toAlgebra
    let ρ : Γ(Spec (CommRingCat.of K), g ⁻¹ᵁ U) →+* K :=
      ((Spec (CommRingCat.of K)).presheaf.germ (g ⁻¹ᵁ U) cp hcU ≫
        (stalkClosedPointIso (CommRingCat.of K)).hom).hom
    have hρA : ∀ a : Γ(Z, U), ρ (algebraMap _ _ a) = algebraMap Γ(Z, U) K a :=
      fun a => stalkIso_germ_app g hg U hcU a
    have htop : g ⁻¹ᵁ U = ⊤ := Scheme.preimage_eq_top_of_closedPoint_mem g hcU
    let res := (Spec (CommRingCat.of K)).presheaf.map (homOfLE (le_top : g ⁻¹ᵁ U ≤ ⊤)).op
    have hres : Function.Bijective res.hom := by
      have : IsIso res := by
        have e : homOfLE (le_top : g ⁻¹ᵁ U ≤ ⊤) = eqToHom htop := Subsingleton.elim _ _
        simp only [res, e]; infer_instance
      exact ConcreteCategory.bijective_of_isIso res
    have hρres : ∀ t, ρ (res.hom t) = (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom t := by
      intro t
      change (stalkClosedPointIso _).hom.hom (((Spec _).presheaf.germ _ cp hcU).hom (res.hom t)) = _
      refine (congrArg (stalkClosedPointIso (CommRingCat.of K)).hom.hom
        (TopCat.Presheaf.germ_res_apply (Spec (CommRingCat.of K)).presheaf
          (homOfLE (le_top : g ⁻¹ᵁ U ≤ ⊤)) cp hcU t)).trans ?_
      exact congrArg (fun q => q.hom t) (germ_stalkClosedPointIso_hom (CommRingCat.of K))
    have hρ : Function.Bijective ρ := by
      have hb : Function.Bijective (ρ ∘ res.hom) := by
        rw [show ρ ∘ res.hom = (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom from funext hρres]
        exact ConcreteCategory.bijective_of_isIso _
      exact (Function.Bijective.of_comp_iff ρ hres).mp hb
    let ρA : Γ(Spec (CommRingCat.of K), g ⁻¹ᵁ U) →ₐ[Γ(Z, U)] K := { ρ with commutes' := hρA }
    obtain ⟨r, hr⟩ := hρ.2 (y • k)
    have hrint : IsIntegral Γ(Z, U) r :=
      (isIntegral_algHom_iff ρA hρ.1).mp (by rw [show ρA r = y • k from hr]; exact hc)
    let b : Γ(g.normalization, π ⁻¹ᵁ U) := (g.normalizationObjIso hU).inv.hom ⟨r, hrint⟩
    have hξU : genericPoint g.normalization ∈ π ⁻¹ᵁ U := hη.mem_open U.isOpen hηU
    have hb : φ.hom (g.normalization.presheaf.germ _ _ hξU b) = y • k := by
      refine (hφ _ _ _).trans ?_
      have hv : ((g.normalizationObjIso hU).hom ≫
          CommRingCat.ofHom (Subalgebra.val _).toRingHom).hom b = r := by
        change ((g.normalizationObjIso hU).hom.hom ((g.normalizationObjIso hU).inv.hom ⟨r, hrint⟩)).1 = r
        rw [Iso.inv_hom_id_apply]
      rw [g.normalizationObjIso_hom_val hU, Scheme.Hom.appLE] at hv
      rw [← hr, ← hv]
      change _ = (stalkClosedPointIso _).hom.hom (((Spec _).presheaf.germ _ cp hcU).hom
        (((Spec _).presheaf.map _).hom ((g.toNormalization.app _).hom b)))
      exact congrArg (stalkClosedPointIso (CommRingCat.of K)).hom.hom
        (TopCat.Presheaf.germ_res_apply (Spec (CommRingCat.of K)).presheaf _ cp hcU _).symm
    have hy : φ.hom (GlobalTheory.TrueGeo.SmallSec.fnMap π hη (Z.presheaf.germ U _ hηU y)) =
        algebraMap Γ(Z, U) K y := hφf _
    have hy0' : algebraMap Γ(Z, U) K y ≠ 0 := fun h => hy0 (hAinj (h.trans (map_zero _).symm))
    refine ⟨g.normalization.presheaf.germ _ _ hξU b *
      (GlobalTheory.TrueGeo.SmallSec.fnMap π hη (Z.presheaf.germ U _ hηU y))⁻¹, ?_⟩
    rw [map_mul, map_inv₀, hb, hy, Algebra.smul_def]
    field_simp
  let e := RingEquiv.ofBijective φ.hom ⟨hinj, hsurj⟩
  refine ⟨e.symm.toRingHom, ?_⟩
  ext z
  apply hinj
  change e (e.symm (algebraMap _ K z)) = φ.hom (GlobalTheory.TrueGeo.SmallSec.fnMap π hη z)
  rw [hφf]
  exact e.apply_symm_apply _

end GlobalTheory.NormFnField
end
end

section
open CategoryTheory AlgebraicGeometry
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_point_morphism_factorization : ∀ (Z : AlgebraicGeometry.Scheme.{0}) [AlgebraicGeometry.IsIntegral Z] (K : Type) [Field K] [Algebra Z.functionField K] [FiniteDimensional Z.functionField K] (g : AlgebraicGeometry.Spec (CommRingCat.of K) ⟶ Z) [AlgebraicGeometry.QuasiCompact g] [AlgebraicGeometry.QuasiSeparated g], g = AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap Z.functionField K)) ≫ Z.fromSpecStalk (genericPoint Z) → ∃ (hη : g.fromNormalization (genericPoint g.normalization) ⤳ genericPoint Z) (ψ : K →+* g.normalization.functionField), ψ.comp (algebraMap Z.functionField K) = GlobalTheory.TrueGeo.SmallSec.fnMap g.fromNormalization hη := by
  first | exact @GlobalTheory.NormFnField.normalization_functionField | exact GlobalTheory.NormFnField.normalization_functionField | (intros; apply GlobalTheory.NormFnField.normalization_functionField <;> assumption)
end

section
open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.Mean4 GlobalTheory.Mean4O

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Mean4O.NormCover

theorem exists_cover (F : Type) [Field F] [NumberField F] (Y : Var F) (M : TrueGeo.Model Y) (K : Type) [Field K]
    [Algebra Y.Fn K] [FiniteDimensional Y.Fn K] :
    ∃ (V : Cover Y) (ρ : V.X ⟶ M.X) (ψ : K →+* V.G.functionField),
      V.j ≫ ρ = V.π ≫ M.j ∧ ψ.comp (algebraMap Y.Fn K) = V.φ := by
  have := M.ar.isIntegral
  have := M.ar.isLocallyNoetherian
  have : IsProper M.p := CommonModel.isProper_of_isProjOver M.ar.isProjOver
  have : IsPreimmersion M.j := GlobalTheory.TrueGeo.SmallSec.isPreimmersion_j M
  have : CharZero Y.Fn := charZero_of_injective_algebraMap (algebraMap F Y.Fn).injective
  have : CharZero K := charZero_of_injective_algebraMap (algebraMap Y.Fn K).injective
  let η := genericPoint Y.X
  let α : Y.X.presheaf.stalk η ⟶ CommRingCat.of K := CommRingCat.ofHom (algebraMap Y.Fn K)
  let g : Spec (.of K) ⟶ Y.X := Spec.map α ≫ Y.X.fromSpecStalk η
  let β : M.X.presheaf.stalk (M.j η) ⟶ CommRingCat.of K := M.j.stalkMap η ≫ α
  let f : Spec (.of K) ⟶ M.X := Spec.map β ≫ M.X.fromSpecStalk (M.j η)
  have hf : f = g ≫ M.j := by
    simp only [f, g, β, Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkMap_fromSpecStalk]
  have hfin : IsFinite f.fromNormalization := by
    refine GlobalTheory.isFinite_fromNormalization_SpecMap_fromSpecStalk M.p (M.j η) β ?_
    have h1 : (M.j.stalkMap η).hom.FiniteType :=
      RingHom.FiniteType.of_surjective _ (M.j.stalkMap_surjective η)
    have h2 : (algebraMap Y.Fn K).FiniteType := (RingHom.finite_algebraMap.2 inferInstance).finiteType
    exact (RingHom.FiniteType.comp h2 h1).essFiniteType
  have hb := GlobalTheory.isPullback_normalizationMap_of_isLocalization (nonZeroDivisors (𝓞 F)) M.pb
    (GlobalTheory.isPullback_id_of_mono g M.j f hf)
  have : IsFinite g.fromNormalization := MorphismProperty.of_isPullback hb hfin
  let pt : Spec (.of K) := IsLocalRing.closedPoint (CommRingCat.of K)
  have hgη : g pt = η := by
    change Y.X.fromSpecStalk η (Spec.map α pt) = η
    rw [show Spec.map α pt = IsLocalRing.closedPoint (Y.X.presheaf.stalk η) from
      Subsingleton.elim (α := PrimeSpectrum (Y.X.presheaf.stalk η)) _ _]
    exact Scheme.fromSpecStalk_closedPoint
  have hg0 : η ∈ Set.range g := ⟨pt, hgη⟩
  have : IsDominant g := ⟨(dense_iff_closure_eq.2 (genericPoint_spec Y.X)).mono
    (Set.singleton_subset_iff.2 hg0)⟩
  have hfη : f pt = M.j η := by
    rw [hf]
    change M.j (g pt) = M.j η
    rw [hgη]
  have : IsDominant f := by
    refine ⟨?_⟩
    have h0 : M.j η ∈ Set.range f := ⟨pt, hfη⟩
    have h1 : genericPoint M.X ∈ closure (Set.range f) :=
      closure_mono (Set.singleton_subset_iff.2 h0)
        (specializes_iff_mem_closure.1 (GlobalTheory.TrueGeo.SmallSec.j_gen_specializes M) :
          genericPoint M.X ∈ closure ({M.j η} : Set M.X))
    have h2 : closure ({genericPoint M.X} : Set M.X) ⊆ closure (Set.range f) :=
      closure_minimal (Set.singleton_subset_iff.2 h1) isClosed_closure
    rw [show closure ({genericPoint M.X} : Set M.X) = Set.univ from genericPoint_spec M.X] at h2
    exact dense_iff_closure_eq.2 (Set.eq_univ_of_univ_subset h2)
  have : IsDominant g.fromNormalization := by
    have : IsDominant (g.toNormalization ≫ g.fromNormalization) := by
      rw [Scheme.Hom.toNormalization_fromNormalization]; infer_instance
    exact IsDominant.of_comp g.toNormalization g.fromNormalization
  have : IsDominant f.fromNormalization := by
    have : IsDominant (f.toNormalization ≫ f.fromNormalization) := by
      rw [Scheme.Hom.toNormalization_fromNormalization]; infer_instance
    exact IsDominant.of_comp f.toNormalization f.fromNormalization
  have : Surjective g.fromNormalization :=
    surjective_of_isDominant_of_isClosed_range _ g.fromNormalization.isClosedMap.isClosed_range
  have hρs : Surjective f.fromNormalization :=
    surjective_of_isDominant_of_isClosed_range _ f.fromNormalization.isClosedMap.isClosed_range
  have hdim : topologicalKrullDim f.normalization = (Y.dim + 1 : ℕ) := by
    rw [← M.ar.dim_eq]
    refine le_antisymm (ProperCover.dim_le_of_residueDegree_pos f.fromNormalization
      (apply_genericPoint_of_isDominant f.fromNormalization) ?_)
      (PosBaseChange.dim_le_of_isClosedMap f.fromNormalization.isClosedMap hρs.surj)
    let := (f.fromNormalization.residueFieldMap (genericPoint f.normalization)).hom.toAlgebra
    have : Module.Finite (M.X.residueField (f.fromNormalization (genericPoint f.normalization)))
        (f.normalization.residueField (genericPoint f.normalization)) :=
      residueFieldMap_finite_of_locallyQuasiFinite f.fromNormalization _
    exact Module.finrank_pos
  have hc : f ≫ M.p = (g ≫ Y.str) ≫ spMap (algebraMap (𝓞 F) F) := by
    simp only [hf, Category.assoc, M.pb.w]
  have hfl : Flat (f.fromNormalization ≫ M.p) := GlobalTheory.flat_fromNormalization_comp f F M.p (g ≫ Y.str) hc
  have hfZ : Flat (spMap (Int.castRingHom (𝓞 F))) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.mpr (inferInstance : Module.Flat ℤ (𝓞 F))
  have : GlobalTheory.IsNormalScheme f.normalization := GlobalTheory.IsNormalScheme.normalization_of_isIntegral f
  obtain ⟨hη, ψ, hψ⟩ := GlobalTheory.T.generic_point_morphism_factorization Y.X K g rfl
  let V : Cover Y :=
    { X := f.normalization
      p := f.fromNormalization ≫ M.p
      ar := ⟨M.ar.isDomain, M.ar.finite, inferInstance,
        GlobalTheory.isProjOver_comp_of_finite _ _ _ _ _ hfin M.ar.isProjOver, inferInstance, hdim⟩
      normal := GlobalTheory.IsNormalScheme.pred _
      G := g.normalization
      j := GlobalTheory.normalizationMap g f (𝟙 _) M.j (by simp [hf])
      π := g.fromNormalization
      pb := hb.paste_vert M.pb
      φ := SmallSec.fnMap g.fromNormalization hη
      φ_spec := by
        change _ = Spec.map (Y.X.presheaf.stalkSpecializes hη ≫ g.fromNormalization.stalkMap _) ≫ _
        rw [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
          Scheme.SpecMap_stalkMap_fromSpecStalk] }
  exact ⟨V, f.fromNormalization, ψ, hb.w, hψ⟩

end GlobalTheory.Mean4O.NormCover
end
end

section
open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.Mean4 GlobalTheory.Mean4O
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cover_function_field_embedding : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (M : TrueGeo.Model Y) (K : Type) [Field K] [Algebra Y.Fn K] [FiniteDimensional Y.Fn K], ∃ (V : Cover Y) (ρ : V.X ⟶ M.X) (ψ : K →+* V.G.functionField), V.j ≫ ρ = V.π ≫ M.j ∧ ψ.comp (algebraMap Y.Fn K) = V.φ := by
  first | exact @GlobalTheory.Mean4O.NormCover.exists_cover | exact GlobalTheory.Mean4O.NormCover.exists_cover | (intros; apply GlobalTheory.Mean4O.NormCover.exists_cover <;> assumption)
end

section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.ArInt GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.Mean4O GlobalTheory.LineNorm GlobalTheory.CoverNorm GlobalTheory.VertForm GlobalTheory.HtGen
open Formalism.MainNotions.DIV.Cons (intO)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HtGen.SplitCover

variable {F : Type} [Field F] [NumberField F] {Y : Var F}

theorem map_genericPoint {V' V : Cover Y} (g : V'.G ⟶ V.G) (h : g ≫ V.π = V'.π) :
    g (genericPoint V'.G) = genericPoint V.G := by
  have key (W : Cover Y) : W.π (genericPoint W.G) = genericPoint Y.X := by
    have := (genericPoint_spec W.G).image W.π.continuous
    rw [Set.image_univ, W.π.surjective.range_eq, closure_univ] at this
    exact this.eq (genericPoint_spec _)
  obtain ⟨U, hU, e⟩ := isDiscrete_iff_forall_mem_exists_isOpen.mp (V.π.isDiscrete_preimage_singleton (genericPoint Y.X))
    (g (genericPoint V'.G)) (by rw [Set.mem_preimage, ← Scheme.Hom.comp_apply, h, key]; rfl)
  have h₁ : g (genericPoint V'.G) ∈ U := (e.ge rfl).1
  exact (e.le ⟨(genericPoint_specializes _).mem_open hU h₁, key V⟩).symm

theorem asIdeal_p_j (V : Cover Y) (y : V.G) : (V.p (V.j y)).asIdeal = ⊥ := by
  rw [← Scheme.Hom.comp_apply, V.pb.w, Scheme.Hom.comp_apply]
  change Ideal.comap (algebraMap (𝓞 F) F) ((V.π ≫ Y.str) y).asIdeal = ⊥
  have := ((V.π ≫ Y.str) y).isPrime
  rw [Ideal.eq_bot_of_prime ((V.π ≫ Y.str) y).asIdeal]
  exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective (𝓞 F) F)

theorem mem_range_j (V : Cover Y) {x : V.X} (hx : (V.p x).asIdeal = ⊥) : x ∈ Set.range V.j := by
  rw [← V.pb.isoPullback_hom_fst, Scheme.Hom.comp_base, TopCat.coe_comp,
    Set.range_comp, V.pb.isoPullback.hom.surjective.range_eq, Set.image_univ,
    Scheme.Pullback.range_fst]
  refine ⟨IsLocalRing.closedPoint F, PrimeSpectrum.ext (Eq.trans ?_ hx.symm)⟩
  change Ideal.comap (algebraMap (𝓞 F) F) (IsLocalRing.maximalIdeal F) = ⊥
  rw [IsLocalRing.maximalIdeal_eq_bot]
  exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective (𝓞 F) F)

theorem j_gen_specializes (V : Cover Y) : V.j (genericPoint V.G) ⤳ genericPoint V.X := by
  have h0 : (V.p (genericPoint V.X)).asIdeal = ⊥ :=
    eq_bot_iff.2 (((PrimeSpectrum.asIdeal_le_asIdeal _ _).2 ((PrimeSpectrum.le_iff_specializes _ _).2
      ((genericPoint_specializes (V.j (genericPoint V.G))).map V.p.continuous))).trans
        (asIdeal_p_j V _).le)
  obtain ⟨y, hy⟩ := mem_range_j V h0
  exact hy ▸ (genericPoint_specializes y).map V.j.continuous

theorem isPreimmersion_j (V : Cover Y) : IsPreimmersion V.j :=
  have := IsPreimmersion.of_isLocalization (R := 𝓞 F) (S := F) (nonZeroDivisors (𝓞 F))
  MorphismProperty.of_isPullback V.pb.flip this

theorem spMap_fnMap {Z W : Scheme.{0}} [IsIntegral Z] [IsIntegral W] (j : W ⟶ Z)
    (hη : j (genericPoint W) ⤳ genericPoint Z) :
    spMap (SmallSec.fnMap j hη) ≫ Z.fromSpecStalk (genericPoint Z) = W.fromSpecStalk (genericPoint W) ≫ j := by
  have e : spMap (SmallSec.fnMap j hη) =
      Spec.map (Z.presheaf.stalkSpecializes hη ≫ j.stalkMap (genericPoint W)) := rfl
  rw [e, Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
    Scheme.SpecMap_stalkMap_fromSpecStalk]

theorem spMap_spMap {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R') (g : R' →+* R'') :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp only [spMap, ← Spec.map_comp]; rfl

theorem splitK_of_splitTors {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {X : Scheme.{0}} (t : SAB H X) {K L : Type} [Field K] [Field L] (x : Sp K ⟶ X) (κ : K →+* L) (ξ : Sp L ⟶ X)
    (hξ : ξ = spMap κ ≫ x) {q : ℕ} (h : SplitTors t x q) : SplitK t ξ q := by
  subst hξ
  intro Ω _ io
  let ε := (FractionRing.algEquiv K K).toRingEquiv
  have e : ((io.comp κ).comp ε.toRingHom).comp (algebraMap K (FractionRing K)) = io.comp κ :=
    RingHom.ext fun a => congrArg (io.comp κ) ((FractionRing.algEquiv K K).commutes a)
  have h' := h Ω ((io.comp κ).comp ε.toRingHom)
  rw [e] at h'
  rw [← Category.assoc, spMap_spMap]
  intro w hw
  obtain ⟨w₀, h₀⟩ := h' w hw
  refine ⟨spMap (κ.comp ε.toRingHom) ≫ w₀, ?_⟩
  rw [← h₀, ← Category.assoc, spMap_spMap]

theorem exists_cover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) [IsLocallyNoetherian X] (t : SAB H X) (F : Type) [Field F] [NumberField F] (Y : Var F) (M : TrueGeo.Model Y) (ρ' : M.X ⟶ X) (V₀ : Cover Y) (q : ℕ), q ≠ 0 → ∃ (V : Cover Y) (a : V.X ⟶ V₀.X) (g : V.G ⟶ V₀.G) (ρ'' : V.X ⟶ X), a ≫ V₀.p = V.p ∧ V.j ≫ a = g ≫ V₀.j ∧ g ≫ V₀.π = V.π ∧ g (genericPoint V.G) = genericPoint V₀.G ∧ V.j ≫ ρ'' = V.π ≫ M.j ≫ ρ' ∧ CharZero V.X.functionField ∧ (∃ ζ : V.X.functionField, IsPrimitiveRoot ζ q) ∧ SplitK t (K := V.X.functionField) (V.X.fromSpecStalk (genericPoint V.X) ≫ ρ'') q := by
  intro E _ _ _ H X _ t F _ _ Y M ρ' V₀ q hq
  haveI : CharZero Y.Fn := charZero_of_injective_algebraMap (algebraMap F Y.Fn).injective
  let x : Sp Y.Fn ⟶ X := Y.X.fromSpecStalk (genericPoint Y.X) ≫ M.j ≫ ρ'
  obtain ⟨K, i1, i2, i3, hfin, hinj, -, ⟨ζ, hζ⟩, hs⟩ := GlobalTheory.T.exists_finite_extension_splitting_torsion E H X t Y.Fn x q hq
  have hK : IsField K := by
    have : Algebra.IsIntegral Y.Fn K := Algebra.IsIntegral.of_finite _ _
    exact (Algebra.IsIntegral.isField_iff_isField hinj).1 (Field.toIsField _)
  letI : Field K := hK.toField
  obtain ⟨V₁, ρ₁, ψ, hρ₁, hψ⟩ := GlobalTheory.T.exists_cover_function_field_embedding F Y M K
  obtain ⟨V, π₀, π₁, hπ₀, -, ⟨g₀, e₀, f₀⟩, ⟨g₁, e₁, f₁⟩⟩ := GlobalTheory.T.common_refinement_covers F Y V₀ V₁
  haveI := isPreimmersion_j V
  have hη := j_gen_specializes V
  have hg₁ : g₁ (genericPoint V.G) ⤳ genericPoint V₁.G := specializes_of_eq (map_genericPoint g₁ f₁)
  let r : V.X.functionField ≃+* V.G.functionField := RingEquiv.ofBijective (SmallSec.fnMap V.j hη)
    ⟨(SmallSec.fnMap V.j hη).injective, SmallSec.fnMap_surjective V.j hη⟩
  let κ : K →+* V.X.functionField := r.symm.toRingHom.comp ((SmallSec.fnMap g₁ hg₁).comp ψ)
  have hj : V.j ≫ π₁ ≫ ρ₁ ≫ ρ' = V.π ≫ M.j ≫ ρ' := by
    rw [← reassoc_of% e₁, reassoc_of% hρ₁, reassoc_of% f₁]
  have hr : V.X.fromSpecStalk (genericPoint V.X) =
      spMap r.symm.toRingHom ≫ V.G.fromSpecStalk (genericPoint V.G) ≫ V.j := by
    rw [← spMap_fnMap V.j hη, ← Category.assoc, spMap_spMap]
    have : r.symm.toRingHom.comp (SmallSec.fnMap V.j hη) = RingHom.id _ := RingHom.ext fun a => r.symm_apply_apply a
    rw [this]
    exact ((congrArg (· ≫ _) (Spec.map_id _)).trans (Category.id_comp _)).symm
  refine ⟨V, π₀, g₀, π₁ ≫ ρ₁ ≫ ρ', hπ₀, e₀.symm, f₀, map_genericPoint g₀ f₀, hj,
    (κ.comp (algebraMap Y.Fn K)).charZero_iff (κ.comp (algebraMap Y.Fn K)).injective |>.1 inferInstance,
    ⟨κ ζ, hζ.map_of_injective κ.injective⟩, splitK_of_splitTors t _ κ _ ?_ hs⟩
  have h₁ := spMap_fnMap g₁ hg₁
  have h₂ := V₁.φ_spec
  have h₃ : spMap κ ≫ spMap (algebraMap Y.Fn K) =
      spMap r.symm.toRingHom ≫ spMap (SmallSec.fnMap g₁ hg₁) ≫ spMap V₁.φ := by
    rw [← hψ, spMap_spMap, spMap_spMap, spMap_spMap]
  rw [hr, Category.assoc, Category.assoc, hj, ← f₁, reassoc_of% h₃]
  congr 1
  rw [Category.assoc, ← reassoc_of% h₁, reassoc_of% h₂]

end GlobalTheory.HtGen.SplitCover
end
end

section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.ArInt GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.Mean4O GlobalTheory.LineNorm GlobalTheory.CoverNorm GlobalTheory.VertForm GlobalTheory.HtGen
open Formalism.MainNotions.DIV.Cons (intO)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cover_refinement_exists : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) [IsLocallyNoetherian X] (t : SAB H X) (F : Type) [Field F] [NumberField F] (Y : Var F) (M : TrueGeo.Model Y) (ρ' : M.X ⟶ X) (V₀ : Cover Y) (q : ℕ), q ≠ 0 → ∃ (V : Cover Y) (a : V.X ⟶ V₀.X) (g : V.G ⟶ V₀.G) (ρ'' : V.X ⟶ X), a ≫ V₀.p = V.p ∧ V.j ≫ a = g ≫ V₀.j ∧ g ≫ V₀.π = V.π ∧ g (genericPoint V.G) = genericPoint V₀.G ∧ V.j ≫ ρ'' = V.π ≫ M.j ≫ ρ' ∧ CharZero V.X.functionField ∧ (∃ ζ : V.X.functionField, IsPrimitiveRoot ζ q) ∧ SplitK t (K := V.X.functionField) (V.X.fromSpecStalk (genericPoint V.X) ≫ ρ'') q := by
  first | exact @GlobalTheory.HtGen.SplitCover.exists_cover | exact GlobalTheory.HtGen.SplitCover.exists_cover | (intros; apply GlobalTheory.HtGen.SplitCover.exists_cover <;> assumption)
end

section
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.ArInt GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.Mean4O GlobalTheory.LineNorm GlobalTheory.CoverNorm GlobalTheory.VertForm GlobalTheory.HtGen
open Formalism.MainNotions.DIV.Cons (intO)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ShFam.Pad

theorem w_mul_exp_cmp_iff : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (ε : GlobalTheory.TrueGeo.Ext v) [Fact (resP v).Prime] (k : ℕ) (gn : Fin k → ℝ), (∀ l, 0 < gn l) → ∀ b : AlgebraicClosure F, (ε.w b * Real.exp (-∑ l, (-Real.log (ε.w (resP v)) / Real.log (resP v)) * Real.log (gn l)) ≤ 1 ↔ ‖ioOf (resP v) ε b‖ ≤ ∏ l, gn l) ∧ (ε.w b * Real.exp (-∑ l, (-Real.log (ε.w (resP v)) / Real.log (resP v)) * Real.log (gn l)) = 1 ↔ ‖ioOf (resP v) ε b‖ = ∏ l, gn l) ∧ (ε.w b * Real.exp (-∑ l, (-Real.log (ε.w (resP v)) / Real.log (resP v)) * Real.log (gn l)) < 1 ↔ ‖ioOf (resP v) ε b‖ < ∏ l, gn l) := by
  intro F _ _ v ε _ k gn hgn b
  have hpr : (resP v).Prime := Fact.out
  have hio := ioOf_le_one_iff (resP v) (residueCharacteristic_mem v) ε
  have hlog := log_w_eq (resP v) ε (ioOf (resP v) ε) hio
  have hwp : ε.w ((resP v : ℕ) : AlgebraicClosure F) < 1 := by
    have h1 : ((resP v : ℕ) : AlgebraicClosure F) =
        algebraMap F _ (algebraMap (𝓞 F) F ((resP v : ℕ) : 𝓞 F)) := by simp
    rw [h1, ε.w_alg]
    exact (v.adicAbv_coe_lt_one_iff (K := F) (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v) _).2 (residueCharacteristic_mem v)
  have hwp0 : 0 < ε.w ((resP v : ℕ) : AlgebraicClosure F) :=
    ε.w.pos (Nat.cast_ne_zero.2 hpr.ne_zero)
  have hlp : 0 < Real.log ((resP v : ℕ) : ℝ) := Real.log_pos (by exact_mod_cast hpr.one_lt)
  set c := -Real.log (ε.w ((resP v : ℕ) : AlgebraicClosure F)) / Real.log ((resP v : ℕ) : ℝ) with hc
  have hc0 : 0 < c := div_pos (neg_pos.2 (Real.log_neg hwp0 hwp)) hlp
  have hwb : ε.w b = ‖ioOf (resP v) ε b‖ ^ c := by
    rcases eq_or_ne b 0 with rfl | hb
    · simp [Real.zero_rpow hc0.ne']
    · have hb' : 0 < ‖ioOf (resP v) ε b‖ := norm_pos_iff.2 ((map_ne_zero _).2 hb)
      rw [← Real.exp_log (ε.w.pos hb), hlog b, Real.rpow_def_of_pos hb', mul_comm]
  have hν : 0 < ∏ l, gn l := Finset.prod_pos fun l _ => hgn l
  have hexp : Real.exp (-∑ l, c * Real.log (gn l)) = (∏ l, gn l) ^ (-c) := by
    rw [Real.rpow_def_of_pos hν, ← Finset.mul_sum, Real.log_prod (fun l _ => (hgn l).ne')]
    ring_nf
  have hkey : ε.w b * Real.exp (-∑ l, c * Real.log (gn l)) = (‖ioOf (resP v) ε b‖ / ∏ l, gn l) ^ c := by
    rw [hexp, hwb, Real.div_rpow (norm_nonneg _) hν.le, Real.rpow_neg hν.le, div_eq_mul_inv]
  rw [hkey]
  have hx : 0 ≤ ‖ioOf (resP v) ε b‖ / ∏ l, gn l := div_nonneg (norm_nonneg _) hν.le
  have hle : (‖ioOf (resP v) ε b‖ / ∏ l, gn l) ^ c ≤ 1 ↔ ‖ioOf (resP v) ε b‖ ≤ ∏ l, gn l := by
    rw [← Real.one_rpow c, Real.rpow_le_rpow_iff hx zero_le_one hc0, div_le_one hν]
  have hge : 1 ≤ (‖ioOf (resP v) ε b‖ / ∏ l, gn l) ^ c ↔ ∏ l, gn l ≤ ‖ioOf (resP v) ε b‖ := by
    rw [← Real.one_rpow c, Real.rpow_le_rpow_iff zero_le_one hx hc0, one_le_div hν]
  refine ⟨hle, ?_, ?_⟩
  · rw [le_antisymm_iff, hle, hge, ← le_antisymm_iff]
  · rw [← Real.one_rpow c, Real.rpow_lt_rpow_iff hx zero_le_one hc0, div_lt_one hν]

end GlobalTheory.ShFam.Pad
end

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.ArInt GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.Mean4O GlobalTheory.LineNorm GlobalTheory.CoverNorm GlobalTheory.VertForm GlobalTheory.HtGen
open Formalism.MainNotions.DIV.Cons (intO)
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_unit_absolute_value_criterion : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (ε : GlobalTheory.TrueGeo.Ext v) [Fact (resP v).Prime] (k : ℕ) (gn : Fin k → ℝ), (∀ l, 0 < gn l) → ∀ b : AlgebraicClosure F, (ε.w b * Real.exp (-∑ l, (-Real.log (ε.w (resP v)) / Real.log (resP v)) * Real.log (gn l)) ≤ 1 ↔ ‖ioOf (resP v) ε b‖ ≤ ∏ l, gn l) ∧ (ε.w b * Real.exp (-∑ l, (-Real.log (ε.w (resP v)) / Real.log (resP v)) * Real.log (gn l)) = 1 ↔ ‖ioOf (resP v) ε b‖ = ∏ l, gn l) ∧ (ε.w b * Real.exp (-∑ l, (-Real.log (ε.w (resP v)) / Real.log (resP v)) * Real.log (gn l)) < 1 ↔ ‖ioOf (resP v) ε b‖ < ∏ l, gn l) := by
  atlas_forward_decl GlobalTheory.ShFam.Pad.w_mul_exp_cmp_iff
end

section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.ArInt GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.Mean4O GlobalTheory.LineNorm GlobalTheory.CoverNorm GlobalTheory.VertForm GlobalTheory.HtGen
open Formalism.MainNotions.DIV.Cons (intO)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HtGen.CoverChart

theorem pairDet_tri {R J : Type} [CommRing R] {m g k : ℕ} (h : J → Fin g → R) (a b : Fin m → Fin g → R)
    (T : Fin m → Fin m → R) (hT : ∀ i l, i < l → T i l = 0) (hb : ∀ i, b i = ∑ l, T i l • a l) (hk : k ≤ m)
    (σ : Fin k → J) :
    pairDet h b hk σ = (∏ l : Fin k, T (Fin.castLE hk l) (Fin.castLE hk l)) * pairDet h a hk σ := by
  have e : ∀ c : Fin m → Fin g → R, pairDet h c hk σ = minor (fun l r => ∑ i, h (σ r) i * c l i) hk id := fun c =>
    (Matrix.det_transpose _).symm
  rw [e, e]
  refine Chart.minor_tri _ _ T hT (fun i => funext fun r => ?_) hk id
  simp only [hb, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ => by ring

theorem sp_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := (Spec.map_comp _ _)

variable {F : Type} [Field F] [NumberField F] {Y : Var F} (V : Cover Y)

theorem gen_eq' {G : Scheme.{0}} [IsIntegral G] (z : G) :
    spMap (algebraMap (G.presheaf.stalk z) G.functionField) ≫ G.fromSpecStalk z = G.fromSpecStalk (genericPoint G) :=
  Scheme.SpecMap_stalkSpecializes_fromSpecStalk (genericPoint_specializes z)

theorem stalk_eq (z : V.G) :
    spMap (V.π.stalkMap z).hom ≫ Y.X.fromSpecStalk (V.π z) = V.G.fromSpecStalk z ≫ V.π :=
  Scheme.SpecMap_stalkMap_fromSpecStalk V.π

theorem alg_comp_stalkMap (z : V.G) :
    (algebraMap (V.G.presheaf.stalk z) V.G.functionField).comp (V.π.stalkMap z).hom =
      V.φ.comp (algebraMap (Y.X.presheaf.stalk (V.π z)) Y.X.functionField) := by
  have h : spMap ((algebraMap (V.G.presheaf.stalk z) V.G.functionField).comp (V.π.stalkMap z).hom) ≫
        Y.X.fromSpecStalk (V.π z) =
      spMap (V.φ.comp (algebraMap (Y.X.presheaf.stalk (V.π z)) Y.X.functionField)) ≫ Y.X.fromSpecStalk (V.π z) := by
    rw [sp_comp, sp_comp, Category.assoc, Category.assoc, stalk_eq, gen_eq', ← Category.assoc, gen_eq', V.φ_spec]
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective ((cancel_mono _).1 h))

end GlobalTheory.HtGen.CoverChart

open GlobalTheory.HtGen.CoverChart GlobalTheory.LineNorm.Chart GlobalTheory.LieMet in

theorem GlobalTheory.HtGen.CoverChart.pairDet_div_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (F : Type) [Field F] [NumberField F] (Y : Var F) (V : Cover Y) (ρ' : V.X ⟶ X) (ρ : Y.X ⟶ X), V.j ≫ ρ' = V.π ≫ ρ → ∀ (m : ℕ) (u₀ : Fin m → (Sp (DualNumber Y.Fn) ⟶ t.G.left)) (f : ∀ y : Y.X, Fin m → (Sp (DualNumber (Y.X.presheaf.stalk y)) ⟶ t.G.left)) (d : Y.X → Fin m → Y.Fnˣ), IsFlagFrame t ρ u₀ f d → ∀ (U : V.X.Opens) (hU : IsAffineOpen U) (g : ℕ) (e : Fin g → (Sp (DualNumber Γ(V.X, U)) ⟶ t.G.left)), IsTanBasis t (hU.fromSpec ≫ ρ') e → ∀ (J : Type) (h : J → Fin g → Γ(V.X, U)) (k : ℕ) (hk : k ≤ m), ∃ s : (Fin k → J) → V.G.functionField, ∀ z : V.G, V.j z ∈ U → ∃ (α : Γ(V.X, U) →+* V.G.presheaf.stalk z) (a : Fin m → Fin g → V.G.presheaf.stalk z), spMap α ≫ hU.fromSpec = V.G.fromSpecStalk z ≫ V.j ∧ (∀ l, IsCombAtG t (spMap α ≫ hU.fromSpec ≫ ρ') (fun i => spMap (dualMap α) ≫ e i) (a l) (spMap (dualMap (V.π.stalkMap z).hom) ≫ f (V.π z) l)) ∧ ∀ σ, s σ / V.φ ((∏ l : Fin k, d (V.π z) (Fin.castLE hk l) : Y.Fnˣ) : Y.Fn) = algebraMap (V.G.presheaf.stalk z) V.G.functionField (pairDet (fun j i => α (h j i)) a hk σ) := by
  intro E _ _ _ H X t F _ _ Y V ρ' ρ hρ m u₀ f d hf U hU g e he J h k hk
  by_cases hgen : V.j (genericPoint V.G) ∈ U
  swap
  · exact ⟨fun _ => 0, fun z hz => absurd
      (((genericPoint_specializes z).map V.j.continuous).mem_open U.isOpen hz) hgen⟩
  choose α hα using fun (z : V.G) (hz : V.j z ∈ U) => exists_stalkHom hU V.j z hz
  have hα' : ∀ z hz, spMap (α z hz) ≫ hU.fromSpec ≫ ρ' = V.G.fromSpecStalk z ≫ V.π ≫ ρ := fun z hz => by
    rw [← Category.assoc, hα, Category.assoc, hρ]
  let ι₀ : Γ(V.X, U) →+* V.G.functionField := α _ hgen
  have hι : spMap ι₀ ≫ hU.fromSpec ≫ ρ' = spMap V.φ ≫ GlobalTheory.ShFam.genericPt Y ≫ ρ :=
    (hα' _ hgen).trans (by rw [← Category.assoc, V.φ_spec, Category.assoc]; rfl)
  have hαι : ∀ z hz, (algebraMap (V.G.presheaf.stalk z) V.G.functionField).comp (α z hz) = ι₀ := fun z hz =>
    ringHom_ext hU (by
      rw [sp_comp, Category.assoc, hα, ← Category.assoc, gen_eq']
      exact (hα _ hgen).symm)
  have ha : ∀ z (hz : V.j z ∈ U) l, ∃ a, IsCombAtG t (spMap (α z hz) ≫ hU.fromSpec ≫ ρ')
      (fun i => spMap (dualMap (α z hz)) ≫ e i) a (spMap (dualMap (V.π.stalkMap z).hom) ≫ f (V.π z) l) := fun z hz l =>
    (he.2 _ (α z hz) _ (isTan_map _ (by
      rw [hα', ← Category.assoc, ← Category.assoc, ← stalk_eq]; rfl) (hf.tan (V.π z) l))).exists
  choose a ha using ha
  have key : ∀ z (hz : V.j z ∈ U) i, ∃ cf : Fin m → Y.Fn, cf i = d (V.π z) i ∧ (∀ k, i < k → cf k = 0) ∧
      IsCombAtG t (spMap ι₀ ≫ hU.fromSpec ≫ ρ') (fun i => spMap (dualMap ι₀) ≫ e i)
        (∑ l, V.φ (cf l) • fun j => algebraMap (V.G.presheaf.stalk z) V.G.functionField (a z hz l j))
        (spMap (dualMap V.φ) ≫ u₀ i) := by
    intro z hz i
    obtain ⟨cf, h1, h2, h3⟩ := hf.tri (V.π z) i
    have h4 := GlobalTheory.LatDRFree.comb_map t V.φ h3
    refine ⟨cf, h1, h2, comb_comb (fun j => isTan_map _ rfl (he.1 j)) (fun l => ?_) (hι ▸ h4)⟩
    have := coord_map _ (algebraMap (V.G.presheaf.stalk z) V.G.functionField) (ha z hz l)
    rw [hαι, dual_comp, alg_comp_stalkMap] at this
    rw [dual_comp]
    exact this
  choose T hT1 hT2 hT3 using key
  have hA₀ : ∀ i, ∃ b, IsCombAtG t (spMap ι₀ ≫ hU.fromSpec ≫ ρ') (fun i => spMap (dualMap ι₀) ≫ e i) b
      (spMap (dualMap V.φ) ≫ u₀ i) := fun i => ⟨_, hT3 _ hgen i⟩
  choose A₀ hA₀ using hA₀
  have hA : ∀ z hz i, A₀ i = ∑ l, V.φ (T z hz i l) • fun j => algebraMap _ V.G.functionField (a z hz l j) := fun z hz i =>
    (he.2 _ ι₀ _ (comb_tan (fun j => isTan_map _ rfl (he.1 j)) (hT3 z hz i))).unique (hA₀ i) (hT3 z hz i)
  refine ⟨fun σ => pairDet (fun j i => ι₀ (h j i)) A₀ hk σ, fun z hz => ⟨α z hz, a z hz, hα z hz, ha z hz, fun σ => ?_⟩⟩
  have hne : V.φ ((∏ l : Fin k, d (V.π z) (Fin.castLE hk l) : Y.Fnˣ) : Y.Fn) ≠ 0 :=
    (_root_.map_ne_zero V.φ).2 (Units.ne_zero _)
  beta_reduce
  rw [div_eq_iff hne, map_pairDet, pairDet_tri _ _ A₀ (fun i l => V.φ (T z hz i l))
    (fun i l hl => by simp only [hT2 z hz i l hl, map_zero]) (hA z hz), mul_comm, Units.coe_prod, map_prod, ← hαι z hz]
  simp only [hT1]
  rfl
end

section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.ArInt GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.Mean4O GlobalTheory.LineNorm GlobalTheory.CoverNorm GlobalTheory.VertForm GlobalTheory.HtGen
open Formalism.MainNotions.DIV.Cons (intO)
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_frame_cover_tangent_compat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (F : Type) [Field F] [NumberField F] (Y : Var F) (V : Cover Y) (ρ' : V.X ⟶ X) (ρ : Y.X ⟶ X), V.j ≫ ρ' = V.π ≫ ρ → ∀ (m : ℕ) (u₀ : Fin m → (Sp (DualNumber Y.Fn) ⟶ t.G.left)) (f : ∀ y : Y.X, Fin m → (Sp (DualNumber (Y.X.presheaf.stalk y)) ⟶ t.G.left)) (d : Y.X → Fin m → Y.Fnˣ), IsFlagFrame t ρ u₀ f d → ∀ (U : V.X.Opens) (hU : IsAffineOpen U) (g : ℕ) (e : Fin g → (Sp (DualNumber Γ(V.X, U)) ⟶ t.G.left)), IsTanBasis t (hU.fromSpec ≫ ρ') e → ∀ (J : Type) (h : J → Fin g → Γ(V.X, U)) (k : ℕ) (hk : k ≤ m), ∃ s : (Fin k → J) → V.G.functionField, ∀ z : V.G, V.j z ∈ U → ∃ (α : Γ(V.X, U) →+* V.G.presheaf.stalk z) (a : Fin m → Fin g → V.G.presheaf.stalk z), spMap α ≫ hU.fromSpec = V.G.fromSpecStalk z ≫ V.j ∧ (∀ l, IsCombAtG t (spMap α ≫ hU.fromSpec ≫ ρ') (fun i => spMap (dualMap α) ≫ e i) (a l) (spMap (dualMap (V.π.stalkMap z).hom) ≫ f (V.π z) l)) ∧ ∀ σ, s σ / V.φ ((∏ l : Fin k, d (V.π z) (Fin.castLE hk l) : Y.Fnˣ) : Y.Fn) = algebraMap (V.G.presheaf.stalk z) V.G.functionField (pairDet (fun j i => α (h j i)) a hk σ) := by
  first | exact @GlobalTheory.HtGen.CoverChart.pairDet_div_eq | exact GlobalTheory.HtGen.CoverChart.pairDet_div_eq | (intros; apply GlobalTheory.HtGen.CoverChart.pairDet_div_eq <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.ArInt GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.Mean4O GlobalTheory.LineNorm GlobalTheory.CoverNorm GlobalTheory.VertForm GlobalTheory.HtGen
open Formalism.MainNotions.DIV.Cons (intO)
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.HtGen.FlagPoint

open GlobalTheory.LineNorm.Chart GlobalTheory.LieMet

theorem residueCharacteristic_eq {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {q : ℕ} (hq : q.Prime)
    (hv : (q : 𝓞 F) ∈ v.asIdeal) : resP v = q := by
  refine (Nat.prime_dvd_prime_iff_eq (residueCharacteristic_prime v) hq).1 (ringChar.dvd ?_)
  rw [← map_natCast (Ideal.Quotient.mk v.asIdeal), Ideal.Quotient.eq_zero_iff_mem]
  exact hv

theorem chart {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
    {t : SAB H X} {S G : Scheme.{0}} (j : G ⟶ S) (ρ' : S ⟶ X) {K : Type} [Field K] (O : ValuationSubring K)
    {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C] (io : K →+* C) (ioO : O →+* intO C)
    (hio : (intO C).subtype.comp ioO = io.comp O.subtype) (z : Sp K ⟶ G) (yt : Sp O ⟶ S)
    (hyt : spMap O.subtype ≫ yt = z ≫ j) {U : S.Opens} (hU : IsAffineOpen U) (hin : ⊤ ≤ yt ⁻¹ᵁ U) {g m : ℕ}
    (e : Fin g → (Sp (DualNumber Γ(S, U)) ⟶ t.G.left)) (α : Γ(S, U) →+* G.presheaf.stalk (below z))
    (hα : spMap α ≫ hU.fromSpec = G.fromSpecStalk (below z) ≫ j) (a : Fin m → Fin g → G.presheaf.stalk (below z))
    (w : Fin m → (Sp (DualNumber (G.presheaf.stalk (below z))) ⟶ t.G.left))
    (ha : ∀ l, IsCombAtG t (spMap α ≫ hU.fromSpec ≫ ρ') (fun i => spMap (dualMap α) ≫ e i) (a l) (w l))
    (ψ : G.presheaf.stalk (below z) →+* C) (hψ : ψ = io.comp (Scheme.stalkClosedPointTo z).hom) :
    ∃ β : Γ(S, U) →+* intO C, spMap β ≫ hU.fromSpec = spMap ioO ≫ yt ∧ (∀ r, ψ (α r) = β r) ∧
      ∀ l, IsCombAtG t (spMap (intO C).subtype ≫ (spMap ioO ≫ yt) ≫ ρ')
        (fun i => spMap (dualMap (intO C).subtype) ≫ spMap (dualMap β) ≫ e i) (fun i => ψ (a l i))
        (spMap (dualMap ψ) ≫ w l) := by
  obtain ⟨β, hβ⟩ := exists_ringHom hU yt hin
  obtain ⟨σ, hσ₀⟩ : ∃ σ : G.presheaf.stalk (below z) →+* K, σ = (Scheme.stalkClosedPointTo z).hom := ⟨_, rfl⟩
  have hσ : σ.comp α = O.subtype.comp β := ringHom_ext hU (by
    rw [← spMap_comp', ← spMap_comp', Category.assoc, Category.assoc, hα, hβ, hyt, ← Category.assoc, hσ₀]
    exact congrArg (· ≫ j) (Scheme.Spec_stalkClosedPointTo_fromSpecStalk z))
  have h1 : spMap (ioO.comp β) ≫ hU.fromSpec = spMap ioO ≫ yt := by
    rw [← spMap_comp', Category.assoc, hβ]
  have h2 : ψ.comp α = (intO C).subtype.comp (ioO.comp β) := by
    rw [hψ, ← hσ₀, RingHom.comp_assoc, hσ, ← RingHom.comp_assoc, ← hio, RingHom.comp_assoc]
  refine ⟨ioO.comp β, h1, fun r => congrArg (fun φ => φ r) h2, fun l => ?_⟩
  have := coord_map α ψ (ha l)
  rw [h2, ← spMap_comp', Category.assoc, ← Category.assoc (spMap (ioO.comp β)), h1] at this
  simpa only [dual_comp] using this

theorem pairDet_values : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H
    : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) [IsLocallyNoetherian
    X] (t : SAB H X), X.IsSeparated → ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V
    : Cover Y) (ρ' : V.X ⟶ X) (ρ : Y.X ⟶ X), V.j ≫ ρ' = V.π ≫ ρ → ∀ (q : ℕ) [Fact q.Prime] (m
    : ℕ) (f : ∀ y : Y.X, Fin m → (Sp (DualNumber (Y.X.presheaf.stalk y)) ⟶ t.G.left)) (d
    : Y.X → Fin m → Y.Fnˣ), (∀ y l, IsTanAtG t (GlobalTheory.ShFam.stalkPt Y y ≫ ρ) (f y
    l)) → (∀ y (K : Type) [Field K] (ψ : Y.X.presheaf.stalk y →+* K), IsIndep t (spMap ψ ≫
    GlobalTheory.ShFam.stalkPt Y y ≫ ρ) (fun l => spMap (dualMap ψ) ≫ f y l)) → ∀ (k : ℕ) (hk
    : k ≤ m) (N : ℕ) (c : Fin N → ∀ y : Sp ↥(intO ℂ_[q]) ⟶ V.X, TorsChar t (y ≫ ρ') (q ^
    2)), (∀ y (c' : TorsChar t (y ≫ ρ') (q ^ 2)), ∃ j, Agree c' (c j y)) → ∀ (U U' : V.X.Opens) (hU
    : IsAffineOpen U) (hU' : IsAffineOpen U') (g g' : ℕ) (e : Fin g → (Sp (DualNumber Γ(V.X, U)) ⟶
    t.G.left)) (e' : Fin g' → (Sp (DualNumber Γ(V.X, U')) ⟶ t.G.left)) (h : Fin N → Fin g → Γ(V.X,
    U)) (h' : Fin N → Fin g' → Γ(V.X, U')), IsTanBasis t (hU.fromSpec ≫
    ρ') e → IsTanBasis t (hU'.fromSpec ≫ ρ') e' → (∀ (x : Γ(V.X, U) →+* ↥(intO ℂ_[q])) (y
    : Sp ↥(intO ℂ_[q]) ⟶ V.X), spMap x ≫ hU.fromSpec = y → ∀ j, DlogIs t q 2 (c j
    y) (fun i => spMap (dualMap x) ≫ e i) (fun i => x (h j i))) → (∀ (x : Γ(V.X, U') →+* ↥(intO
    ℂ_[q])) (y : Sp ↥(intO ℂ_[q]) ⟶ V.X), spMap x ≫ hU'.fromSpec = y → ∀ j, DlogIs t q 2 (c j
    y) (fun i => spMap (dualMap x) ≫ e' i) (fun i => x (h' j i))) → ∀ (s s' : (Fin k → Fin
    N) → V.G.functionField), (∀ z : V.G, V.j z ∈ U → ∃ (α : Γ(V.X, U) →+* V.G.presheaf.stalk z) (a
    : Fin m → Fin g → V.G.presheaf.stalk z), spMap α ≫ hU.fromSpec = V.G.fromSpecStalk z ≫ V.j ∧ (∀ l, IsCombAtG t (spMap
    α ≫ hU.fromSpec ≫ ρ') (fun i => spMap (dualMap α) ≫ e i) (a l) (spMap (dualMap (V.π.stalkMap
    z).hom) ≫ f (V.π z) l)) ∧ ∀ σ, s σ / V.φ ((∏ l : Fin k, d (V.π z) (Fin.castLE hk l) : Y.Fnˣ)
    : Y.Fn) = algebraMap (V.G.presheaf.stalk z) V.G.functionField (pairDet (fun j i => α (h j i)) a
    hk σ)) → (∀ z : V.G, V.j z ∈ U' → ∃ (α : Γ(V.X, U') →+* V.G.presheaf.stalk z) (a
    : Fin m → Fin g' → V.G.presheaf.stalk z), spMap α ≫ hU'.fromSpec = V.G.fromSpecStalk z ≫ V.j ∧ (∀ l, IsCombAtG t (spMap
    α ≫ hU'.fromSpec ≫ ρ') (fun i => spMap (dualMap α) ≫ e' i) (a l) (spMap (dualMap (V.π.stalkMap
    z).hom) ≫ f (V.π z) l)) ∧ ∀ σ, s' σ / V.φ ((∏ l : Fin k, d (V.π z) (Fin.castLE hk l) : Y.Fnˣ)
    : Y.Fn) = algebraMap (V.G.presheaf.stalk z) V.G.functionField (pairDet (fun j i => α (h' j i)) a
    hk σ)) → ∀ (v : HeightOneSpectrum (𝓞 F)) (ε : GlobalTheory.TrueGeo.Ext v) (y : AlgPt Y) (z
    : Sp (AlgebraicClosure F) ⟶ V.G) (yt : Sp ε.O ⟶ V.X), (q
    : 𝓞 F) ∈ v.asIdeal → z ≫ V.π = y.1 → spMap ε.O.subtype ≫ yt = z ≫ V.j → ⊤ ≤ yt ⁻¹ᵁ U → ⊤ ≤ yt ⁻¹ᵁ U' → ∀ [Fact
    (resP v).Prime], (∀ l, 0 < GlobalTheory.ShFam.Pad.grNorm t (spMap ((ioOf (resP v) ε).comp
    (Scheme.stalkClosedPointTo y.1).hom) ≫ GlobalTheory.ShFam.stalkPt Y (below y.1) ≫ ρ) (lat t
    (resP v) (spMap ((ioOf (resP v) ε).comp (Scheme.stalkClosedPointTo y.1).hom) ≫
    GlobalTheory.ShFam.stalkPt Y (below y.1) ≫ ρ) (decide (resP v = q))) (fun l => spMap (dualMap
    ((ioOf (resP v) ε).comp (Scheme.stalkClosedPointTo y.1).hom)) ≫ f (below y.1) l) (Fin.castLE hk
    l)) ∧ (∀ σ, ‖ioOf (resP v) ε (TrueGeo.valAt z (s σ / V.φ ((∏ l : Fin k, d (below
    y.1) (Fin.castLE hk l) : Y.Fnˣ) : Y.Fn)))‖ ≤ ∏ l : Fin k, GlobalTheory.ShFam.Pad.grNorm t (spMap
    ((ioOf (resP v) ε).comp (Scheme.stalkClosedPointTo y.1).hom) ≫ GlobalTheory.ShFam.stalkPt Y
    (below y.1) ≫ ρ) (lat t (resP v) (spMap ((ioOf (resP v) ε).comp (Scheme.stalkClosedPointTo
    y.1).hom) ≫ GlobalTheory.ShFam.stalkPt Y (below y.1) ≫ ρ) (decide (resP v =
    q))) (fun l => spMap (dualMap ((ioOf (resP v) ε).comp (Scheme.stalkClosedPointTo
    y.1).hom)) ≫ f (below y.1) l) (Fin.castLE hk l)) ∧ (∃ σ, ‖ioOf (resP v) ε (TrueGeo.valAt z (s σ
    / V.φ ((∏ l : Fin k, d (below y.1) (Fin.castLE hk l) : Y.Fnˣ)
    : Y.Fn)))‖ = ∏ l : Fin k, GlobalTheory.ShFam.Pad.grNorm t (spMap ((ioOf (resP v) ε).comp
    (Scheme.stalkClosedPointTo y.1).hom) ≫ GlobalTheory.ShFam.stalkPt Y (below y.1) ≫ ρ) (lat t
    (resP v) (spMap ((ioOf (resP v) ε).comp (Scheme.stalkClosedPointTo y.1).hom) ≫
    GlobalTheory.ShFam.stalkPt Y (below y.1) ≫ ρ) (decide (resP v = q))) (fun l => spMap (dualMap
    ((ioOf (resP v) ε).comp (Scheme.stalkClosedPointTo y.1).hom)) ≫ f (below y.1) l) (Fin.castLE hk
    l)) ∧ ∀ σ, ‖ioOf (resP v) ε (TrueGeo.valAt z ((s σ - s' σ) / V.φ ((∏ l : Fin k, d (below
    y.1) (Fin.castLE hk l) : Y.Fnˣ) : Y.Fn)))‖ < ∏ l : Fin k, GlobalTheory.ShFam.Pad.grNorm t (spMap
    ((ioOf (resP v) ε).comp (Scheme.stalkClosedPointTo y.1).hom) ≫ GlobalTheory.ShFam.stalkPt Y
    (below y.1) ≫ ρ) (lat t (resP v) (spMap ((ioOf (resP v) ε).comp (Scheme.stalkClosedPointTo
    y.1).hom) ≫ GlobalTheory.ShFam.stalkPt Y (below y.1) ≫ ρ) (decide (resP v =
    q))) (fun l => spMap (dualMap ((ioOf (resP v) ε).comp (Scheme.stalkClosedPointTo
    y.1).hom)) ≫ f (below y.1) l) (Fin.castLE hk l) := by
  intro E _ _ _ H X _ t hX F _ _ Y V ρ' ρ hρ q hq m f d hf hind k hk N c hc U U' hU hU' g g' e e' h h' he he' hd hd'
    s s' hs hs' v ε y z yt hv hz hyt hin hin' hp
  obtain rfl : resP v = q := residueCharacteristic_eq v hq.out hv
  obtain rfl : hq = hp := rfl
  obtain ⟨y, hy⟩ := y
  dsimp only at hz ⊢
  subst hz
  have h1 := ioOf_le_one_iff (resP v) hv ε
  generalize ioOf (resP v) ε = io at h1 ⊢
  let ioO : ε.O →+* intO ℂ_[resP v] := (io.comp ε.O.subtype).codRestrict _ fun b => (h1 b).2 b.2
  have hio : (intO ℂ_[resP v]).subtype.comp ioO = io.comp ε.O.subtype := rfl
  have hmem : ∀ W : V.X.Opens, ⊤ ≤ yt ⁻¹ᵁ W → V.j (below z) ∈ W := fun W hW => by
    have : (spMap ε.O.subtype ≫ yt) (IsLocalRing.closedPoint _) ∈ W := hW (Set.mem_univ _)
    rwa [hyt] at this
  obtain ⟨α, a, hα, ha, hsα⟩ := hs _ (hmem U hin)
  obtain ⟨α', a', hα', ha', hsα'⟩ := hs' _ (hmem U' hin')
  obtain ⟨ψ, hψ⟩ : ∃ ψ : V.G.presheaf.stalk (below z) →+* ℂ_[resP v],
    ψ = io.comp (Scheme.stalkClosedPointTo z).hom := ⟨_, rfl⟩
  obtain ⟨β, hβ, hβα, hb⟩ := chart V.j ρ' ε.O io ioO hio z yt hyt hU hin e α hα a _ ha ψ hψ
  obtain ⟨β', hβ', hβα', hb'⟩ := chart V.j ρ' ε.O io ioO hio z yt hyt hU' hin' e' α' hα' a' _ ha' ψ hψ
  obtain ⟨φ, hφ⟩ : ∃ φ : Y.X.presheaf.stalk (V.π (below z)) →+* ℂ_[resP v],
    φ = io.comp (Scheme.stalkClosedPointTo (z ≫ V.π)).hom := ⟨_, rfl⟩
  have hφψ : ψ.comp (V.π.stalkMap (below z)).hom = φ := by
    rw [hφ, hψ, Scheme.stalkClosedPointTo_comp]; rfl
  simp only [dual_comp _ ψ, hφψ] at hb hb'
  have hx : spMap φ ≫ GlobalTheory.ShFam.stalkPt Y (V.π (below z)) ≫ ρ =
      spMap (intO ℂ_[resP v]).subtype ≫ (spMap ioO ≫ yt) ≫ ρ' := by
    have e1 : spMap (Scheme.stalkClosedPointTo z).hom ≫ V.G.fromSpecStalk (below z) = z :=
      Scheme.Spec_stalkClosedPointTo_fromSpecStalk z
    have e2 : spMap (V.π.stalkMap (below z)).hom ≫ GlobalTheory.ShFam.stalkPt Y (V.π (below z)) =
        V.G.fromSpecStalk (below z) ≫ V.π := Scheme.SpecMap_stalkMap_fromSpecStalk V.π
    rw [← hφψ, ← spMap_comp', Category.assoc, ← Category.assoc _ _ ρ, e2, Category.assoc, ← hρ, hψ, ← spMap_comp',
      Category.assoc, ← Category.assoc _ (V.G.fromSpecStalk _), e1, Category.assoc,
      ← Category.assoc (spMap (intO ℂ_[resP v]).subtype), spMap_comp', hio, ← spMap_comp', Category.assoc,
      ← Category.assoc _ yt, hyt, Category.assoc]
  have hB := GlobalTheory.LineNorm.WedgeMax.isTanBasis_map t β he
  have hB' := GlobalTheory.LineNorm.WedgeMax.isTanBasis_map t β' he'
  rw [← Category.assoc, hβ] at hB
  rw [← Category.assoc, hβ'] at hB'
  have hli : LinearIndependent ℂ_[resP v] fun l i => ψ (a l i) :=
    linInd (GlobalTheory.LineNorm.WedgeMax.isTanBasis_map t _ hB).1 hb (hx ▸ hind _ _ φ)
  obtain ⟨k1, k2, k3, k4⟩ := GlobalTheory.T.pairDet_norm_le_attained_and_sub_norm_lt E H X t hX (resP v) _ g g' _ _ hB hB' N (fun j => c j (spMap ioO ≫ yt)) _ _
    (hc _) (hd β _ hβ) (hd' β' _ hβ') m k hk _ _ _ hli hb hb' _ rfl
  rw [← hx] at k1 k2 k3 k4
  have hval : ∀ r, io (TrueGeo.valAt z (algebraMap (V.G.presheaf.stalk (below z)) V.G.functionField r)) = ψ r :=
    fun r => by rw [hψ, Base.valAt_stalk]; rfl
  have hv1 : ∀ σ, ψ (pairDet (fun j i => α (h j i)) a hk σ) =
      pairDet (fun j i => (β (h j i) : ℂ_[resP v])) (fun l i => ψ (a l i)) hk σ := fun σ => by
    simp only [map_pairDet, hβα]
  have hv2 : ∀ σ, ψ (pairDet (fun j i => α' (h' j i)) a' hk σ) =
      pairDet (fun j i => (β' (h' j i) : ℂ_[resP v])) (fun l i => ψ (a' l i)) hk σ := fun σ => by
    simp only [map_pairDet, hβα']
  rw [decide_eq_true rfl]
  subst hφ
  refine ⟨fun l => k1 _, fun σ => ?_, ?_, fun σ => ?_⟩
  · exact (congrArg norm (((congrArg (fun r => io (TrueGeo.valAt z r)) (hsα σ)).trans (hval _)).trans (hv1 σ))).trans_le
      (k2 σ)
  · obtain ⟨σ, hσ⟩ := k3
    exact ⟨σ, (congrArg norm (((congrArg (fun r => io (TrueGeo.valAt z r)) (hsα σ)).trans (hval _)).trans
      (hv1 σ))).trans hσ⟩
  · have e1 := (sub_div _ _ _).trans ((congrArg₂ (· - ·) (hsα σ) (hsα' σ)).trans (map_sub _ _ _).symm)
    refine (congrArg norm (((congrArg (fun r => io (TrueGeo.valAt z r)) e1).trans (hval _)).trans ?_)).trans_lt (k4 σ)
    rw [map_sub, hv1, hv2]

end GlobalTheory.HtGen.FlagPoint
end

section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.ArInt GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.Mean4O GlobalTheory.LineNorm GlobalTheory.CoverNorm GlobalTheory.VertForm GlobalTheory.HtGen
open Formalism.MainNotions.DIV.Cons (intO)
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_frame_prime_tangent_compat : ∀ (E : Type) [Field E] [NumberField
    E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X
    : Scheme.{0}) [IsLocallyNoetherian X] (t : SAB H X), X.IsSeparated → ∀ (F : Type) [Field
    F] [NumberField F] (Y : Var F) (V : Cover Y) (ρ' : V.X ⟶ X) (ρ
    : Y.X ⟶ X), V.j ≫ ρ' = V.π ≫ ρ → ∀ (q : ℕ) [Fact q.Prime] (m : ℕ) (f : ∀ y : Y.X, Fin m → (Sp
    (DualNumber (Y.X.presheaf.stalk y)) ⟶ t.G.left)) (d
    : Y.X → Fin m → Y.Fnˣ), (∀ y l, IsTanAtG t (GlobalTheory.ShFam.stalkPt Y y ≫ ρ) (f y
    l)) → (∀ y (K : Type) [Field K] (ψ : Y.X.presheaf.stalk y →+* K), IsIndep t (spMap ψ ≫
    GlobalTheory.ShFam.stalkPt Y y ≫ ρ) (fun l => spMap (dualMap ψ) ≫ f y l)) → ∀ (k : ℕ) (hk
    : k ≤ m) (N : ℕ) (c : Fin N → ∀ y : Sp ↥(intO ℂ_[q]) ⟶ V.X, TorsChar t (y ≫ ρ') (q ^
    2)), (∀ y (c' : TorsChar t (y ≫ ρ') (q ^ 2)), ∃ j, Agree c' (c j y)) → ∀ (U U' : V.X.Opens) (hU
    : IsAffineOpen U) (hU' : IsAffineOpen U') (g g' : ℕ) (e : Fin g → (Sp (DualNumber Γ(V.X, U)) ⟶
    t.G.left)) (e' : Fin g' → (Sp (DualNumber Γ(V.X, U')) ⟶ t.G.left)) (h : Fin N → Fin g → Γ(V.X,
    U)) (h' : Fin N → Fin g' → Γ(V.X, U')), IsTanBasis t (hU.fromSpec ≫
    ρ') e → IsTanBasis t (hU'.fromSpec ≫ ρ') e' → (∀ (x : Γ(V.X, U) →+* ↥(intO ℂ_[q])) (y
    : Sp ↥(intO ℂ_[q]) ⟶ V.X), spMap x ≫ hU.fromSpec = y → ∀ j, DlogIs t q 2 (c j
    y) (fun i => spMap (dualMap x) ≫ e i) (fun i => x (h j i))) → (∀ (x : Γ(V.X, U') →+* ↥(intO
    ℂ_[q])) (y : Sp ↥(intO ℂ_[q]) ⟶ V.X), spMap x ≫ hU'.fromSpec = y → ∀ j, DlogIs t q 2 (c j
    y) (fun i => spMap (dualMap x) ≫ e' i) (fun i => x (h' j i))) → ∀ (s s' : (Fin k → Fin
    N) → V.G.functionField), (∀ z : V.G, V.j z ∈ U → ∃ (α : Γ(V.X, U) →+* V.G.presheaf.stalk z) (a
    : Fin m → Fin g → V.G.presheaf.stalk z), spMap α ≫ hU.fromSpec = V.G.fromSpecStalk z ≫ V.j ∧ (∀ l, IsCombAtG t (spMap
    α ≫ hU.fromSpec ≫ ρ') (fun i => spMap (dualMap α) ≫ e i) (a l) (spMap (dualMap (V.π.stalkMap
    z).hom) ≫ f (V.π z) l)) ∧ ∀ σ, s σ / V.φ ((∏ l : Fin k, d (V.π z) (Fin.castLE hk l) : Y.Fnˣ)
    : Y.Fn) = algebraMap (V.G.presheaf.stalk z) V.G.functionField (pairDet (fun j i => α (h j i)) a
    hk σ)) → (∀ z : V.G, V.j z ∈ U' → ∃ (α : Γ(V.X, U') →+* V.G.presheaf.stalk z) (a
    : Fin m → Fin g' → V.G.presheaf.stalk z), spMap α ≫ hU'.fromSpec = V.G.fromSpecStalk z ≫ V.j ∧ (∀ l, IsCombAtG t (spMap
    α ≫ hU'.fromSpec ≫ ρ') (fun i => spMap (dualMap α) ≫ e' i) (a l) (spMap (dualMap (V.π.stalkMap
    z).hom) ≫ f (V.π z) l)) ∧ ∀ σ, s' σ / V.φ ((∏ l : Fin k, d (V.π z) (Fin.castLE hk l) : Y.Fnˣ)
    : Y.Fn) = algebraMap (V.G.presheaf.stalk z) V.G.functionField (pairDet (fun j i => α (h' j i)) a
    hk σ)) → ∀ (v : HeightOneSpectrum (𝓞 F)) (ε : GlobalTheory.TrueGeo.Ext v) (y : AlgPt Y) (z
    : Sp (AlgebraicClosure F) ⟶ V.G) (yt : Sp ε.O ⟶ V.X), (q
    : 𝓞 F) ∈ v.asIdeal → z ≫ V.π = y.1 → spMap ε.O.subtype ≫ yt = z ≫ V.j → ⊤ ≤ yt ⁻¹ᵁ U → ⊤ ≤ yt ⁻¹ᵁ U' → ∀ [Fact
    (resP v).Prime], (∀ l, 0 < GlobalTheory.ShFam.Pad.grNorm t (spMap ((ioOf (resP v) ε).comp
    (Scheme.stalkClosedPointTo y.1).hom) ≫ GlobalTheory.ShFam.stalkPt Y (below y.1) ≫ ρ) (lat t
    (resP v) (spMap ((ioOf (resP v) ε).comp (Scheme.stalkClosedPointTo y.1).hom) ≫
    GlobalTheory.ShFam.stalkPt Y (below y.1) ≫ ρ) (decide (resP v = q))) (fun l => spMap (dualMap
    ((ioOf (resP v) ε).comp (Scheme.stalkClosedPointTo y.1).hom)) ≫ f (below y.1) l) (Fin.castLE hk
    l)) ∧ (∀ σ, ‖ioOf (resP v) ε (TrueGeo.valAt z (s σ / V.φ ((∏ l : Fin k, d (below
    y.1) (Fin.castLE hk l) : Y.Fnˣ) : Y.Fn)))‖ ≤ ∏ l : Fin k, GlobalTheory.ShFam.Pad.grNorm t (spMap
    ((ioOf (resP v) ε).comp (Scheme.stalkClosedPointTo y.1).hom) ≫ GlobalTheory.ShFam.stalkPt Y
    (below y.1) ≫ ρ) (lat t (resP v) (spMap ((ioOf (resP v) ε).comp (Scheme.stalkClosedPointTo
    y.1).hom) ≫ GlobalTheory.ShFam.stalkPt Y (below y.1) ≫ ρ) (decide (resP v =
    q))) (fun l => spMap (dualMap ((ioOf (resP v) ε).comp (Scheme.stalkClosedPointTo
    y.1).hom)) ≫ f (below y.1) l) (Fin.castLE hk l)) ∧ (∃ σ, ‖ioOf (resP v) ε (TrueGeo.valAt z (s σ
    / V.φ ((∏ l : Fin k, d (below y.1) (Fin.castLE hk l) : Y.Fnˣ)
    : Y.Fn)))‖ = ∏ l : Fin k, GlobalTheory.ShFam.Pad.grNorm t (spMap ((ioOf (resP v) ε).comp
    (Scheme.stalkClosedPointTo y.1).hom) ≫ GlobalTheory.ShFam.stalkPt Y (below y.1) ≫ ρ) (lat t
    (resP v) (spMap ((ioOf (resP v) ε).comp (Scheme.stalkClosedPointTo y.1).hom) ≫
    GlobalTheory.ShFam.stalkPt Y (below y.1) ≫ ρ) (decide (resP v = q))) (fun l => spMap (dualMap
    ((ioOf (resP v) ε).comp (Scheme.stalkClosedPointTo y.1).hom)) ≫ f (below y.1) l) (Fin.castLE hk
    l)) ∧ ∀ σ, ‖ioOf (resP v) ε (TrueGeo.valAt z ((s σ - s' σ) / V.φ ((∏ l : Fin k, d (below
    y.1) (Fin.castLE hk l) : Y.Fnˣ) : Y.Fn)))‖ < ∏ l : Fin k, GlobalTheory.ShFam.Pad.grNorm t (spMap
    ((ioOf (resP v) ε).comp (Scheme.stalkClosedPointTo y.1).hom) ≫ GlobalTheory.ShFam.stalkPt Y
    (below y.1) ≫ ρ) (lat t (resP v) (spMap ((ioOf (resP v) ε).comp (Scheme.stalkClosedPointTo
    y.1).hom) ≫ GlobalTheory.ShFam.stalkPt Y (below y.1) ≫ ρ) (decide (resP v =
    q))) (fun l => spMap (dualMap ((ioOf (resP v) ε).comp (Scheme.stalkClosedPointTo
    y.1).hom)) ≫ f (below y.1) l) (Fin.castLE hk l) := by
  first | exact @GlobalTheory.HtGen.FlagPoint.pairDet_values | exact GlobalTheory.HtGen.FlagPoint.pairDet_values | (intros; apply GlobalTheory.HtGen.FlagPoint.pairDet_values <;> assumption)
end

section
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.ArInt GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.Mean4O GlobalTheory.LineNorm GlobalTheory.CoverNorm GlobalTheory.VertForm GlobalTheory.HtGen
open Formalism.MainNotions.DIV.Cons (intO)
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.HtGen.genOver_flag : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) [IsLocallyNoetherian X] (t : SAB H X), X.IsSeparated → ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V : Cover Y) (ρ' : V.X ⟶ X) (ρ : Y.X ⟶ X), V.j ≫ ρ' = V.π ≫ ρ → ∀ (q : ℕ) [Fact q.Prime], CharFam t ρ' q 2 → ∀ (m : ℕ) (u₀ : Fin m → (Sp (DualNumber Y.Fn) ⟶ t.G.left)) (f : ∀ y : Y.X, Fin m → (Sp (DualNumber (Y.X.presheaf.stalk y)) ⟶ t.G.left)) (d : Y.X → Fin m → Y.Fnˣ), IsFlagFrame t ρ u₀ f d → ∀ (k : ℕ) (hk : k ≤ m), GenOver V (fun y => ((∏ l : Fin k, d y (Fin.castLE hk l) : Y.Fnˣ) : Y.Fn)) (fun v e y => -∑ l : Fin k, stepLog t ρ f q (Fin.castLE hk l) v e y) q := by
  intro E _ _ _ H X _ t hX F _ _ Y V ρ' ρ hρ q _ hC m u₀ f d hf k hk
  obtain ⟨N, c, hc, hh⟩ := hC
  have hch : ∀ x : V.X, ∃ (U : V.X.Opens) (hU : IsAffineOpen U) (g : ℕ)
      (e : Fin g → (Sp (DualNumber Γ(V.X, U)) ⟶ t.G.left)) (h : Fin N → Fin g → Γ(V.X, U)),
      x ∈ U ∧ IsTanBasis t (hU.fromSpec ≫ ρ') e ∧
      ∀ (β : Γ(V.X, U) →+* ↥(intO ℂ_[q])) (y : Sp ↥(intO ℂ_[q]) ⟶ V.X), spMap β ≫ hU.fromSpec = y →
        ∀ j, DlogIs t q 2 (c j y) (fun i => spMap (dualMap β) ≫ e i) (fun i => β (h j i)) := by
    intro x
    obtain ⟨⟨U, hU⟩, g, e, hx, he⟩ := GlobalTheory.T.exists_affine_tangent_basis_locally E H X t V.X ρ' x
    obtain ⟨h, hh'⟩ := hh U hU g e he
    exact ⟨U, hU, g, e, h, hx, he, hh'⟩
  choose U hU g e h hx he hd using hch
  choose s hs using fun x => GlobalTheory.T.flag_frame_cover_tangent_compat E H X t F Y V ρ' ρ hρ m u₀ f d hf (U x) (hU x) (g x) (e x) (he x) (Fin N) (h x) k hk
  let eqv := Fintype.equivFin (Fin k → Fin N)
  refine ⟨Fintype.card (Fin k → Fin N), U, fun x J => s x (eqv.symm J), hx, fun x J z hz => ?_,
    fun v ε y z yt hq hzy hyt x hxU => ?_⟩
  · obtain ⟨α, a, -, -, hv⟩ := hs x z hz
    exact ⟨_, (hv _).symm⟩
  · obtain ⟨hp, -, -⟩ := ioOf_spec F v ε
    haveI := Fact.mk hp
    have P := fun x' (hx' : ⊤ ≤ yt ⁻¹ᵁ U x') => GlobalTheory.T.flag_frame_prime_tangent_compat E H X t hX F Y V ρ' ρ hρ q m f d hf.tan
      (fun y K _ ψ => hf.indep y K ψ) k hk N c hc (U x) (U x') (hU x) (hU x') (g x) (g x') (e x) (e x') (h x) (h x')
      (he x) (he x') (hd x) (hd x') (s x) (s x') (hs x) (hs x') v ε y z yt hq hzy hyt hxU hx'
    obtain ⟨hpos, hle, ⟨σ, heq⟩, -⟩ := P x hxU
    have hsum := Finset.sum_congr (s₁ := (Finset.univ : Finset (Fin k))) rfl fun l _ =>
      GlobalTheory.LineNorm.Chart.stepLog_eq ρ f q (Fin.castLE hk l) v ε y hp _ rfl
    have C := GlobalTheory.T.local_unit_absolute_value_criterion F v ε k _ hpos
    dsimp only
    rw [hsum]
    refine ⟨fun J => (C _).1.2 (hle _), ⟨eqv σ, ?_⟩, fun x' hx' J => (C _).2.2.2 ((P x' hx').2.2.2 _)⟩
    rw [Equiv.symm_apply_apply]
    exact (C _).2.1.2 heq
end

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.ArInt GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.Mean4O GlobalTheory.LineNorm GlobalTheory.CoverNorm GlobalTheory.VertForm GlobalTheory.HtGen
open Formalism.MainNotions.DIV.Cons (intO)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_char_tangent_family : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) [IsLocallyNoetherian X] (t : SAB H X), X.IsSeparated → ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V : Cover Y) (ρ' : V.X ⟶ X) (ρ : Y.X ⟶ X), V.j ≫ ρ' = V.π ≫ ρ → ∀ (q : ℕ) [Fact q.Prime], CharFam t ρ' q 2 → ∀ (m : ℕ) (u₀ : Fin m → (Sp (DualNumber Y.Fn) ⟶ t.G.left)) (f : ∀ y : Y.X, Fin m → (Sp (DualNumber (Y.X.presheaf.stalk y)) ⟶ t.G.left)) (d : Y.X → Fin m → Y.Fnˣ), IsFlagFrame t ρ u₀ f d → ∀ (k : ℕ) (hk : k ≤ m), GenOver V (fun y => ((∏ l : Fin k, d y (Fin.castLE hk l) : Y.Fnˣ) : Y.Fn)) (fun v e y => -∑ l : Fin k, stepLog t ρ f q (Fin.castLE hk l) v e y) q := by
  atlas_forward_decl GlobalTheory.HtGen.genOver_flag
end

section
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.CoverNorm

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HtGen

open GlobalTheory.LineNorm GlobalTheory.Cartier

theorem nefOver_of_icls {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {d : ℕ} (hX : IsArithVar p d)
    {L A B : HermLB p} {m : ℕ} (hm : 0 < m) (h : m • L.icls = A.icls + B.icls) {l : ℕ} (hA : NefOver A l)
    (hB : NefOver B l) : NefOver L l := by
  intro Z i _ _ κ _ _ _ _ hd
  have : Module.Finite ℤ k := hX.finite
  have : IsProper p := (isProper_and_exists_isAmpleLB_of_isProjOver hX.isProjOver).1
  have hproj : IsProjOver (strHom κ Z) := by
    have : IsFinite (spMap (Int.castRingHom k)) := by
      rw [spMap, IsFinite.SpecMap_iff]
      exact (RingHom.finite_algebraMap (A := ℤ) (B := k)).2 inferInstance
    have e : strHom κ Z ≫ spMap (Int.castRingHom κ) =
        i ≫ p ≫ spMap (Int.castRingHom k) := specZIsTerminal.hom_ext _ _
    have : IsProper (strHom κ Z ≫ spMap (Int.castRingHom κ)) := by
      rw [e]; infer_instance
    have : IsProper (strHom κ Z) := IsProper.of_comp _ (spMap (Int.castRingHom κ))
    exact ProperCurve.isProjOver_of_isProper _ hd
  let F₀ : HermLB.IsomClass p → ℤ :=
    Quotient.lift (s := HermLB.isometrySetoid p) (fun L => topSelfIntersection κ (L.B.pull i) 1) fun L L' e => by
      have ⟨w, hw, _⟩ := HermLB.Isometric.pull e i rfl
      exact interNum_congr_lbIso κ _ (fun _ => (L.restr i).isLB) (fun _ => (L'.restr i).isLB) fun _ => ⟨w, hw⟩
  let G : HermLB.IsomClass p →+ ℤ := AddMonoidHom.mk' F₀ (by
    rintro ⟨L⟩ ⟨L'⟩
    exact HtTensCurve.topSelf_one_pull_tens hproj hd i L.isLB L'.isLB)
  have e := congrArg G h
  rw [map_nsmul, map_add, nsmul_eq_mul] at e
  have h₁ : 0 ≤ G A.icls := hA Z i κ hd
  have h₂ : 0 ≤ G B.icls := hB Z i κ hd
  change 0 ≤ G L.icls
  exact (mul_nonneg_iff_of_pos_left (by exact_mod_cast hm : (0 : ℤ) < m)).1 (e ▸ add_nonneg h₁ h₂)

theorem nefOver_of_pow {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {d : ℕ} (hX : IsArithVar p d)
    {L : HermLB p} {m : ℕ} (hm : 0 < m) {l : ℕ} (h : NefOver (L.pow m) l) : NefOver L l :=
  nefOver_of_icls hX (m := m + m) (by omega) (by rw [HermLB.icls_pow, add_nsmul]) h h

theorem residueCharacteristic_eq {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)} (e : TrueGeo.Ext v) {l : ℕ}
    (hl : l.Prime) (h : (l : 𝓞 F) ∈ v.asIdeal) : resP v = l := by
  obtain ⟨hp, -⟩ := ioOf_spec F v e
  refine (Nat.prime_dvd_prime_iff_eq hp hl).1 (ringChar.dvd ?_)
  rw [← map_natCast (Ideal.Quotient.mk v.asIdeal)]
  exact Ideal.Quotient.eq_zero_iff_mem.2 h

section Flags

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {lv : Level H} {Xo : Moduli Dw lv} {c : Coeff lv} {O : Type} [CommRing O] {β : O →+* c.F}
  {Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β} {F : Type} [Field F] [NumberField F] {ε : F ≃+* c.F} (C : GlobalTheory.ShFam.FlagCpt Z ε)

theorem symLog_eq {b : ℕ → Bool} {l : ℕ} (hl : l.Prime) (hb : b l = true) (σ : E →+* ℂ) (i : Fin (Dw.mult σ))
    (v : HeightOneSpectrum (𝓞 F)) (e : TrueGeo.Ext v) (y : AlgPt C.Y) (h : (l : 𝓞 F) ∈ v.asIdeal) :
    symLog C b (.inl (σ, i)) v e y = stepLog Z.t (C.π ≫ GlobalTheory.Toroidal.genι Z) (fun y => (fr C y).v σ) l i v e y +
      (if σ (H.rt : E) = H.rt0 then vDiff E l else 0) * Real.log (e.w l) := by
  obtain rfl := residueCharacteristic_eq e hl h
  rw [mixLog_eq (b := b) (by simp [hb])]
  have hl' : Real.log (resP v) ≠ 0 := (Real.log_pos (by exact_mod_cast hl.one_lt)).ne'
  simp only [symLog, mixLog, lnStep, dif_pos hl, dif_pos i.2, hb, true_and]
  split_ifs
  · field_simp
    ring
  · simp

theorem nefOver_step [IsLocallyNoetherian Z.X] (hX : Z.X.IsSeparated) (V : Cover C.Y) (ρ' : V.X ⟶ Z.X)
    (hρ : V.j ≫ ρ' = V.π ≫ C.π ≫ GlobalTheory.Toroidal.genι Z) {l : ℕ} [hl : Fact l.Prime] (hc : CharFam Z.t ρ' l 2)
    {b : ℕ → Bool} (hb : b l = true) (σ : E →+* ℂ) {k : ℕ} (hk : k ≤ Dw.mult σ) {L : HermLB V.p}
    {a : ∀ s : F →+* ℂ, Pts C.Y s → ℝ}
    (h : Norms V L (fun y => ((∏ i : Fin k, dg C y σ (Fin.castLE hk i) : C.Y.Fnˣ) : C.Y.Fn)) a
      fun v e y => -∑ i : Fin k, symLog C b (.inl (σ, (Fin.castLE hk i : ℕ))) v e y) : NefOver L l := by
  have h₁ := GlobalTheory.T.torsion_char_tangent_family E H Z.X Z.t hX F C.Y V ρ' _ hρ l hc _ _ _ _ (isFlagFrame_eig C σ) k hk
  have hm : 0 < Module.finrank ℚ E := Module.finrank_pos
  have h₂ := norms_pow F C.Y V _ _ _ _ (Module.finrank ℚ E) h
  refine nefOver_of_pow V.ar hm (GlobalTheory.T.nef_over_of_generated F C.Y V _ _ _ _ l h₂ (GlobalTheory.T.generic_over_power F C.Y V _ _ _ l _
    (-(k * if σ (H.rt : E) = H.rt0 then padicValNat l (discr E).natAbs else 0 : ℕ)) hl.out.ne_zero hm
    (fun v e y hv => ?_) h₁))
  simp only [symLog_eq C hl.out hb σ _ v e y hv, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  have : ((Module.finrank ℚ E : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  split_ifs
  · have h₃ : vDiff E l * Module.finrank ℚ E = padicValNat l (discr E).natAbs := div_mul_cancel₀ _ this
    rw [Int.cast_neg, Int.cast_natCast, Nat.cast_mul]
    linear_combination (-(k : ℝ) * Real.log (e.w l)) * h₃
  · simp

theorem norms_single {V : Cover C.Y} {L : HermLB V.p} {a : ∀ s : F →+* ℂ, Pts C.Y s → ℝ} (b : ℕ → Bool) (σ : E →+* ℂ)
    {k : ℕ} (hk : k < Dw.mult σ) (n : ℤ) {w : Sym E →₀ ℤ} (hw : w = Finsupp.single (b, none, .inl (σ, k)) n)
    (h : Norms V L (fun y => genAt (divOf C (expo Dw w)) y) a fun v e y => lgOf C w v e y) :
    ∃ a', Norms V L (fun y => ((dg C y σ ⟨k, hk⟩ ^ (-n) : C.Y.Fnˣ) : C.Y.Fn)) a'
      fun v e y => n * symLog C b (.inl (σ, k)) v e y := by
  have hP (y : C.Y.X) : ∏ x : Letter Dw, dg C y x.1 x.2 ^ expo Dw w x = dg C y σ ⟨k, hk⟩ ^ n := by
    rw [Finset.prod_eq_single ⟨σ, ⟨k, hk⟩⟩ (fun x _ hx => by
      rw [hw, expo_single, if_neg (by simpa [letterOf, hk] using hx.symm), zpow_zero]) (by simp), hw, expo_single,
      if_pos (by simp [letterOf, hk])]
  have hu (y : C.Y.X) : UnitAt y (((dg C y σ ⟨k, hk⟩ ^ n) * (eqn (divOf C (expo Dw w)) y)⁻¹ : C.Y.Fnˣ) : C.Y.Fn) := by
    have h₁ : (divOf C (expo Dw w)).IsEqn y (∏ x : Letter Dw, dg C y x.1 x.2 ^ expo Dw w x) :=
      isEqn_sum _ y fun x => ((fr_spec C y).2 x.1 x.2).zsmul _
    rw [hP] at h₁
    simpa [div_eq_mul_inv] using (Base.isEqn_eqn _ y).iff_unitAt.1 h₁
  refine ⟨_, (norms_mul_unit F C.Y V L _ _ _ _ (fun y => (hu y).inv) h).congr (fun y => ?_) (fun _ _ => rfl)
    fun v e y => ?_⟩
  · rw [← Units.val_inv_eq_inv_val, genAt, ← Units.val_mul]
    congr 1
    rw [mul_inv, inv_inv, mul_inv_cancel_right, zpow_neg]
  · rw [lgOf_eq_lgCopy, lgCopy_eq, hP, GlobalTheory.LineNorm.Neg.valAt_inv (hu _), map_inv₀, Real.log_inv, neg_add_cancel_left, hw]
    exact Finsupp.sum_single_index (h := fun (a : Sym E) (n : ℤ) => (n : ℝ) * symLog C a.1 a.2.2 v e y) (by simp)

end Flags

theorem prod_zpow_of_injective {α G : Type} [Fintype α] [CommGroup G] {k : ℕ} (e : Fin k → α) (he : Function.Injective e)
    (f : α → G) (n : α → ℤ) (s : ℤ) (h₀ : ∀ x, x ∉ Set.range e → n x = 0) (h₁ : ∀ i, n (e i) = s) :
    ∏ x, f x ^ n x = ∏ i, f (e i) ^ s :=
  (Fintype.prod_of_injective e he _ _ (fun x hx => by rw [h₀ x hx, zpow_zero]) fun i => by rw [h₁]).symm

end GlobalTheory.HtGen

open GlobalTheory.HtGen GlobalTheory.LineNorm in

theorem GlobalTheory.HtGen.exists_cover_nefOver_steps : Hypotheses2 → HypothesesH → OnObj fun D O _ _ _ _ => ∀ (c : O.s.Comp) (Q : Finset ℕ) (l : ℕ), l ∈ Q → l.Prime → ∃ (V : Cover (O.var c)) (M : DV.Rt D.what₂.Tau O.N → HermLB V.p), (∀ x, Norms V (M x) (fun z => genAt (O.root0 c Q x).D z) (fun σ y => lnAdl (O.root0 c Q x) σ y) (fun v e y => (O.root0 c Q x).lg v e y)) ∧ ∀ (τ : D.what₂.Tau) (i : ℕ), i < O.N → NefOver (ArInt.comb M fun x => if x.1 = τ ∧ x.2.val < i then -1 else 0) l := by
  intro h2 hH D O hO hf A T H h c Q l hlQ hl
  have := Fact.mk hl
  obtain ⟨hX, hN, M₀, ρ', -, hρ⟩ := GlobalTheory.T.exists_normal_model_over_projective D.what₂.LL (O.Φ.C c).Y (𝓞 O.κ.c.F) (RingOfIntegers.mapRingEquiv O.κ.e)
    O.s.T.Z.X O.s.T.Z.s ((O.Φ.C c).π ≫ GlobalTheory.Toroidal.genι O.s.T.Z) O.s.T.Z.proj (by
      rw [← (O.Φ.C c).π_str]
      simp only [Category.assoc]
      rw [Limits.pullback.condition_assoc, ← Spec.map_comp, ← Spec.map_comp]
      rfl)
  let W := h.mdl Q c
  obtain ⟨V, a, g, ρ'', ha, e₁, e₂, e₃, e₄, hz, hζ, hs⟩ :=
    GlobalTheory.T.cover_refinement_exists _ _ _ O.s.T.Z.t _ _ M₀ ρ' W.V (l ^ 2) (pow_ne_zero _ hl.ne_zero)
  rw [hρ] at e₄
  have hc := GlobalTheory.T.torsion_split_normal_base _ _ _ O.s.T.Z.t V.X ρ'' l 2 V.normal hz hζ hs
  obtain ⟨M, hM⟩ : ∃ M : DV.Rt D.what₂.Tau O.N → HermLB V.p, ∀ x, Norms V (M x) (fun z => genAt (O.root0 c Q x).D z)
      (fun σ y => lnAdl (O.root0 c Q x) σ y) (fun v e y => (O.root0 c Q x).lg v e y) :=
    ⟨_, fun x => (norms_pull _ _ W.V V a ha g e₁ e₂ e₃ _ _ _ _
      (norms_of_induces (Setup.induces_root0 D O hO.dualRef _ c W _ subset_rfl x))).congr (fun _ => pow_one _)
      (fun _ _ => by simp) fun _ _ _ => by simp⟩
  refine ⟨V, M, hM, fun τ i hi => ?_⟩
  have hb : GlobalTheory.ShFam.Pad.ArIn.ind Q l = true := decide_eq_true hlQ
  have hp : O.S.Dw.p = O.j := O.S.p_eq
  have hpq : O.S.Dw.p + O.S.Dw.q = O.N := O.S.rank_eq
  have hτ (τ : D.what₂.Tau) : O.S.Dw.mult (DV.tauEmb D τ) = O.j := GlobalTheory.LocM.Check.mult_tau (S := O.S) τ
  have hcj (τ : D.what₂.Tau) : O.S.Dw.mult (conjEmb (DV.tauEmb D τ)) + O.j = O.N := GlobalTheory.LocM.Check.mult_conj (S := O.S) τ
  have hj := O.indef.2

  have hR (x : DV.Rt D.what₂.Tau O.N) : ∃ (σ : D.host.E →+* ℂ) (k : ℕ) (hk : k < O.S.Dw.mult σ) (n : ℤ) (a' : _),
      Norms V (M x) (fun y => ((dg (O.Φ.C c) y σ ⟨k, hk⟩ ^ (-n) : (O.var c).Fnˣ) : (O.var c).Fn)) a'
        (fun v e y => n * symLog (O.Φ.C c) (GlobalTheory.ShFam.Pad.ArIn.ind Q) (.inl (σ, k)) v e y) ∧
      (x.2.val < O.j → σ = DV.tauEmb D x.1 ∧ k = x.2 ∧ n = 1) ∧
      (O.j ≤ x.2.val → σ = conjEmb (DV.tauEmb D x.1) ∧ k = O.N - 1 - x.2 ∧ n = -1) := by
    have hx := x.2.2
    by_cases hxj : x.2.val < O.j
    · obtain ⟨a', h'⟩ := norms_single (O.Φ.C c) (GlobalTheory.ShFam.Pad.ArIn.ind Q) (DV.tauEmb D x.1) (k := x.2) (by rw [hτ]; exact hxj) 1
        (if_pos (by omega)) (hM x)
      exact ⟨_, _, _, _, a', h', fun _ => ⟨rfl, rfl, rfl⟩, fun h => by omega⟩
    · have := hcj x.1
      obtain ⟨a', h'⟩ := norms_single (O.Φ.C c) (GlobalTheory.ShFam.Pad.ArIn.ind Q) (conjEmb (DV.tauEmb D x.1)) (k := O.N - 1 - x.2)
        (by omega) (-1) ((if_neg (by omega)).trans (by rw [hpq])) (hM x)
      exact ⟨_, _, _, _, a', h', fun h => absurd h hxj, fun _ => ⟨rfl, rfl, rfl⟩⟩
  choose σ k hk n a' hR h₁ h₂ using hR
  have step (s : D.host.E →+* ℂ) (m : ℕ) (hm : m ≤ O.S.Dw.mult s) (e : Fin m → DV.Rt D.what₂.Tau O.N)
      (he : Function.Injective e) (w : DV.Rt D.what₂.Tau O.N → ℤ) (u : ℤ) (hu : u * u = 1) (w₀ : ∀ x, x ∉ Set.range e → w x = 0)
      (w₁ : ∀ r, w (e r) = u) (hs : ∀ r, σ (e r) = s ∧ k (e r) = r ∧ n (e r) = -u) : NefOver (ArInt.comb M w) l := by
    refine nefOver_step (O.Φ.C c) hX V ρ'' e₄ hc hb s hm ((norms_comb hR w).congr (fun y => ?_) (fun _ _ => rfl)
      fun v ε y => ?_)
    · simp only [← Units.val_zpow_eq_zpow_val, ← Units.coe_prod]
      rw [prod_zpow_of_injective e he _ w u w₀ w₁]
      refine congrArg _ (Finset.prod_congr rfl fun r _ => ?_)
      obtain ⟨q₁, q₂, q₃⟩ := hs r
      have := hk (e r)
      rw [q₃, neg_neg, ← zpow_mul, hu, zpow_one]
      revert this
      generalize hk (e r) = q₄
      revert q₄
      rw [q₁, q₂]
      intro _ _
      rfl
    · rw [← Finset.sum_neg_distrib]
      refine (Fintype.sum_of_injective e he _ _ (fun x hx => by rw [w₀ x hx]; simp) fun r => ?_).symm
      obtain ⟨q₁, q₂, q₃⟩ := hs r
      have hu' : (u : ℝ) * u = 1 := by exact_mod_cast hu
      rw [w₁, q₁, q₂, q₃, Fin.val_castLE]
      push_cast
      linear_combination (symLog (O.Φ.C c) (GlobalTheory.ShFam.Pad.ArIn.ind Q) (.inl (s, r)) v ε y) * hu'
  by_cases hij : i ≤ O.j
  · have h₃ := step (DV.tauEmb D τ) i (by rw [hτ]; exact hij) (fun r => (τ, ⟨r, by omega⟩))
      (fun r r' e => Fin.ext (congrArg (fun x : DV.Rt D.what₂.Tau O.N => x.2.val) e))
      (fun x => if x.1 = τ ∧ x.2.val < i then -1 else 0) (-1) (by norm_num)
      (fun x hx => if_neg fun ⟨q₁, q₂⟩ => hx ⟨⟨x.2, q₂⟩, by rw [← q₁]⟩) (fun r => if_pos ⟨rfl, r.2⟩)
      fun r => h₁ _ (lt_of_lt_of_le r.2 hij)
    exact h₃
  · have hτ' := hcj τ
    have h₃ := step (conjEmb (DV.tauEmb D τ)) (O.N - i) (by omega) (fun r => (τ, ⟨O.N - 1 - r, by omega⟩))
      (fun r r' e => Fin.ext (by
        have : O.N - 1 - r = O.N - 1 - r' := congrArg (fun x : DV.Rt D.what₂.Tau O.N => x.2.val) e
        omega))
      (fun x => if x.1 = τ ∧ i ≤ x.2.val then 1 else 0) 1 (by norm_num)
      (fun x hx => if_neg fun ⟨q₁, q₂⟩ => hx ⟨⟨O.N - 1 - x.2, by omega⟩, Prod.ext q₁.symm (Fin.ext (by
        have := x.2.2
        show O.N - 1 - (O.N - 1 - x.2) = x.2
        omega))⟩)
      (fun r => if_pos ⟨rfl, by show i ≤ O.N - 1 - r; omega⟩)
      fun r => by
        obtain ⟨q₁, q₂, q₃⟩ := h₂ (τ, ⟨O.N - 1 - r, by omega⟩) (by show O.j ≤ O.N - 1 - r; omega)
        exact ⟨q₁, q₂.trans (by show O.N - 1 - (O.N - 1 - r) = r; omega), q₃⟩
    refine nefOver_of_icls V.ar one_pos ?_ (GlobalTheory.T.adelic_norm_nef_indicators h2 hH D O hO hf A T H h c Q l hlQ hl V M hM τ).2 h₃
    rw [one_nsmul, icls_comb, icls_comb, icls_comb, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← add_smul]
    congr 1
    by_cases q₁ : x.1 = τ <;> by_cases q₂ : x.2.val < i <;> simp [q₁, q₂]
    omega

end
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.CoverNorm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_norm_nef_partial_sums : Hypotheses2 → HypothesesH → OnObj fun D O _ _ _ _ => ∀ (c : O.s.Comp) (Q : Finset ℕ) (l : ℕ), l ∈ Q → l.Prime → ∃ (V : Cover (O.var c)) (M : DV.Rt D.what₂.Tau O.N → HermLB V.p), (∀ x, Norms V (M x) (fun z => genAt (O.root0 c Q x).D z) (fun σ y => lnAdl (O.root0 c Q x) σ y) (fun v e y => (O.root0 c Q x).lg v e y)) ∧ ∀ (τ : D.what₂.Tau) (i : ℕ), i < O.N → NefOver (ArInt.comb M fun x => if x.1 = τ ∧ x.2.val < i then -1 else 0) l := by
  atlas_forward_decl GlobalTheory.HtGen.exists_cover_nefOver_steps
end
