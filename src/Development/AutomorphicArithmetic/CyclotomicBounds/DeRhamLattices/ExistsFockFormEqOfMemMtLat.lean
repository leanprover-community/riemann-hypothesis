import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DefiniteComplexFormsEqTwistComplexFormsFockModel
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RationalLatticeTwistedTupleSpanTop
import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.ExistsRationalStructureLowestFormSpace
import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.ScaledFockFormCoefficientsIntegral
import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.ScaledFockFormMemMtLatIff

section
theorem _root_.UpperTheory.KN.mem_range_semilinear_of_values_mem_range :
    ∀ (K M N V U I J : Type) [Field K] [AddCommGroup M] [Module K M] [AddCommGroup N] [Module ℂ N] [AddCommGroup V] [Module K V] [AddCommGroup U] [Module ℂ U]
      (σ : K →+* ℂ) (jm : M →ₛₗ[σ] N) (ev : N →ₗ[ℂ] (I → U)) (c0 : V →ₛₗ[σ] U) (b : Module.Basis J K V),
      Submodule.span ℂ (Set.range jm) = ⊤ → Function.Injective ev → LinearIndependent ℂ (fun i => c0 (b i)) →
      (∀ m h, ev (jm m) h ∈ Set.range c0) → ∀ f : N, (∀ h, ev f h ∈ Set.range c0) → f ∈ Set.range jm := by
  intro K M N V U I J _ _ _ _ _ _ _ _ _ σ jm ev c0 b hspan hev hli hjm f hf
  classical
  letI : Algebra K ℂ := σ.toAlgebra
  have hσ : ∀ k : K, algebraMap K ℂ k = σ k := fun k => rfl
  obtain ⟨lam, hlam⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap K ℂ)
    (LinearMap.ker_eq_bot.mpr (algebraMap K ℂ).injective)
  have lam_mul : ∀ k z, lam (σ k * z) = k * lam z := by
    intro k z
    rw [← hσ, ← Algebra.smul_def, map_smul, smul_eq_mul]
  have lam_one : lam 1 = 1 := by
    have := LinearMap.congr_fun hlam 1
    simpa using this
  let B := Module.Basis.span hli
  obtain ⟨Ψ, hΨ⟩ := LinearMap.exists_extend (B.repr.toLinearMap)
  have hΨb : ∀ j, Ψ (c0 (b j)) = Finsupp.single j 1 := by
    intro j
    have h1 := LinearMap.congr_fun hΨ (B j)
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearEquiv.coe_coe,
      B.repr_self] at h1
    rwa [Module.Basis.span_apply] at h1
  have hΨv : ∀ v j, Ψ (c0 v) j = σ (b.repr v j) := by
    intro v j
    conv_lhs => rw [← b.linearCombination_repr v, Finsupp.linearCombination_apply]
    simp [map_finsuppSum, hΨb, Finsupp.single_apply, Finsupp.sum_apply]
    intro h0
    rw [h0, map_zero]
  let R : U →+ V := b.repr.symm.toLinearMap.toAddMonoidHom.comp
    ((Finsupp.mapRange.addMonoidHom lam.toAddMonoidHom).comp Ψ.toAddMonoidHom)
  have hRrepr : ∀ u j, b.repr (R u) j = lam (Ψ u j) := by
    intro u j
    simp [R]
  have KR : ∀ (z : ℂ) (v : V), R (z • c0 v) = lam z • v := by
    intro z v
    apply b.repr.injective
    ext j
    rw [hRrepr, map_smul, Finsupp.smul_apply, hΨv, smul_eq_mul, mul_comm, lam_mul,
      map_smul, Finsupp.smul_apply, smul_eq_mul, mul_comm]
  have Rc0 : ∀ v, R (c0 v) = v := by
    intro v
    have := KR 1 v
    rwa [one_smul, lam_one, one_smul] at this
  have hf' : f ∈ Submodule.span ℂ (Set.range jm) := hspan ▸ Submodule.mem_top
  obtain ⟨c, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hf'
  refine ⟨c.sum fun m a => lam a • m, ?_⟩
  apply hev
  funext h
  obtain ⟨w, hw⟩ := hf h
  have hu : ∀ m, c0 (R (ev (jm m) h)) = ev (jm m) h := by
    intro m
    obtain ⟨v, hv⟩ := hjm m h
    rw [← hv, Rc0]
  have e1 : ev (jm (c.sum fun m a => lam a • m)) h = c.sum fun m a => σ (lam a) • ev (jm m) h := by
    simp [Finsupp.sum, map_sum, map_smulₛₗ, Finset.sum_apply]
  have e2 : ev (c.sum fun m a => a • jm m) h = c.sum fun m a => a • ev (jm m) h := by
    simp [Finsupp.sum, map_sum, Finset.sum_apply]
  have e3 : c0 (R (c.sum fun m a => a • ev (jm m) h)) = c.sum fun m a => σ (lam a) • ev (jm m) h := by
    simp only [Finsupp.sum, map_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    conv_lhs => rw [← hu m]
    rw [KR, map_smulₛₗ, hu m]
  rw [e1, ← e3, ← e2, ← hw, Rc0]
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)

theorem _root_.UpperTheory.KN.exists_fock_form_eq_of_mem_mtLat :
    ∀ (D : D7) (X : RealSide D) (X0 : BaseLevelRowSide D) (Y : GlobalTheory.Mem.R3.Read (A3 := X.A3) X.R.toRealDat X.F.lv2 X0) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS X.R X.cG S) (Z : ExportTie YS X.geo.v₀) (c : NChoice D) (w : D.what₂.places.Pl) (j : Fin D.R.m) (H : AtPlace Y Z c w j),
      ∀ ι : KE c w →+* ℂ, (∀ x, ι (c.embW w x) = D.what₂.embLL x) →
      ∀ (u : ∀ τ, lowT (X.R.MW j (sg0 D X.A3.A)) τ), IsLow X j u →
      ∀ κ : ℂ, κ ≠ 0 → IsScale X.R X.geo.v₀ (baseOf Z c w j) κ →
      ∀ F ∈ (baseOf Z c w j).mtLat D.what₂.embLL (labLL D) (intLL D) (twVia Z.ρ ι), ∃ m : D.what₂.MtL (D.what₂.muTw w) (j.1 + 1), F = κ⁻¹ • fockOf Y (used_of_tw H.tw) j u (D.what₂.jMt (D.what₂.muTw w) (j.1 + 1) m) := by
  classical
  intro D X X0 Y S YS Z c w j H ι hι u hu κ hκ hsc F hF
  have hkey := UpperTheory.KN.scaled_fock_form_mem_mtLat_iff D X X0 Y S YS Z c w j H ι hι u hu κ hκ hsc
  obtain ⟨gramR, c0R, c0L, hft, u', hu', hscale⟩ := hsc
  obtain rfl : u' = u := funext fun τ => Subtype.ext ((hu' τ).trans (hu τ).symm)
  have hcoef := UpperTheory.KN.scaled_fock_form_coefficients_integral D X X0 Y S YS Z c w j H ι hι u' hu gramR c0R c0L hft κ hκ hscale
  obtain ⟨hinj, hrange⟩ := GlobalTheory.T.definiteComplexForms_eq_twistComplexForms_fockModel D X X0 Y S YS Z c w j H ι hι u' hu
  obtain ⟨hio, -⟩ := UpperTheory.KN.ioP_tprod_injective_and_range_eq_valSpace D X X0 Y S YS Z c w j H ι hι u' hu
  obtain ⟨-, -, -, hspan⟩ := UpperTheory.KN.exists_rational_structure_lowest_form_space D X X0 Y (D.what₂.muTw w) (used_of_tw H.tw) j
  have hli : LinearIndependent ℂ fun i => (c0L j (bVV D.what₂.LL (FWT.lamV D j) i) : (X.R.cV j).W) := (hft.mapL j).2.1
  let ev := (X.R.HV j (Y.tupT (D.what₂.muTw w))).e ∘ₗ formOf Y (used_of_tw H.tw) j
  have hev : ∀ x h, fockOf Y (used_of_tw H.tw) j u' x h = X.R.ioP j (PiTensorProduct.tprod ℂ u') (ev x h) := fun _ _ => rfl
  have hevinj : Function.Injective ev := fun x y hxy => hinj (funext fun h => by rw [hev, hev, hxy])
  have hval : ∀ g, κ⁻¹ • fockOf Y (used_of_tw H.tw) j u' g ∈ (baseOf Z c w j).mtLat D.what₂.embLL (labLL D) (intLL D) (twVia Z.ρ ι) →
      ∀ h, ev g h ∈ Set.range (c0L j) := by
    intro g hg h
    obtain ⟨G, -, hG⟩ := (hcoef h _).1 (((Base.mem_mtLat _ _ _ _).1 hg).2 h)
    rw [Pi.smul_apply, hev] at hG
    exact ⟨G, (hio (smul_right_injective _ (inv_ne_zero hκ) hG)).symm⟩
  have hsp : Submodule.span D.what₂.LL {x | D.what₂.jMt (D.what₂.muTw w) (j.1 + 1) x ∈ ((D.what₂.MtLat (D.what₂.muTw w) (j.1 + 1)).gen : Set _)} = ⊤ :=
    GlobalTheory.T.rationalLatticeTwistedTuple_span_top D w (j.1 + 1)
  have hall : ∀ m h, ev (D.what₂.jMt (D.what₂.muTw w) (j.1 + 1) m) h ∈ Set.range (c0L j) := by
    intro m h
    have hm : m ∈ Submodule.span D.what₂.LL {x | D.what₂.jMt (D.what₂.muTw w) (j.1 + 1) x ∈ ((D.what₂.MtLat (D.what₂.muTw w) (j.1 + 1)).gen : Set _)} := by
      rw [hsp]; trivial
    induction hm using Submodule.span_induction with
    | mem x hx =>
      refine hval _ ((hkey x).2 ⟨fun v => if v = D.what₂.jMt (D.what₂.muTw w) (j.1 + 1) x then 1 else 0, ?_⟩) h
      rw [Finset.sum_eq_single_of_mem _ (Finset.mem_coe.1 hx)]
      · simp
      · intro v _ hv
        simp [hv]
    | zero => exact ⟨0, by rw [map_zero, map_zero, map_zero]; rfl⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := hy
      exact ⟨a + b, by rw [map_add, map_add, map_add, Pi.add_apply, ← ha, ← hb]; rfl⟩
    | smul s x _ hx =>
      obtain ⟨a, ha⟩ := hx
      exact ⟨s • a, by rw [LinearMap.map_smulₛₗ, LinearMap.map_smulₛₗ, map_smul, Pi.smul_apply, ← ha]; rfl⟩
  have hF1 : κ • F ∈ LinearMap.range (fockOf Y (used_of_tw H.tw) j u') := by
    rw [hrange]
    exact Submodule.smul_mem _ _ ((Base.mem_mtLat _ _ _ _).1 hF).1
  obtain ⟨f, hf⟩ := hF1
  have hFf : F = κ⁻¹ • fockOf Y (used_of_tw H.tw) j u' f := by rw [hf, smul_smul, inv_mul_cancel₀ hκ, one_smul]
  obtain ⟨m, hm⟩ := UpperTheory.KN.mem_range_semilinear_of_values_mem_range _ _ _ _ _ _ _ D.what₂.embLL (D.what₂.jMt (D.what₂.muTw w) (j.1 + 1)) ev (c0L j)
    (bVV D.what₂.LL (FWT.lamV D j)) hspan hevinj hli hall f (hval f (hFf ▸ hF))
  exact ⟨m, by rw [hm]; exact hFf⟩
end
