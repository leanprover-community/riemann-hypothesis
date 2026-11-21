import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.ArthurClozelDescent
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.InfinitesimalCharacterPullback.HasInfCharPullSub
import GroundTheory.GlobalFields.Adele.Compact
import GroundTheory.AutomorphicForms.StrongApproximationSLDense
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.SymmetricAdjointFrobenius.InfEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.JacquetLanglandsLattices.DiscOfCusp
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.AbsExpo
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.LocCompR
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.SatLoc
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.IsGalRepOfOfIso
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsQuadraticSignCharacter
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FrobeniusSignCompatibility

section
noncomputable section

open NumberField IsDedekindDomain Topology Matrix Neutral.B1 Formalism.L2.Host Formalism.L2.Host.CT GlobalTheory.CuspRep
open scoped ContDiff

namespace UpperTheory.V.Lit

section Comp

variable {E : Type} [Field E] [NumberField E] [IsTotallyReal E]

omit [IsTotallyReal E] in

private def zf (y : Af E) : Ad E := ((0, y) : InfiniteAdeleRing E × Af E)

omit [IsTotallyReal E] in
private theorem continuous_zf : Continuous (zf (E := E)) :=
  (continuous_const.prodMk continuous_id : Continuous fun y : Af E => ((0, y) : InfiniteAdeleRing E × Af E))

private theorem continuous_sInf : Continuous (TR.sInf E) :=
  ((TR.continuous_infEq E).prodMk continuous_const :
    Continuous fun x : TR.Rinf E => ((TR.infEq E x, 0) : InfiniteAdeleRing E × Af E))

private theorem continuous_pInf : Continuous (TR.pInf E) := by
  have h : Continuous (TR.infEq E).symm := continuous_pi fun w =>
    (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal w)).continuous.comp
      (continuous_apply w)
  exact h.comp continuous_fst

private theorem split (x : Ad E) : x = TR.sInf E (TR.pInf E x) + zf (pFin E x) :=
  Prod.ext (((TR.infEq E).apply_symm_apply _).symm.trans (add_zero _).symm) (zero_add _).symm

private theorem fin_kill (f : Ad E →+* Af E) (hf : Continuous f) (t : TR.Rinf E) : f (TR.sInf E t) = 0 := by
  refine FiniteAdeleRing.ext _ fun u => ?_
  have hc : Continuous fun t : TR.Rinf E => (f (TR.sInf E t)) u :=
    (RestrictedProduct.continuous_eval u).comp (hf.comp continuous_sInf)
  have h := (isPreconnected_range hc).subsingleton ⟨t, rfl⟩ ⟨0, rfl⟩
  simpa using h

omit [IsTotallyReal E] in

private theorem inf_kill (f : Ad E →+* ℝ) (hf : Continuous f) (y : Af E) : f (zf y) = 0 := by
  have h1 : f (zf 1) = 0 := by
    obtain ⟨C, hC⟩ := ((GroundTheory.Global.isCompact_integralFiniteAdeles E).image (hf.comp continuous_zf)).isBounded.exists_norm_le
    by_contra h0
    have hp : 0 < ‖f (zf 1)‖ := norm_pos_iff.2 h0
    obtain ⟨n, hn⟩ := exists_nat_gt (C / ‖f (zf 1)‖)
    have h2 := hC _ ⟨(n : Af E), natCast_mem _ n, rfl⟩
    have e : zf (n : Af E) = (n : Ad E) * zf 1 := Prod.ext (mul_zero _).symm (mul_one _).symm
    rw [Function.comp_apply, e, map_mul, map_natCast, norm_mul, Real.norm_natCast] at h2
    rw [div_lt_iff₀ hp] at hn
    linarith
  have e : zf y = zf y * zf 1 := Prod.ext (mul_zero _).symm (mul_one _).symm
  rw [e, map_mul, h1, mul_zero]

private theorem abs_pInf (x : E) (v : InfinitePlace E) : ‖TR.pInf E (algebraMap E (Ad E) x) v‖ = v x := by
  have : TR.pInf E (algebraMap E (Ad E) x) v = InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v) x := by
    change InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal v) (algebraMap E (InfiniteAdeleRing E) x v) = _
    simp
  rw [this]
  exact InfinitePlace.norm_embedding_of_isReal _ _

private theorem ringHom_pi {ι : Type} [Finite ι] (g : (ι → ℝ) →+* ℝ) : ∃ v, ∀ t, g t = t v := by
  classical
  have := Fintype.ofFinite ι
  obtain ⟨v, hv⟩ : ∃ v, g (Pi.single v 1) ≠ 0 := by
    by_contra! h
    have h1 := map_sum g (fun v => Pi.single v (1 : ℝ)) Finset.univ
    rw [show ∑ v, Pi.single v (1 : ℝ) = (1 : ι → ℝ) from Finset.univ_sum_single (1 : ι → ℝ)] at h1
    simp [h] at h1
  refine ⟨v, fun t => mul_right_cancel₀ hv ?_⟩
  have e : t * Pi.single v 1 = algebraMap ℝ (ι → ℝ) (t v) * Pi.single v 1 := by
    funext u
    by_cases h : u = v <;> simp [h]
  have e2 : g (algebraMap ℝ (ι → ℝ) (t v)) = t v :=
    DFunLike.congr_fun (Subsingleton.elim (g.comp (algebraMap ℝ (ι → ℝ))) (RingHom.id ℝ)) (t v)
  rw [← map_mul, e, map_mul, e2]

variable {σ : E ≃+* E} {s : Ad E →+* Ad E} (hs : IsAdExt (σ : E →+* E) s)
include hs

private theorem pFin_ext (x : Ad E) : pFin E (s x) = finMap σ (pFin E x) := by
  have hf : Continuous ((pFin E).comp s) := continuous_snd.comp hs.1
  have h1 : ∀ x, pFin E (s x) = pFin E (s (zf (pFin E x))) := fun x => by
    conv_lhs => rw [split x, map_add, map_add]
    rw [show pFin E (s (TR.sInf E _)) = 0 from fin_kill _ hf _, zero_add]
  rw [h1]
  refine congrFun ((GroundTheory.Automorphic.AdelicGLn.denseRange_algebraMap_finiteAdeleRing E).equalizer
    (hf.comp continuous_zf) (continuous_finMap σ) (funext fun k => ?_)) _
  exact (h1 (algebraMap E (Ad E) k)).symm.trans ((congrArg (pFin E) (hs.2 k)).trans
    (FieldIso.finMap_algebraMap σ k).symm)

private theorem pInf_ext (x : Ad E) (w : InfinitePlace E) :
    TR.pInf E (s x) w = TR.pInf E x (w.comap (σ : E →+* E)) := by
  let f : Ad E →+* ℝ := (Pi.evalRingHom (fun _ => ℝ) w).comp ((TR.pInf E).comp s)
  have hf : Continuous f := (continuous_apply w).comp (continuous_pInf.comp hs.1)
  have h1 : ∀ x, f x = f (TR.sInf E (TR.pInf E x)) := fun x => by
    conv_lhs => rw [split x, map_add, inf_kill f hf, add_zero]
  let g : TR.Rinf E →+* ℝ :=
    { toFun := fun t => f (TR.sInf E t)
      map_one' := by
        have := h1 1
        rw [map_one, map_one] at this
        exact this.symm
      map_mul' := fun a b => by rw [map_mul, map_mul]
      map_zero' := by rw [map_zero, map_zero]
      map_add' := fun a b => by rw [map_add, map_add] }
  obtain ⟨v, hv⟩ := ringHom_pi g
  have h2 : ∀ x, TR.pInf E (s x) w = TR.pInf E x v := fun x => (h1 x).trans (hv _)
  have h3 : v = w.comap (σ : E →+* E) := by
    ext k
    have := h2 (algebraMap E (Ad E) k)
    rw [hs.2] at this
    rw [InfinitePlace.comap_apply, ← abs_pInf, ← abs_pInf, this]
  rw [h2, h3]

end Comp

section Pull

variable {E : Type} [Field E] [NumberField E] [IsTotallyReal E] {a : ℕ}

omit [NumberField E] [IsTotallyReal E] in

private def rinf (σ : E ≃+* E) : TR.Rinf E →+* TR.Rinf E :=
  RingHom.pi fun u => Pi.evalRingHom (fun _ => ℝ) (u.comap (σ : E →+* E))

omit [IsTotallyReal E] in
variable (a) in

private def lieMap (σ : E ≃+* E) : TR.Lie E a →L[ℝ] TR.Lie E a :=
  LinearMap.toContinuousLinearMap
    { toFun := fun X i k => rinf σ (X i k)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

variable {σ : E ≃+* E} {s : Ad E →+* Ad E} (hs : IsAdExt (σ : E →+* E) s)
include hs

private theorem pInf_map (g : GA E a) : GeneralLinearGroup.map (TR.pInf E) (GeneralLinearGroup.map s g) =
    GeneralLinearGroup.map (rinf σ) (GeneralLinearGroup.map (TR.pInf E) g) :=
  Units.ext (Matrix.ext fun _ _ => funext fun w => pInf_ext hs _ w)

private theorem pFin_map (g : GA E a) : GeneralLinearGroup.map (pFin E) (GeneralLinearGroup.map s g) =
    GeneralLinearGroup.map (finMap σ) (GeneralLinearGroup.map (pFin E) g) :=
  Units.ext (Matrix.ext fun _ _ => pFin_ext hs _)

private theorem map_infGL (y : GL (Fin a) (TR.Rinf E)) :
    GeneralLinearGroup.map s (TR.infGL E a y) = TR.infGL E a (GeneralLinearGroup.map (rinf σ) y) :=
  TR.ga_ext (by rw [pInf_map hs, TR.pInf_infGL, TR.pInf_infGL])
    (by rw [pFin_map hs, TR.pFin_infGL, TR.pFin_infGL, map_one])

private theorem chart_map (φ : GA E a → ℂ) (g : GA E a) {x : TR.Lie E a} (hx : x ∈ TR.invSet E a) :
    TR.chart (fun g => φ (GeneralLinearGroup.map s g)) g x = TR.chart φ (GeneralLinearGroup.map s g) (lieMap a σ x) ∧
      lieMap a σ x ∈ TR.invSet E a := by
  obtain ⟨u, hu⟩ := id hx
  obtain rfl : x = TR.toL u.val := hu.symm
  have e : lieMap a σ (TR.toL u.val) = TR.toL (GeneralLinearGroup.map (rinf σ) u).val := rfl
  rw [e, TR.chart_val, TR.chart_val, map_mul, map_infGL hs]
  exact ⟨rfl, TR.val_mem_invSet _⟩

variable (a) in

private def pl : TR.Sm E a →ₗ[ℂ] TR.Sm E a where
  toFun φ := ⟨fun g => φ.1 (GeneralLinearGroup.map s g), fun g =>
    ((φ.2 (GeneralLinearGroup.map s g)).comp (lieMap a σ).contDiff.contDiffOn
      fun _ hx => (chart_map hs φ.1 g hx).2).congr fun _ hx => (chart_map hs φ.1 g hx).1⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end Pull

end UpperTheory.V.Lit
end
end

section
noncomputable section

open NumberField Formalism.REAL

namespace UpperTheory.V.Lit

section Alg

variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

end Alg

variable {E : Type} [Field E] [NumberField E] [IsTotallyReal E] {a : ℕ}

private def res (π : TR.CuspSub E a) (w : InfinitePlace E) (i j : Fin a) : Module.End ℂ π.V :=
  (TR.Eop w i j).restrict (π.stable (.lie _))

end UpperTheory.V.Lit
end
end

section
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Matrix GlobalTheory.PRep Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR UpperTheory.V.TR Topology
open GlobalTheory.CuspRep (Af GA Ad finGL finId pFin sFin cornerGL corner ratGL chiDet)
open private orb orb_comm annPart exists_type decomp continuous_pInf from Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ShortLatticeUnitarize.CompactBoxLattices.CentChar
open private UpperTheory.V.Lit.JL.abs_pow from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.JacquetLanglandsLattices.DiscOfCusp

namespace UpperTheory.V.Lit.UnitaryTwistAlt

section Scal

variable {R S : Type} [CommRing R] [CommRing S] {a : ℕ}

private abbrev sc (a : ℕ) (y : Rˣ) : GL (Fin a) R := GeneralLinearGroup.scalar (Fin a) y

private theorem corner_scalar (s : R →ₙ+* S) (y : Rˣ) : cornerGL a s (sc a y) = sc a (Units.map (corner s) y) := by
  ext i j
  change (1 : Matrix (Fin a) (Fin a) S) i j - s ((1 : Matrix (Fin a) (Fin a) R) i j) + s (sc a y i j) = _
  by_cases e : i = j <;> simp [corner, GeneralLinearGroup.scalar, e, Matrix.one_apply, Matrix.diagonal_apply]

private theorem sc_comm (y : Rˣ) (g : GL (Fin a) R) : g * sc a y = sc a y * g :=
  Units.ext (Matrix.scalar_commute (y : R) (fun _ => mul_comm _ _) g.val).eq.symm

private theorem continuous_sc [TopologicalSpace R] : Continuous (sc a : Rˣ → GL (Fin a) R) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact (continuous_pi fun _ => Units.continuous_val : Continuous fun (y : Rˣ) (_ : Fin a) => (y : R)).matrix_diagonal
  · exact (continuous_pi fun _ => Units.continuous_coe_inv :
      Continuous fun (y : Rˣ) (_ : Fin a) => ((y⁻¹ : Rˣ) : R)).matrix_diagonal

end Scal

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {a : ℕ}

private def cptPart (π : CuspSub F a) : Representation ℂ (Kinf F a) π.V :=
  sub (cptRep F a) π.V fun k => π.stable (.cpt k)

private theorem cpt_fin (π : CuspSub F a) (k : Kinf F a) (g : GL (Fin a) (Af F)) (y : π.V) :
    π.finPart g (cptPart π k y) = cptPart π k (π.finPart g y) := by
  refine Subtype.ext ?_
  change (rt F a (finGL F a g) * rt F a (infGL F a (Unitary.toUnits k))) y.1 =
    (rt F a (infGL F a (Unitary.toUnits k)) * rt F a (finGL F a g)) y.1
  rw [← map_mul, ← map_mul, infGL_comm]

private theorem schur (h : UpperTheory.V.Published.AdmissibleReal) (π : CuspSub F a) (z : Module.End ℂ (Sm F a))
    (hz : ∀ φ ∈ π.V, z φ ∈ π.V) (hc : ∀ o, Commute z (TR.act o)) : ∃ c : ℂ, ∀ φ ∈ π.V, z φ = c • φ := by
  obtain ⟨φ₀, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 π.ne_bot
  set φ : π.V := ⟨φ₀, hφ⟩
  have h0' : φ ≠ 0 := fun e => h0 (congrArg Subtype.val e)
  let T : Module.End ℂ π.V := z.restrict hz
  have hT : ∀ o x, T (π.op o x) = π.op o (T x) := fun o x => Subtype.ext (LinearMap.congr_fun (hc o).eq x.1)
  let L : Subgroup (GL (Fin a) (Af F)) :=
    { carrier := {k | π.finPart k φ = φ}
      one_mem' := by simp
      mul_mem' := fun {a' b} ha hb => by
        change π.finPart (a' * b) φ = φ
        rw [map_mul, Module.End.mul_apply, hb, ha]
      inv_mem' := fun {a'} ha => by
        change π.finPart a'⁻¹ φ = φ
        conv_lhs => rw [← ha, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
  let X : Submodule ℂ π.V := ⨅ k ∈ L, LinearMap.eqLocus (π.finPart k) LinearMap.id
  have mem_fix : ∀ {x}, x ∈ X ↔ ∀ k ∈ L, π.finPart k x = x := fun {x} => by
    simp [X, Submodule.mem_iInf]
  have hL : IsOpen (L : Set (GL (Fin a) (Af F))) := by
    convert (π.cusp φ₀ hφ).1.level using 1
    ext k
    exact Subtype.ext_iff
  have hfd : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => cptPart π k φ)) := by
    have := (π.cusp φ₀ hφ).1.kfin
    refine FiniteDimensional.of_injective ((π.V.subtype ∘ₗ Submodule.subtype _).codRestrict
      (Submodule.span ℂ (Set.range fun k => cptRep F a k φ₀)) fun v => ?_)
      fun v v' e => Subtype.ext (Subtype.ext (by have e' := congrArg Subtype.val e; exact e'))
    refine Submodule.mem_comap.1 ((Submodule.span_le (p := Submodule.comap π.V.subtype _)).2 ?_ v.2)
    rintro _ ⟨k, rfl⟩
    exact Submodule.subset_span ⟨k, rfl⟩
  obtain ⟨d, ξ, hξ⟩ := exists_type (cptPart π) φ hfd
  let U : Submodule ℂ π.V := annPart (cptPart π) φ ⊓ X
  obtain ⟨W, hW, hWf⟩ := h F a π L hL d ξ
  have hfin : FiniteDimensional ℂ U := by
    refine Submodule.finiteDimensional_of_le (S₂ := W) fun x hx => ?_
    obtain ⟨f, hf, hx1, hf2⟩ := hξ x hx.1
    refine hWf f hf (fun k hk v => ?_) hx1
    obtain ⟨c, hc⟩ := hf2 v
    rw [hc, ← orb_comm _ _ (fun k' x => cpt_fin π k' k x), mem_fix.1 hx.2 k hk]
  have hst : ∀ x ∈ U, T x ∈ U := fun x hx => ⟨fun c hc => by
      rw [orb_comm _ T (fun k x => hT (.cpt k) x), show orb (cptPart π) x c = 0 from hx.1 c hc, map_zero],
    mem_fix.2 fun k hk => (hT (.fin k) x).symm.trans (congrArg T (mem_fix.1 hx.2 k hk))⟩
  have hφU : φ ∈ U := ⟨fun _ hc => hc, mem_fix.2 fun k hk => hk⟩
  have : Nontrivial U := ⟨⟨φ, hφU⟩, 0, fun e => h0' (congrArg Subtype.val e)⟩
  obtain ⟨c, hc'⟩ := Module.End.exists_eigenvalue (T.restrict hst)
  obtain ⟨v, hv⟩ := hc'.exists_hasEigenvector
  have hv1 : z v.1.1 = c • v.1.1 := congrArg (fun x : U => x.1.1) hv.apply_eq_smul
  refine ⟨c, fun ψ hψ => ?_⟩
  rcases π.irred (π.V ⊓ z.eigenspace c) inf_le_left (fun o x hx => ⟨π.stable o x hx.1, by
    have h1 : z x = c • x := Module.End.mem_eigenspace_iff.1 hx.2
    refine Module.End.mem_eigenspace_iff.2 ?_
    rw [← map_smul, ← h1]
    exact LinearMap.congr_fun (hc o).eq x⟩) with h | h
  · have : v.1.1 ∈ π.V ⊓ z.eigenspace c := ⟨v.1.2, Module.End.mem_eigenspace_iff.2 hv1⟩
    rw [h] at this
    exact absurd (Subtype.ext (Subtype.ext ((Submodule.mem_bot ℂ).1 this))) hv.2
  · rw [← h] at hψ
    exact Module.End.mem_eigenspace_iff.1 hψ.2

private theorem inf_sc (u : (Rinf F)ˣ) : infGL F a (sc a u) = sc a (infId F u) := corner_scalar _ u

omit [IsTotallyReal F] in
private theorem fin_sc (u : (Af F)ˣ) : finGL F a (sc a u) = sc a (finId F u) := corner_scalar _ u

private theorem commute_rt (z : Ideles F) (g : GA F a) : Commute (rt F a (sc a z)) (rt F a g) :=
  (Commute.symm (sc_comm z g)).map (rt F a)

private theorem lie_sc_rt (z : Rinf F) (y : GL (Fin a) (Rinf F)) :
    Commute (lie F a (toL (Matrix.scalar (Fin a) z))) (rt F a (infGL F a y)) := by
  have h := Cen.rt_lie y (Matrix.scalar (Fin a) z)
  rw [← (Matrix.scalar_commute z (fun _ => mul_comm _ _) y.val).eq, Units.mul_inv_cancel_right] at h
  exact h.symm

private theorem lie_sc_act (z : Rinf F) (o : Op F a) : Commute (lie F a (toL (Matrix.scalar (Fin a) z))) (TR.act o) := by
  cases o with
  | fin k => exact lie_rt_fin _ k
  | cpt k => exact lie_sc_rt z _
  | lie X =>
    have h := lie_comm (toL (Matrix.scalar (Fin a) z)) X
    have e : Matrix.of (toL (Matrix.scalar (Fin a) z)) * Matrix.of X = Matrix.of X * Matrix.of (toL (Matrix.scalar (Fin a) z)) :=
      (Matrix.scalar_commute z (fun _ => mul_comm _ _) (Matrix.of X)).eq
    rw [e, sub_self, sub_eq_zero] at h
    exact h

private def Scal (π : CuspSub F a) (z : Ideles F) : Prop := ∃ c : ℂ, ∀ φ ∈ π.V, rt F a (sc a z) φ = c • φ

private theorem Scal.mul {π : CuspSub F a} {z z' : Ideles F} (h : Scal π z) (h' : Scal π z') : Scal π (z * z') := by
  obtain ⟨c, hc⟩ := h
  obtain ⟨c', hc'⟩ := h'
  refine ⟨c' * c, fun φ hφ => ?_⟩
  rw [sc, map_mul, map_mul, Module.End.mul_apply, hc' φ hφ, map_smul, hc φ hφ, smul_smul]

private theorem scal_fin (h : UpperTheory.V.Published.AdmissibleReal) (π : CuspSub F a) (u : (Af F)ˣ) : Scal π (finId F u) := by
  refine schur h π _ (fun φ hφ => ?_) fun o => ?_
  · rw [← fin_sc]; exact π.stable (.fin _) φ hφ
  · cases o with
    | fin k => exact commute_rt _ _
    | cpt k => exact commute_rt _ _
    | lie X => rw [← fin_sc]; exact (lie_rt_fin X _).symm

private theorem scal_sign (h : UpperTheory.V.Published.AdmissibleReal) (π : CuspSub F a) (s : (Rinf F)ˣ) (hs : s * s = 1) :
    Scal π (infId F s) := by
  have hs' : (s : Rinf F) * s = 1 := congrArg Units.val hs
  have hk : (sc a s).val ∈ Matrix.unitaryGroup (Fin a) (Rinf F) := by
    rw [Matrix.mem_unitaryGroup_iff]
    simp [GeneralLinearGroup.scalar, Matrix.star_eq_conjTranspose, hs']
  have e : Unitary.toUnits (⟨_, hk⟩ : Kinf F a) = sc a s := Units.ext rfl
  refine schur h π _ (fun φ hφ => ?_) fun o => ?_
  · rw [← inf_sc, ← e]; exact π.stable (.cpt _) φ hφ
  · cases o with
    | fin k => exact commute_rt _ _
    | cpt k => exact commute_rt _ _
    | lie X =>
      rw [← inf_sc]
      have h := Cen.rt_lie (sc a s) (Matrix.of X)
      have e2 : (sc a s).val * Matrix.of X = Matrix.of X * (sc a s).val :=
        (Matrix.scalar_commute (s : Rinf F) (fun _ => mul_comm _ _) (Matrix.of X)).eq
      rw [e2, Units.mul_inv_cancel_right] at h
      exact h

private theorem scal_exp (h : UpperTheory.V.Published.AdmissibleReal) (π : CuspSub F a) (z : Rinf F) :
    Scal π (infId F (expU z)) := by
  obtain ⟨c, hc⟩ := schur h π _ (π.stable (.lie (toL (Matrix.scalar (Fin a) z)))) (lie_sc_act z)
  refine ⟨Complex.exp c, fun φ hφ => Subtype.ext (funext fun g => ?_)⟩
  let f : ℝ → ℂ := fun t => φ.1 (g * infGL F a (sc a (expU (t • z))))
  have hf : ∀ t, HasDerivAt f (c * f t) t := fun t => by
    have h1 := hasDerivAt_curve φ (g * infGL F a (sc a (expU (t • z)))) (fun t => sc a (expU (t • z)))
      (toL (Matrix.scalar (Fin a) z)) (by simp [expU_zero]) (by
        refine hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => hasDerivAt_pi.2 fun v => ?_
        by_cases e : i = j
        · subst e
          have := ((hasDerivAt_id (0 : ℝ)).mul_const (z v)).exp
          simpa using this
        · simpa [Matrix.diagonal_apply, e] using hasDerivAt_const (0 : ℝ) (0 : ℝ))
    have h2 : lieD (toL (Matrix.scalar (Fin a) z)) φ.1 (g * infGL F a (sc a (expU (t • z)))) = c * f t :=
      congrArg (fun ψ : Sm F a => ψ.1 (g * infGL F a (sc a (expU (t • z))))) (hc φ hφ)
    rw [h2] at h1
    have h3 : (fun s : ℝ => φ.1 (g * infGL F a (sc a (expU (t • z))) * infGL F a (sc a (expU (s • z))))) =
        fun s => f (t + s) := by
      funext s
      simp only [f, add_smul, expU_add, map_mul, mul_assoc]
    rw [h3] at h1
    have h4 := HasDerivAt.comp_sub_const (f := fun s => f (t + s)) t t (by rw [sub_self]; exact h1)
    simpa using h4
  have hd : ∀ t : ℝ, HasDerivAt (fun t : ℝ => Complex.exp (-c * t) * f t) 0 t := fun t => by
    have := (((hasDerivAt_id t).ofReal_comp.const_mul (-c)).cexp).mul (hf t)
    have e : Complex.exp (-c * t) * (-c * ((1 : ℝ) : ℂ)) * f t + Complex.exp (-c * t) * (c * f t) = 0 := by
      push_cast; ring
    exact e ▸ this
  have := is_const_of_deriv_eq_zero (fun t => (hd t).differentiableAt) (fun t => (hd t).deriv) 1 0
  simp only [f, one_smul, zero_smul, expU_zero, map_one, mul_one, Complex.ofReal_one, Complex.ofReal_zero, mul_zero,
    Complex.exp_zero, one_mul, inf_sc] at this
  change φ.1 (g * sc a (infId F (expU z))) = Complex.exp c * φ.1 g
  rw [← this, ← mul_assoc, ← Complex.exp_add]
  simp

private theorem scal_all (h : UpperTheory.V.Published.AdmissibleReal) (π : CuspSub F a) (z : Ideles F) : Scal π z := by
  rw [decomp z]
  refine Scal.mul ?_ (scal_fin h π _)
  obtain ⟨s, hs, e⟩ := exists_sign_mul_expU (Units.map (pInf F).toMonoidHom z)
  rw [e, map_mul]
  exact (scal_sign h π s hs).mul (scal_exp h π _)

private theorem main (h : UpperTheory.V.Published.AdmissibleReal) (π : CuspSub F a) : ∃ ω : HChar F,
    ∀ (z : Ideles F), ∀ φ ∈ π.V, rt F a (sc a z) φ = ((ω.1 z : ℂˣ) : ℂ) • φ := by
  choose c hc using scal_all h π
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 π.ne_bot
  have hi := smul_left_injective ℂ h0
  let c' : Ideles F →* ℂ :=
    { toFun := c
      map_one' := hi (by
        change c 1 • φ = (1 : ℂ) • φ
        rw [← hc 1 φ hφ, sc, map_one, map_one, one_smul]; rfl)
      map_mul' := fun z z' => hi (by
        change c (z * z') • φ = (c z * c z') • φ
        rw [← hc _ φ hφ, sc, map_mul, map_mul, Module.End.mul_apply, hc z' φ hφ, map_smul, hc z φ hφ, smul_smul, mul_comm]) }
  obtain ⟨g, hg⟩ : ∃ g, φ.1 g ≠ 0 := by
    by_contra hn
    push Not at hn
    exact h0 (Subtype.ext (funext hn))
  have h1 : Continuous fun u : (Rinf F)ˣ => c' (infId F u) := by
    have e : (fun u : (Rinf F)ˣ => c' (infId F u)) = fun u => chart φ.1 g (toL (sc a u).val) / φ.1 g := by
      funext u
      rw [chart_val, inf_sc, eq_div_iff hg]
      exact (congrArg (fun ψ : Sm F a => ψ.1 g) (hc _ φ hφ)).symm
    rw [e]
    have h3 : Continuous fun u : (Rinf F)ˣ => toL (sc a u).val :=
      (Units.continuous_val (M := Matrix (Fin a) (Fin a) (Rinf F))).comp continuous_sc
    exact ((φ.2 g).continuousOn.comp_continuous h3 fun u => val_mem_invSet _).div_const _
  have h2 : Continuous fun u : (Af F)ˣ => c' (finId F u) := by
    refine continuous_of_continuousAt_one (c'.comp (finId F)) ?_
    have ho := (π.cusp φ hφ).1.level.preimage (continuous_sc (R := Af F) (a := a))
    refine (continuousAt_const (y := (1 : ℂ))).congr ?_
    filter_upwards [ho.mem_nhds (show finRep F a (sc a 1) φ = φ by rw [sc, map_one, map_one]; rfl)] with u hu
    refine hi ?_
    change (1 : ℂ) • φ = c (finId F u) • φ
    rw [← hc _ φ hφ, ← fin_sc, one_smul]
    exact hu.symm
  have h3 : Continuous c' := by
    have e : (c' : Ideles F → ℂ) = fun z => c' (infId F (Units.map (pInf F).toMonoidHom z)) *
        c' (finId F (Units.map (pFin F).toMonoidHom z)) := by
      funext z
      rw [← map_mul, ← decomp]
    rw [e]
    exact (h1.comp (Continuous.units_map _ continuous_pInf)).mul (h2.comp (Continuous.units_map _ continuous_snd))
  refine ⟨⟨c'.toHomUnits, Units.continuous_iff.2 ⟨h3, h3.comp continuous_inv⟩, fun k => Units.ext (hi ?_)⟩, hc⟩
  change c (diagUnits F k) • φ = (1 : ℂ) • φ
  rw [← hc _ φ hφ, one_smul]
  refine Subtype.ext (funext fun x => ?_)
  have e : sc a (diagUnits F k) = ratGL F a (sc a k) := by
    ext i j
    by_cases e : i = j <;> simp [GeneralLinearGroup.scalar, ratGL, diagUnits, e, Matrix.diagonal_apply]
  rw [rt_apply, sc_comm, e]
  exact (π.cusp φ hφ).1.left _ _

end UpperTheory.V.Lit.UnitaryTwistAlt

open UpperTheory.V.Lit.UnitaryTwistAlt GlobalTheory.HeckeGal.Model GlobalTheory.Mem.Chr.CharModel in
theorem UpperTheory.V.Lit.unitTw :
    UpperTheory.V.Af.Hypotheses₂ → UpperTheory.V.Lit.UnitTw := by
  intro P F E _ _ _ _ _ _ _ a ha π
  obtain ⟨ω, hω⟩ := main P.admR π
  obtain ⟨r, hr⟩ := UpperTheory.V.Lit.JL.abs_pow E ω
  have ha0 : (a : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have key : ∀ (K : Type) [Field K] [NumberField K] (s : ℝ) w, (absPow K s).UnrAt w ∧
      (((absPow K s).val w : ℂˣ) : ℂ) = (((Formalism.ConjugateSelfDual.normV w : ℝ) ^ (-s) : ℝ) : ℂ) := fun K _ _ s w => by
    have hE := absPow_isAbsPow K s
    refine ⟨fun u hu => hE.1 w u hu, ?_⟩
    have hq : Ideal.absNorm w.asIdeal = Formalism.ConjugateSelfDual.normV w := rfl
    rw [hE.2.1 w, Complex.ofReal_cpow (Nat.cast_nonneg _), ← hq]
    simp
  refine ⟨-r / a, absPow E (-r / a), absPow F (-r / a), ⟨ω * absPow E (-r / a) ^ a, fun z => ?_, ?_⟩,
    UpperTheory.V.Af.Nf.absExpo E _, UpperTheory.V.Af.Nf.absExpo F _, key E _, key F _⟩
  · have e : ‖(((absPow E (-r / a)).1 z : ℂˣ) : ℂ)‖ = Real.exp (-r / a * logNorm E z) := by
      change ‖Complex.exp (((-r / a : ℝ) : ℂ) * (logNorm E z : ℝ))‖ = _
      rw [← Complex.ofReal_mul, Complex.norm_exp_ofReal]
    change ‖((ω.1 z * (absPow E (-r / a)).1 z ^ a : ℂˣ) : ℂ)‖ = 1
    rw [Units.val_mul, Units.val_pow_eq_pow_val, norm_mul, norm_pow, hr, e, ← Real.exp_nat_mul, ← Real.exp_add,
      Real.exp_eq_one_iff]
    field_simp
    ring
  · rintro _ ⟨φ, hφ, rfl⟩ z g
    set ν := absPow E (-r / a)
    have hd : GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin a) z) = z ^ a :=
      Units.ext (by simp [GeneralLinearGroup.scalar])
    have e : chiDet a ν (GeneralLinearGroup.scalar (Fin a) z) = ν.1 z ^ a := (congrArg ν.1 hd).trans (map_pow _ _ _)
    have h1 : φ.1 (GeneralLinearGroup.scalar (Fin a) z * g) = ((ω.1 z : ℂˣ) : ℂ) * φ.1 g :=
      (congrArg φ.1 (sc_comm z g)).symm.trans (congrArg (fun ψ : Sm E a => ψ.1 g) (hω z φ hφ))
    change φ.1 _ * ((chiDet a ν _ : ℂˣ) : ℂ) = ((ω.1 z * ν.1 z ^ a : ℂˣ) : ℂ) * (φ.1 g * ((chiDet a ν g : ℂˣ) : ℂ))
    rw [h1, map_mul, e]
    simp only [Units.val_mul]
    ring
end
end

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.CuspRep GlobalTheory.HeckeGal
  GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published UpperTheory.V.Lit

section Places

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]





private def PlRel (σ : E ≃ₐ[F] E) (w w' : HeightOneSpectrum (𝓞 E)) : Prop :=
  ∀ x y : 𝓞 E, (y : E) = σ x → (x ∈ w'.asIdeal ↔ y ∈ w.asIdeal)

end Places

section Main

variable {F E : Type} [Field F] [NumberField F] [IsTotallyReal F] [Field E] [NumberField E] [IsTotallyReal E] [Algebra F E] {a : ℕ}

variable (F) in
private def Concl (π : TR.CuspSub E a) : Prop :=
  ((∀ (v v' : InfinitePlace E) (m : Multiset ℂ), v.comap (algebraMap F E) = v'.comap (algebraMap F E) →
      π.HasInfChar v m → π.HasInfChar v' m) ∧
    ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∀ w' : HeightOneSpectrum (𝓞 E), w'.under (𝓞 F) = w.under (𝓞 F) →
      ∃ B, π.HasSat w B ∧ π.HasSat w' B) ∨
  ∃ P : TR.CuspSub F (2 * a),
    (∀ (v v' : InfinitePlace E) (m m' : Multiset ℂ), v ≠ v' → v.comap (algebraMap F E) = v'.comap (algebraMap F E) →
      π.HasInfChar v m → π.HasInfChar v' m' → P.HasInfChar (v.comap (algebraMap F E)) (m + m')) ∧
    ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite,
      (∀ w' : HeightOneSpectrum (𝓞 E), w' ≠ w → w'.under (𝓞 F) = w.under (𝓞 F) →
        ∃ B B', π.HasSat w B ∧ π.HasSat w' B' ∧ P.HasSat (w.under (𝓞 F)) (B + B')) ∧
      (normV w = normV (w.under (𝓞 F)) ^ 2 → ∃ B B' : Multiset ℂˣ, π.HasSat w (B'.map (· ^ 2)) ∧
        B = B' + B'.map (fun b => -b) ∧ P.HasSat (w.under (𝓞 F)) B)

end Main
end
