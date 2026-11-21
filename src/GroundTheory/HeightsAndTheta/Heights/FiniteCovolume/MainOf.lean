import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.OfUnfolding
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsArchUnimodular
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PGramAtData
import GroundTheory.HeightsAndTheta.Theta.RealSignature
import GroundTheory.HeightsAndTheta.Theta.Unimodular.IndefiniteUnitary
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsMajorantStabCompact
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PBoundedInverseCompact
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsSemidirectHaar
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsUnitsInvHaar
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsTorusEmbedding
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsLineEigenvalue
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsTorusModulus
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsSemidirectCovering
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PStabilizerLeviPlaces
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PUnipotentModulusHomeo
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PUnipotentModulusHaar
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StUnipotentHorizontal
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StUnipotentCentral
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PWittPartner
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsStabilizerLevi
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PComplementLattice
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PComplementExtension
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsNsmulMem

section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic GroundTheory.Heights₂.Theta Module Matrix MeasureTheory
open scoped NNReal

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

namespace ArchUnimodular

abbrev sigP (h : HermitianForm F E W) (v : Basis ι E W) (w : InfinitePlace E) : ℕ :=
  posEigenCount (GramAtData.proof h v w).1

abbrev sigQ (h : HermitianForm F E W) (v : Basis ι E W) (w : InfinitePlace E) : ℕ :=
  negEigenCount (GramAtData.proof h v w).1

def placeEquiv (h : HermitianForm F E W) (v : Basis ι E W) (w : InfinitePlace E) :
    unitaryGroupMatrix (starRingEnd ℂ) (gramAt h v w) ≃ₜ*
      indefiniteUnitaryGroup (sigP h v w) (sigQ h v w) :=
  unitaryHermitianEquiv (hH := (GramAtData.proof h v w).1) (GramAtData.proof h v w).2

def fromPi (h : HermitianForm F E W) (v : Basis ι E W) :
    (∀ w : InfinitePlace E, indefiniteUnitaryGroup (sigP h v w) (sigQ h v w)) →*
      archUnitary h v where
  toFun f := ⟨fun w => ((placeEquiv h v w).symm (f w) : GL ι ℂ),
    (Subgroup.mem_pi _).2 fun w _ => ((placeEquiv h v w).symm (f w)).2⟩
  map_one' := by
    apply Subtype.ext
    funext w
    simp
  map_mul' f g := by
    apply Subtype.ext
    funext w
    simp

theorem continuous_fromPi (h : HermitianForm F E W) (v : Basis ι E W) :
    Continuous (fromPi h v) :=
  Continuous.subtype_mk (continuous_pi fun w => continuous_subtype_val.comp
    ((placeEquiv h v w).symm.continuous.comp (continuous_apply w))) _

theorem mulEquivHaarChar_conjCME_eq_one_of_reflect {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    {t j : G} (hjj : j * j = 1) (hjt : j * t * j = t⁻¹) : mulEquivHaarChar (conjCME t) = 1 := by
  have hJ : mulEquivHaarChar (conjCME j) * mulEquivHaarChar (conjCME j) = 1 := by
    rw [← mulEquivHaarChar_conjCME_mul, hjj, conjCME_one, mulEquivHaarChar_refl]
  have h1 : mulEquivHaarChar (conjCME t⁻¹) = mulEquivHaarChar (conjCME t) := by
    rw [← hjt, mulEquivHaarChar_conjCME_mul, mulEquivHaarChar_conjCME_mul]
    calc mulEquivHaarChar (conjCME j) * mulEquivHaarChar (conjCME t) *
          mulEquivHaarChar (conjCME j)
        = mulEquivHaarChar (conjCME t) *
            (mulEquivHaarChar (conjCME j) * mulEquivHaarChar (conjCME j)) := by ring
      _ = mulEquivHaarChar (conjCME t) := by rw [hJ, mul_one]
  have h2 := mulEquivHaarChar_conjCME_inv t
  rw [h1] at h2
  have h3 : ((mulEquivHaarChar (conjCME t) : ℝ≥0) : ℝ) * (mulEquivHaarChar (conjCME t) : ℝ) = 1 := by
    exact_mod_cast h2
  have h4 : (0 : ℝ) ≤ (mulEquivHaarChar (conjCME t) : ℝ) := NNReal.coe_nonneg _
  have h5 : ((mulEquivHaarChar (conjCME t) : ℝ≥0) : ℝ) = 1 := by nlinarith
  exact_mod_cast h5

theorem mulEquivHaarChar_conjCME_archUnitary (h : HermitianForm F E W) (v : Basis ι E W)
    (g : archUnitary h v) : mulEquivHaarChar (conjCME g) = 1 := by
  let f : ∀ w : InfinitePlace E, indefiniteUnitaryGroup (sigP h v w) (sigQ h v w) :=
    fun w => placeEquiv h v w ⟨g.1 w, (Subgroup.mem_pi _).1 g.2 w trivial⟩
  have hg : fromPi h v f = g := by
    apply Subtype.ext
    funext w
    simp [fromPi, f]
  let ks := fun w => cartanHomeomorph.symm (f w)
  let k : ∀ w : InfinitePlace E, indefiniteUnitaryGroup (sigP h v w) (sigQ h v w) :=
    fun w => ((ks w).1 : indefiniteUnitaryGroup _ _)
  let s : ∀ w : InfinitePlace E, indefiniteUnitaryGroup (sigP h v w) (sigQ h v w) :=
    fun w => upqOfMatrix (ks w).2.1 (ks w).2.2.2
  let Jm : ∀ w : InfinitePlace E, indefiniteUnitaryGroup (sigP h v w) (sigQ h v w) :=
    fun w => indefJElem _ _
  have hfks : f = k * s := funext fun w => (cartanHomeomorph.apply_symm_apply (f w)).symm
  have eJ : Jm * Jm = 1 := funext fun w => indefJElem_mul_self
  have eS : Jm * s * Jm = s⁻¹ := funext fun w => indefJElem_mul_mul_indefJElem (ks w).2
  let K : Subgroup (archUnitary h v) :=
    (Subgroup.pi Set.univ fun w : InfinitePlace E =>
      maxCompact (indefiniteUnitaryGroup (sigP h v w) (sigQ h v w))).map (fromPi h v)
  have hK : IsCompact (K : Set (archUnitary h v)) := by
    rw [Subgroup.coe_map, Subgroup.coe_pi]
    exact (isCompact_univ_pi fun w => isCompact_maxCompact_indefiniteUnitary).image
      (continuous_fromPi h v)
  have hk : fromPi h v k ∈ K :=
    Subgroup.mem_map_of_mem _ ((Subgroup.mem_pi _).2 fun w _ => (ks w).1.2)
  have hjj : fromPi h v Jm * fromPi h v Jm = 1 := by rw [← map_mul, eJ, map_one]
  have hjt : fromPi h v Jm * fromPi h v s * fromPi h v Jm = (fromPi h v s)⁻¹ := by
    rw [← map_mul, ← map_mul, eS, map_inv]
  rw [← hg, hfks, map_mul, mulEquivHaarChar_conjCME_mul, mulEquivHaarChar_conjCME_eq_one hK hk,
    one_mul]
  exact mulEquivHaarChar_conjCME_eq_one_of_reflect hjj hjt

end ArchUnimodular

theorem ArchUnimodular.proof (h : HermitianForm F E W) (v : Basis ι E W) :
    ArchUnimodular.Statement h v := by
  intro μ _
  refine ⟨fun g => ?_⟩
  have hc : μ.map (conjCME g⁻¹) = μ := by
    have e := mulEquivHaarChar_smul_map μ (conjCME g⁻¹)
    rwa [ArchUnimodular.mulEquivHaarChar_conjCME_archUnitary, one_smul] at e
  have hfun : (fun x => x * g) = (fun x => g * x) ∘ (conjCME g⁻¹) := by
    funext x
    simp [mul_assoc]
  have hm : Measurable (conjCME g⁻¹) := (map_continuous (conjCME g⁻¹)).measurable
  rw [hfun, ← Measure.map_map (measurable_const_mul g) hm, hc, map_mul_left_eq_self]

section Example

open GaussianPlane

example : muG.IsMulRightInvariant := ArchUnimodular.proof hG vG muG

end Example

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix Topology
open scoped ComplexOrder

noncomputable section

namespace MajorantStabCompact

theorem form_mulVec {ι : Type*} [Fintype ι] {P A : Matrix ι ι ℂ}
    (hA : (A.map (starRingEnd ℂ))ᵀ * P * A = P) (y : ι → ℂ) :
    star (A *ᵥ y) ⬝ᵥ (P *ᵥ (A *ᵥ y)) = star y ⬝ᵥ (P *ᵥ y) := by
  have hc : (A.map (starRingEnd ℂ))ᵀ = Aᴴ := by
    ext i j
    simp [conjTranspose_apply]
  rw [hc] at hA
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, hA]

end MajorantStabCompact

open MajorantStabCompact

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [NumberField F] [IsTotallyReal F] [IsTotallyComplex E] in

theorem MajorantStabCompact.proof (h : HermitianForm F E W) (v : Basis ι E W) :
    MajorantStabCompact.Statement h v := by
  intro M
  set e : Fin (Fintype.card ι) → W := v ∘ (Fintype.equivFin ι).symm
  have he : Submodule.span E (Set.range e) = ⊤ := by
    rw [Set.range_comp, Equiv.range_eq_univ, Set.image_univ, v.span_eq]
  set C : ℝ := ∑ a, M.len (vecAt v (e a))
  have hcpt := BoundedInverseCompact.proof h v M _ e he C

  have hclosed : IsClosed (M.stab : Set (archUnitary h v)) := by
    have : (M.stab : Set (archUnitary h v)) = ⋂ w, {g : archUnitary h v |
        ((((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ)).map (starRingEnd ℂ))ᵀ * M.P w *
          (((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ)) = M.P w} := by
      ext g
      simp [Majorant.stab, Subgroup.mem_subgroupOf, Subgroup.mem_pi, mem_unitaryGroupMatrix]
    rw [this]
    refine isClosed_iInter fun w => isClosed_eq ?_ continuous_const
    have hg : Continuous fun g : archUnitary h v =>
        (((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ)) :=
      Units.continuous_val.comp ((continuous_apply w).comp continuous_subtype_val)
    exact ((hg.matrix_map Complex.continuous_conj).matrix_transpose.matrix_mul
      continuous_const).matrix_mul hg
  refine hcpt.of_isClosed_subset hclosed ?_
  intro g hg a

  have hgi : (g⁻¹ : archUnitary h v) ∈ M.stab := inv_mem hg
  have hw : ∀ w, (((((g⁻¹ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ)).map
      (starRingEnd ℂ))ᵀ * M.P w * ((((g⁻¹ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w :
        Matrix ι ι ℂ)) = M.P w := by
    intro w
    have := (Subgroup.mem_pi _).mp (Subgroup.mem_subgroupOf.mp hgi) w (Set.mem_univ w)
    exact mem_unitaryGroupMatrix.mp this
  have heq : M.len (invApply g (vecAt v (e a))) = M.len (vecAt v (e a)) := by
    simp only [Majorant.len, invApply]
    congr 1
    exact Finset.sum_congr rfl fun w _ => by rw [form_mulVec (hw w)]
  rw [heq]
  exact Finset.single_le_sum (f := fun a => M.len (vecAt v (e a)))
    (fun b _ => Real.sqrt_nonneg _) (Finset.mem_univ a)

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix MeasureTheory
open scoped ENNReal NNReal

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

def LineStabHaar.invUnits (b : InfinitePlace E → ℂ) : InfinitePlace E → ℂˣ :=
  fun w => if hb : b w = 0 then 1 else (Units.mk0 (b w) hb)⁻¹

omit [NumberField E] [IsTotallyComplex E] in
theorem LineStabHaar.invUnits_of_ne {b : InfinitePlace E → ℂ} (hb : ∀ w, b w ≠ 0) :
    invUnits b = fun w => (Units.mk0 (b w) (hb w))⁻¹ := by
  funext w
  simp [invUnits, hb w]

omit [NumberField E] [IsTotallyComplex E] in
theorem LineStabHaar.measurable_invUnits : Measurable (invUnits (E := E)) := by
  have h0 : Measurable fun z : ℂ => if hz : z = 0 then (1 : ℂˣ) else (Units.mk0 z hz)⁻¹ := by
    refine measurable_iff_comap_le.2 ?_
    change MeasurableSpace.comap _ (MeasurableSpace.comap Units.val _) ≤ _
    rw [MeasurableSpace.comap_comp]
    have e : (Units.val ∘ fun z : ℂ => if hz : z = 0 then (1 : ℂˣ) else (Units.mk0 z hz)⁻¹) =
        fun z => if z = 0 then 1 else z⁻¹ := by
      funext z
      by_cases hz : z = 0 <;> simp [hz]
    rw [e]
    exact (Measurable.ite (measurableSet_singleton 0) measurable_const measurable_inv).comap_le
  exact measurable_pi_lambda _ fun w => h0.comp (measurable_pi_apply w)

omit [NumberField F] [NumberField E] [IsTotallyReal F] [IsTotallyComplex E] [DecidableEq ι] in

theorem LineStabHaar.two_le_finrank {h : HermitianForm F E W} (v : Basis ι E W) {x₀ w₀ : W}
    (hx₀ : x₀ ≠ 0) (hp : IsHyperbolicPair h x₀ w₀) : 2 ≤ finrank E W := by
  have : Module.Finite E W := Module.Finite.of_basis v
  have hli : LinearIndependent E ![x₀, w₀] := by
    refine LinearIndependent.pair_iff.2 fun s t hst => ?_
    have e := congrArg (h.toSesq x₀) hst
    rw [map_add, map_smul, map_smul, hp.1, hp.2.2, map_zero, smul_zero, zero_add, smul_eq_mul,
      mul_one] at e
    subst e
    rw [zero_smul, add_zero, smul_eq_zero] at hst
    exact ⟨hst.resolve_right hx₀, rfl⟩
  simpa using hli.fintype_card_le_finrank

omit [NumberField F] [IsTotallyReal F] [IsTotallyComplex E] in

theorem LineStabHaar.proof (h : HermitianForm F E W) (v : Basis ι E W)
    (h1 : WittPartner.Statement h) (h2 : VecAtNeZero.Statement v)
    (h3 : TorusEmbedding.Statement h v) (h4 : LineEigenvalue.Statement h v)
    (h5 : TorusModulus.Statement h v)
    (h6 : SemidirectHaar.Statement (archUnitary h v) (InfinitePlace E → ℂˣ))
    (h7 : UnitsInvHaar.Statement (InfinitePlace E)) : LineStabHaar.Statement h v := by
  classical
  intro x₀ hx₀ hiso μP _
  obtain ⟨w₀, hxw, hww⟩ := h1 x₀ hx₀ hiso
  have hp : IsHyperbolicPair h x₀ w₀ := ⟨hiso, hww, hxw⟩
  obtain ⟨τ₀, hτc, hτ⟩ := h3 x₀ w₀ hp
  obtain ⟨β, hβc, hβ⟩ := h4 x₀ hx₀
  have hN := LineStabHaar.two_le_finrank v hx₀ hp
  have hX := h2 x₀ hx₀
  have act : ∀ (g k : archUnitary h v) w (z : ι → ℂ),
      (((g * k : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ z =
        ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ
          (((k : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ z) := by
    intro g k w z
    simp [Matrix.mulVec_mulVec]
  have τinv : ∀ a w, ((((τ₀ a)⁻¹ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w :
      Matrix ι ι ℂ) *ᵥ vecAt v x₀ w = (((a w)⁻¹ : ℂˣ) : ℂ) • vecAt v x₀ w := by
    intro a w
    rw [← map_inv, (hτ a⁻¹ w).1, Pi.inv_apply]
  have hmemP : ∀ t, τ₀ t ∈ lineStab h v x₀ := fun t w => ⟨t w, (hτ t w).1⟩
  have hnorm : ∀ t, ∀ x ∈ vecFixGroup h v x₀, τ₀ t * x * (τ₀ t)⁻¹ ∈ vecFixGroup h v x₀ := by
    intro t x hx w
    rw [act, act, τinv, Matrix.mulVec_smul, Matrix.mulVec_smul, hx w, (hτ t w).1, smul_smul,
      Units.inv_mul, one_smul]
  have hinj : ∀ t, τ₀ t ∈ vecFixGroup h v x₀ → t = 1 := by
    intro t ht
    funext w
    have e := ht w
    rw [(hτ t w).1] at e
    have e' : ((t w : ℂ) - 1) • vecAt v x₀ w = 0 := by rw [sub_smul, one_smul, e, sub_self]
    exact Units.ext (sub_eq_zero.mp ((smul_eq_zero.mp e').resolve_right (hX w)))
  have hdec : ∀ p : lineStab h v x₀, (p : archUnitary h v) * (τ₀ (β p))⁻¹ ∈ vecFixGroup h v x₀ := by
    intro p w
    rw [act, τinv, Matrix.mulVec_smul, hβ p w, smul_smul, Units.inv_mul, one_smul]
  set N := finrank E W with hNdef
  let δ : (InfinitePlace E → ℂˣ) → ℝ≥0 := fun t => ∏ w, ‖(((t w)⁻¹ : ℂˣ) : ℂ)‖₊ ^ (2 * (N - 1))
  have hδc : Continuous δ := continuous_finsetProd _ fun w _ =>
    ((Units.continuous_coe_inv.comp (continuous_apply w)).nnnorm).pow _
  have hδcoe : ∀ t, (δ t : ℝ≥0∞) = ∏ w, ‖(t w : ℂ)‖ₑ⁻¹ ^ (2 * (N - 2 + 1)) := by
    intro t
    rw [show N - 2 + 1 = N - 1 by omega, ENNReal.ofNNReal_finsetProd]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [ENNReal.coe_pow, Units.val_inv_eq_inv_val, nnnorm_inv,
      ENNReal.coe_inv (nnnorm_ne_zero_iff.mpr (t w).ne_zero), enorm_eq_nnnorm]
  let ν₀ : Measure (vecFixGroup h v x₀) := Measure.haar
  let ρ : Measure (InfinitePlace E → ℂˣ) := Measure.haar
  have hδ : ∀ (t : InfinitePlace E → ℂˣ) (f : archUnitary h v → ℝ≥0∞), Measurable f →
      ∫⁻ x, f (τ₀ t * x * (τ₀ t)⁻¹) ∂ν₀ = δ t * ∫⁻ x, f x ∂ν₀ := by
    intro t f hf
    rw [hδcoe, show N - 2 + 1 = N - 1 by omega]
    exact h5 x₀ w₀ hp (τ₀ t) (fun w => (t w : ℂ)) (fun w => (hτ t w).1) (fun w => (hτ t w).2.1)
      (fun w z hz₁ hz₂ => (hτ t w).2.2 z hz₁ hz₂) ν₀ f hf
  obtain ⟨c, hc0, hc⟩ := h6 (lineStab h v x₀) (vecFixGroup h v x₀) (isClosed_lineStab h v x₀)
    (isClosed_vecFixGroup h v x₀) (vecFixGroup_le_lineStab h v x₀) τ₀ β δ hτc hβc hδc hmemP hnorm
    hinj hdec μP ν₀ ρ hδ
  obtain ⟨c', hc'0, hc'⟩ := h7 ρ
  let τ : (InfinitePlace E → ℂ) → archUnitary h v := fun b =>
    if ∀ w, b w ≠ 0 then τ₀ (LineStabHaar.invUnits b) else 1
  have hτb : ∀ b (hb : ∀ w, b w ≠ 0), τ b = τ₀ fun w => (Units.mk0 (b w) (hb w))⁻¹ := by
    intro b hb
    simp only [τ, if_pos hb, LineStabHaar.invUnits_of_ne hb]
  have hset : MeasurableSet {b : InfinitePlace E → ℂ | ∀ w, b w ≠ 0} := by
    rw [Set.ofPred_forall]
    exact MeasurableSet.iInter fun w => (measurableSet_singleton (0 : ℂ)).compl.preimage
      (measurable_pi_apply w)
  refine ⟨((c * c' : ℝ≥0) : ℝ≥0∞) • ν₀, τ, Measure.IsHaarMeasure.smul _ (by simp [hc0, hc'0]) ENNReal.coe_ne_top,
    Measurable.ite hset (hτc.measurable.comp LineStabHaar.measurable_invUnits) measurable_const,
    fun b => ?_, fun b hb => ?_, fun φ hφ => ?_⟩
  · by_cases hb : ∀ w, b w ≠ 0
    · rw [hτb b hb]
      exact hmemP _
    · simp only [τ, if_neg hb]
      exact one_mem _
  · funext w
    rw [invApply, hτb b hb, ← map_inv, (hτ _ w).1]
    simp
  · have hg : Measurable fun t => ∫⁻ x : vecFixGroup h v x₀, φ (x * τ₀ t) ∂ν₀ :=
      Measurable.lintegral_prod_right' (f := fun q : (InfinitePlace E → ℂˣ) × vecFixGroup h v x₀ =>
        φ (q.2 * τ₀ q.1)) (hφ.comp ((continuous_subtype_val.comp continuous_snd).mul
          (hτc.comp continuous_fst)).measurable)
    have key := hc' (N - 2) (fun t => ∫⁻ x : vecFixGroup h v x₀, φ (x * τ₀ t) ∂ν₀)
      (fun b => ∫⁻ x : vecFixGroup h v x₀, φ (x * τ b) ∂ν₀) hg (fun b hb => by rw [hτb b hb])
    rw [hc φ hφ]
    simp_rw [hδcoe]
    rw [key]
    have e2 : ∀ b : InfinitePlace E → ℂ, (∏ w, ‖b w‖ₑ ^ (2 * (N - 2))) *
        ∫⁻ x : vecFixGroup h v x₀, φ (x * τ b) ∂(((c * c' : ℝ≥0) : ℝ≥0∞) • ν₀) =
        ((c * c' : ℝ≥0) : ℝ≥0∞) * ((∏ w, ‖b w‖ₑ ^ (2 * (N - 2))) *
          ∫⁻ x : vecFixGroup h v x₀, φ (x * τ b) ∂ν₀) := by
      intro b
      rw [lintegral_smul_measure, smul_eq_mul, mul_left_comm]
    simp_rw [e2]
    rw [lintegral_const_mul' _ _ ENNReal.coe_ne_top, ENNReal.coe_mul, mul_assoc]

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open MeasureTheory MeasureTheory.Measure Topology
open scoped ENNReal

noncomputable section

theorem SemidirectCovering.proof (H L N : Type*) [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] [LocallyCompactSpace H] [SecondCountableTopology H] [T2Space H]
    [MeasurableSpace H] [BorelSpace H] [Group L] [TopologicalSpace L] [IsTopologicalGroup L]
    [LocallyCompactSpace L] [SecondCountableTopology L] [T2Space L] [MeasurableSpace L]
    [BorelSpace L] [Group N] [TopologicalSpace N] [IsTopologicalGroup N] [LocallyCompactSpace N]
    [SecondCountableTopology N] [T2Space N] [MeasurableSpace N] [BorelSpace N] :
    SemidirectCovering.Statement H L N := by
  intro i q j hi hq hj hqi hker μL _ μN _ hconj Γ C T hC hT hTfin hCcov hTcov ν _
  have hqj : ∀ n, q (j n) = 1 := fun n => (hker _).2 ⟨n, rfl⟩
  have hmem : ∀ g, g * (i (q g))⁻¹ ∈ Set.range j := fun g =>
    (hker _).1 (by simp [hqi])
  let e := Equiv.ofInjective j hj.injective
  let k : H → N := fun g => e.symm ⟨g * (i (q g))⁻¹, hmem g⟩
  have hjk : ∀ g, j (k g) = g * (i (q g))⁻¹ := fun g =>
    Equiv.apply_ofInjective_symm hj.injective _
  have hk : Continuous k := by
    rw [hj.isEmbedding.continuous_iff]
    have : (j ∘ k) = fun g => g * (i (q g))⁻¹ := funext hjk
    rw [this]; fun_prop

  let Φ : N × L ≃ₜ H :=
    { toFun := fun p => j p.1 * i p.2
      invFun := fun g => (k g, q g)
      left_inv := fun p => by
        have h1 : q (j p.1 * i p.2) = p.2 := by simp [hqj, hqi]
        refine Prod.ext (hj.injective ?_) h1
        rw [hjk, h1]; simp
      right_inv := fun g => by simp [hjk]
      continuous_toFun := by fun_prop
      continuous_invFun := hk.prodMk hq }
  have hΦ : ∀ p, Φ p = j p.1 * i p.2 := fun _ => rfl
  let μ' : Measure H := (μN.prod μL).map Φ
  have : IsFiniteMeasureOnCompacts μ' := ⟨fun K hK => by
    rw [Measure.map_apply Φ.continuous.measurable hK.isClosed.measurableSet]
    exact (Φ.isCompact_preimage.2 hK).measure_lt_top⟩
  have : IsOpenPosMeasure μ' := Φ.continuous.isOpenPosMeasure_map Φ.surjective
  have : IsMulLeftInvariant μ' := by
    refine ⟨fun h => ?_⟩
    obtain ⟨⟨n₀, l₀⟩, rfl⟩ := Φ.surjective h

    let c : N → N := fun n => k (i l₀ * j n * (i l₀)⁻¹)
    have hjc : ∀ n, j (c n) = i l₀ * j n * (i l₀)⁻¹ := fun n => by
      simp only [c, hjk, map_mul, map_inv, hqj, hqi]; simp
    have hcc : Continuous c := by fun_prop
    have hcμ : MeasurePreserving c μN μN := by
      refine ⟨hcc.measurable, ?_⟩
      have hjm := hj.measurableEmbedding
      calc μN.map c = (((μN.map c).map j).comap j) := (hjm.comap_map _).symm
        _ = ((μN.map j).comap j) := by
          rw [Measure.map_map hjm.measurable hcc.measurable,
            show j ∘ c = fun n => i l₀ * j n * (i l₀)⁻¹ from funext hjc, hconj l₀]
        _ = μN := hjm.comap_map _
    have hF : MeasurePreserving (Prod.map (fun n => n₀ * c n) (fun l => l₀ * l))
        (μN.prod μL) (μN.prod μL) :=
      ((measurePreserving_mul_left μN n₀).comp hcμ).prod (measurePreserving_mul_left μL l₀)
    have hcomp : (fun g => Φ (n₀, l₀) * g) ∘ Φ =
        Φ ∘ Prod.map (fun n => n₀ * c n) (fun l => l₀ * l) := by
      funext ⟨n, l⟩
      simp only [Function.comp_apply, hΦ, Prod.map_fst, Prod.map_snd, map_mul, hjc]
      group
    simp only [μ']
    rw [Measure.map_map (measurable_const_mul _) Φ.continuous.measurable, hcomp,
      ← Measure.map_map Φ.continuous.measurable hF.measurable, hF.map_eq]
  have : IsHaarMeasure μ' := {}

  refine ⟨Φ.symm ⁻¹' (C ×ˢ T), Φ.symm.continuous.measurable (hC.isClosed.measurableSet.prod hT),
    ?_, ?_⟩
  · rw [isMulLeftInvariant_eq_smul ν μ', Measure.smul_apply,
      Measure.map_apply Φ.continuous.measurable
        (Φ.symm.continuous.measurable (hC.isClosed.measurableSet.prod hT))]
    have : Φ ⁻¹' (Φ.symm ⁻¹' (C ×ˢ T)) = C ×ˢ T := by ext p; simp
    rw [this, Measure.prod_prod, ENNReal.smul_def, smul_eq_mul]
    exact ENNReal.mul_lt_top ENNReal.coe_lt_top (ENNReal.mul_lt_top hC.measure_lt_top hTfin)
  · intro g
    obtain ⟨γ₁, hγ₁, hγ₁T⟩ := hTcov (q g)
    obtain ⟨δ, hδ, hδC⟩ := hCcov (k (γ₁ * g))
    refine ⟨j δ * γ₁, Γ.mul_mem hδ hγ₁, ?_⟩
    have h1 : q (j δ * γ₁ * g) = q γ₁ * q g := by simp [hqj]
    have h2 : k (j δ * γ₁ * g) = δ * k (γ₁ * g) := by
      apply hj.injective
      rw [hjk, h1, map_mul j, hjk, map_mul i]
      simp [mul_assoc]
    show (k (j δ * γ₁ * g), q (j δ * γ₁ * g)) ∈ C ×ˢ T
    rw [h1, h2]
    exact ⟨hδC, hγ₁T⟩

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix Topology

noncomputable section

set_option linter.unusedSectionVars false

namespace StabilizerLevi

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

def mat {h : HermitianForm F E W} {v : Basis ι E W} (g : archUnitary h v) (w : InfinitePlace E) :
    Matrix ι ι ℂ :=
  ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ)

section Mat

variable {h : HermitianForm F E W} {v : Basis ι E W}

theorem mat_mul (g g' : archUnitary h v) (w : InfinitePlace E) :
    mat (g * g') w = mat g w * mat g' w := rfl

theorem mat_one (w : InfinitePlace E) : mat (1 : archUnitary h v) w = 1 := rfl

theorem mat_mul_inv (g : archUnitary h v) (w : InfinitePlace E) : mat g w * mat g⁻¹ w = 1 := by
  rw [← mat_mul, mul_inv_cancel, mat_one]

theorem mat_inv_mul (g : archUnitary h v) (w : InfinitePlace E) : mat g⁻¹ w * mat g w = 1 := by
  rw [← mat_mul, inv_mul_cancel, mat_one]

theorem unitary_mat (g : archUnitary h v) (w : InfinitePlace E) :
    (mat g w)ᴴ * gramAt h v w * mat g w = gramAt h v w := by
  have := mem_archUnitary.1 g.2 w
  rwa [conjT_eq] at this

theorem continuous_mat (w : InfinitePlace E) : Continuous fun g : archUnitary h v => mat g w :=
  Units.continuous_val.comp ((continuous_apply w).comp continuous_subtype_val)

end Mat

variable {h : HermitianForm F E W} {v : Basis ι E W} {x₀ w₀ : W} {n : ℕ}
  (hp : IsHyperbolicPair h x₀ w₀) {h' : HermitianForm F E (hypComplement h x₀ w₀)}
  (hh' : ∀ x y, h'.toSesq x y = h.toSesq x y) {v' : Basis (Fin n) E (hypComplement h x₀ w₀)}

abbrev bMat (v : Basis ι E W) (v' : Basis (Fin n) E (hypComplement h x₀ w₀)) (w : InfinitePlace E) :
    Matrix ι (Fin n) ℂ :=
  colMat v (fun k => (v' k : W)) w

include hp hh'

theorem q_mul (g g' : archUnitary h v) (hg : g ∈ vecFixGroup h v x₀)
    (hg' : g' ∈ vecFixGroup h v x₀) (w : InfinitePlace E) :
    leviProj (gramAt h v w) (bMat v v' w) (mat (g * g') w) =
      leviProj (gramAt h v w) (bMat v v' w) (mat g w) *
        leviProj (gramAt h v w) (bMat v v' w) (mat g' w) := by
  obtain ⟨hH, hG, hBX, hBY, hXX, hYY, hXY, hspan⟩ := frame v hp h' hh' v' w
  rw [mat_mul]
  exact leviProj_mul hH hG hBX hBY hXX hYY hXY hspan (unitary_mat g w) (hg w) (unitary_mat g' w)
    (hg' w)

theorem q_one (w : InfinitePlace E) :
    leviProj (gramAt h v w) (bMat v v' w) (mat (1 : archUnitary h v) w) = 1 := by
  obtain ⟨hH, hG, -⟩ := frame v hp h' hh' v' w
  rw [mat_one, leviProj, Matrix.mul_one]
  exact leftInv_mul hG

def qUnit (g : vecFixGroup h v x₀) (w : InfinitePlace E) : GL (Fin n) ℂ where
  val := leviProj (gramAt h v w) (bMat v v' w) (mat (g : archUnitary h v) w)
  inv := leviProj (gramAt h v w) (bMat v v' w) (mat ((g⁻¹ : vecFixGroup h v x₀) : archUnitary h v) w)
  val_inv := by
    rw [← q_mul hp hh' _ _ g.2 (g⁻¹).2, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one,
      q_one hp hh']
  inv_val := by
    rw [← q_mul hp hh' _ _ (g⁻¹).2 g.2, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one,
      q_one hp hh']

theorem qUnit_mem (g : vecFixGroup h v x₀) :
    (fun w => qUnit hp hh' (v' := v') g w) ∈ archUnitary h' v' := by
  rw [mem_archUnitary]
  intro w
  obtain ⟨hH, hG, hBX, hBY, hXX, hYY, hXY, hspan⟩ := frame v hp h' hh' v' w
  rw [conjT_eq]
  change (leviProj (gramAt h v w) (bMat v v' w) (mat (g : archUnitary h v) w))ᴴ * gramAt h' v' w *
    leviProj (gramAt h v w) (bMat v v' w) (mat (g : archUnitary h v) w) = gramAt h' v' w
  rw [gramAt_complement v h' hh' v' w]
  exact leviProj_unitary hH hG hBX hBY hXX hYY hXY hspan (unitary_mat _ w) (g.2 w)

def qHom : vecFixGroup h v x₀ →* archUnitary h' v' where
  toFun g := ⟨fun w => qUnit hp hh' g w, qUnit_mem hp hh' g⟩
  map_one' := Subtype.ext (funext fun w => Units.ext (q_one hp hh' w))
  map_mul' g g' := Subtype.ext (funext fun w => Units.ext (q_mul hp hh' _ _ g.2 g'.2 w))

def iUnit (m : archUnitary h' v') (w : InfinitePlace E) : GL ι ℂ where
  val := leviSec (gramAt h v w) (bMat v v' w) (mat m w)
  inv := leviSec (gramAt h v w) (bMat v v' w) (mat m⁻¹ w)
  val_inv := by
    obtain ⟨hH, hG, -⟩ := frame v hp h' hh' v' w
    rw [← leviSec_mul hG, mat_mul_inv, leviSec_one]
  inv_val := by
    obtain ⟨hH, hG, -⟩ := frame v hp h' hh' v' w
    rw [← leviSec_mul hG, mat_inv_mul, leviSec_one]

theorem iUnit_mem (m : archUnitary h' v') : (fun w => iUnit hp hh' (v := v) m w) ∈ archUnitary h v := by
  rw [mem_archUnitary]
  intro w
  obtain ⟨hH, hG, -⟩ := frame v hp h' hh' v' w
  rw [conjT_eq]
  change (leviSec (gramAt h v w) (bMat v v' w) (mat m w))ᴴ * gramAt h v w *
    leviSec (gramAt h v w) (bMat v v' w) (mat m w) = gramAt h v w
  refine leviSec_unitary hH hG _ ?_
  rw [← gramAt_complement v h' hh' v' w]
  exact unitary_mat m w

theorem iUnit_mem_vecFixGroup (m : archUnitary h' v') :
    (⟨fun w => iUnit hp hh' (v := v) m w, iUnit_mem hp hh' m⟩ : archUnitary h v) ∈ vecFixGroup h v x₀ := by
  intro w
  obtain ⟨hH, hG, hBX, -⟩ := frame v hp h' hh' v' w
  exact leviSec_mulVec_of hBX _

def iHom : archUnitary h' v' →* vecFixGroup h v x₀ where
  toFun m := ⟨⟨fun w => iUnit hp hh' (v := v) m w, iUnit_mem hp hh' m⟩, iUnit_mem_vecFixGroup hp hh' m⟩
  map_one' := Subtype.ext (Subtype.ext (funext fun w => Units.ext (by
    change leviSec (gramAt h v w) (bMat v v' w) (mat (1 : archUnitary h' v') w) = 1
    rw [mat_one, leviSec_one])))
  map_mul' m m' := Subtype.ext (Subtype.ext (funext fun w => Units.ext (by
    obtain ⟨hH, hG, -⟩ := frame v hp h' hh' v' w
    change leviSec (gramAt h v w) (bMat v v' w) (mat (m * m') w) =
      leviSec (gramAt h v w) (bMat v v' w) (mat m w) * leviSec (gramAt h v w) (bMat v v' w) (mat m' w)
    rw [mat_mul, leviSec_mul hG])))

theorem continuous_qHom : Continuous (qHom hp hh' (v := v) (v' := v')) := by
  refine continuous_induced_rng.2 (continuous_pi fun w => Units.continuous_iff.2 ⟨?_, ?_⟩)
  · change Continuous fun g : vecFixGroup h v x₀ =>
      leftInv (gramAt h v w) (bMat v v' w) * mat (g : archUnitary h v) w * bMat v v' w
    exact (continuous_const.matrix_mul ((continuous_mat w).comp continuous_subtype_val)).matrix_mul
      continuous_const
  · change Continuous fun g : vecFixGroup h v x₀ =>
      leftInv (gramAt h v w) (bMat v v' w) * mat ((g⁻¹ : vecFixGroup h v x₀) : archUnitary h v) w *
        bMat v v' w
    exact (continuous_const.matrix_mul (((continuous_mat w).comp continuous_subtype_val).comp
      continuous_inv)).matrix_mul continuous_const

theorem continuous_iHom : Continuous (iHom hp hh' (v := v) (v' := v')) := by
  refine continuous_induced_rng.2 (continuous_induced_rng.2
    (continuous_pi fun w => Units.continuous_iff.2 ⟨?_, ?_⟩))
  · change Continuous fun m : archUnitary h' v' =>
      1 - bMat v v' w * leftInv (gramAt h v w) (bMat v v' w) +
        bMat v v' w * mat m w * leftInv (gramAt h v w) (bMat v v' w)
    exact continuous_const.add ((continuous_const.matrix_mul (continuous_mat w)).matrix_mul
      continuous_const)
  · change Continuous fun m : archUnitary h' v' =>
      1 - bMat v v' w * leftInv (gramAt h v w) (bMat v v' w) +
        bMat v v' w * mat m⁻¹ w * leftInv (gramAt h v w) (bMat v v' w)
    exact continuous_const.add ((continuous_const.matrix_mul
      ((continuous_mat w).comp continuous_inv)).matrix_mul continuous_const)

end StabilizerLevi

open StabilizerLevi

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem StabilizerLevi.proof (h : HermitianForm F E W) (v : Basis ι E W) :
    StabilizerLevi.Statement h v := by
  intro x₀ w₀ hp h' hh' n v'
  refine ⟨iHom hp hh', qHom hp hh', continuous_iHom hp hh', continuous_qHom hp hh', ?_, ?_, ?_, ?_⟩
  · intro m
    apply Subtype.ext
    funext w
    apply Units.ext
    obtain ⟨hH, hG, -⟩ := frame v hp h' hh' v' w
    exact leviProj_leviSec hG (mat m w)
  · intro g
    rw [mem_unipRadical]
    constructor
    · intro h1 w
      obtain ⟨hH, hG, hBX, hBY, hXX, hYY, hXY, hspan⟩ := frame v hp h' hh' v' w
      have e : leviProj (gramAt h v w) (bMat v v' w) (mat (g : archUnitary h v) w) = 1 :=
        congrArg (fun u : archUnitary h' v' =>
          ((u : InfinitePlace E → GL (Fin n) ℂ) w : Matrix (Fin n) (Fin n) ℂ)) h1
      exact ⟨g.2 w, (leviProj_eq_one_iff hH hG hBX hBY hXX hYY hXY hspan (unitary_mat _ w)
        (g.2 w)).1 e⟩
    · intro h1
      apply Subtype.ext
      funext w
      apply Units.ext
      obtain ⟨hH, hG, hBX, hBY, hXX, hYY, hXY, hspan⟩ := frame v hp h' hh' v' w
      exact (leviProj_eq_one_iff hH hG hBX hBY hXX hYY hXY hspan (unitary_mat _ w) (g.2 w)).2
        (h1 w).2
  · intro m w
    obtain ⟨hH, hG, hBX, hBY, -⟩ := frame v hp h' hh' v' w
    exact leviSec_mulVec_of hBY _
  · intro γ m hx hw hW
    apply Subtype.ext
    funext w
    apply Units.ext
    obtain ⟨hH, hG, hBX, hBY, hXX, hYY, hXY, hspan⟩ := frame v hp h' hh' v' w
    change leviSec (gramAt h v w) (bMat v v' w) (mat (archEmbed h' v' m) w) = mat (archEmbed h v γ) w
    symm
    apply eq_leviSec hH hG hBX hBY hXX hYY hXY hspan
    · rw [mat, archEmbed_apply, map_toMatrix_mulVec_vecAt]
      exact congrArg (fun x => vecAt v x w) hx
    · rw [mat, archEmbed_apply, map_toMatrix_mulVec_vecAt]
      exact congrArg (fun x => vecAt v x w) hw
    · apply ext_of_mulVec_single
      intro k
      rw [← mulVec_mulVec, ← mulVec_mulVec, ← vecAt_basis v' k w, ← vecAt_coe, mat, mat,
        archEmbed_apply, archEmbed_apply, map_toMatrix_mulVec_vecAt, map_toMatrix_mulVec_vecAt,
        ← vecAt_coe]
      exact congrArg (fun x => vecAt v x w) (hW (v' k))

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix Topology MeasureTheory

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

section Form

variable {h : HermitianForm F E W} {v : Basis ι E W} {x₀ w₀ : W}

def heisForm (h : HermitianForm F E W) (v : Basis ι E W) (x₀ w₀ : W) :
    LinearMap.BilinForm ℝ (heisY h v x₀ w₀) :=
  LinearMap.mk₂ ℝ (fun y z => ∑ w, (hForm (gramAt h v w) ((y : InfinitePlace E → ι → ℂ) w)
      ((z : InfinitePlace E → ι → ℂ) w)).re)
    (fun y y' z => by
      simp only [Submodule.coe_add, Pi.add_apply, hForm_add_left, Complex.add_re,
        Finset.sum_add_distrib])
    (fun c y z => by
      simp only [Submodule.coe_smul, Pi.smul_apply, real_smul_vec, hForm_smul_left,
        Complex.conj_ofReal, Complex.re_ofReal_mul, smul_eq_mul, Finset.mul_sum])
    (fun y z z' => by
      simp only [Submodule.coe_add, Pi.add_apply, hForm_add_right, Complex.add_re,
        Finset.sum_add_distrib])
    (fun c y z => by
      simp only [Submodule.coe_smul, Pi.smul_apply, real_smul_vec, hForm_smul_right,
        Complex.re_ofReal_mul, smul_eq_mul, Finset.mul_sum])

omit [NumberField F] [IsTotallyReal F] [IsTotallyComplex E] [DecidableEq ι] in
theorem heisForm_apply (y z : heisY h v x₀ w₀) :
    heisForm h v x₀ w₀ y z = ∑ w, (hForm (gramAt h v w) ((y : InfinitePlace E → ι → ℂ) w)
      ((z : InfinitePlace E → ι → ℂ) w)).re := rfl

theorem heisForm_comm (hp : IsHyperbolicPair h x₀ w₀) (y z : heisY h v x₀ w₀) :
    heisForm h v x₀ w₀ y z = heisForm h v x₀ w₀ z y := by
  rw [heisForm_apply, heisForm_apply]
  refine Finset.sum_congr rfl fun w _ => ?_
  obtain ⟨hH, -⟩ := hyperbolic_at_place h v hp w
  rw [← hForm_conj hH, Complex.conj_re]

theorem heisForm_nondegenerate (hp : IsHyperbolicPair h x₀ w₀) :
    (heisForm h v x₀ w₀).Nondegenerate := by
  classical
  have left : ∀ y : heisY h v x₀ w₀, (∀ z, heisForm h v x₀ w₀ y z = 0) → y = 0 := by
    intro y hy
    apply Subtype.ext
    funext w
    change (y : InfinitePlace E → ι → ℂ) w = 0
    obtain ⟨hH, hd, ha, hb, hab⟩ := hyperbolic_at_place h v hp w
    have hba : hForm (gramAt h v w) (vecAt v w₀ w) (vecAt v x₀ w) = 1 := by
      rw [← hForm_conj hH, hab, map_one]
    apply eq_zero_of_hForm hd
    intro z
    set q := z - hForm (gramAt h v w) (vecAt v w₀ w) z • vecAt v x₀ w -
      hForm (gramAt h v w) (vecAt v x₀ w) z • vecAt v w₀ w with hq
    have hqa : hForm (gramAt h v w) (vecAt v x₀ w) q = 0 := by
      rw [hq]
      simp only [hForm_sub_right, hForm_smul_right, ha, hab]
      ring
    have hqb : hForm (gramAt h v w) (vecAt v w₀ w) q = 0 := by
      rw [hq]
      simp only [hForm_sub_right, hForm_smul_right, hb, hba]
      ring
    have key : ∀ c : ℂ, (hForm (gramAt h v w) ((y : InfinitePlace E → ι → ℂ) w) (c • q)).re = 0 := by
      intro c
      have hmem : (Pi.single w (c • q) : InfinitePlace E → ι → ℂ) ∈ heisY h v x₀ w₀ := by
        intro w'
        by_cases hw : w' = w
        · subst hw
          simp only [Pi.single_eq_same, hForm_smul_right, hqa, hqb, mul_zero, and_self]
        · simp only [Pi.single_eq_of_ne hw, hForm_zero_right, and_self]
      have := hy ⟨_, hmem⟩
      rw [heisForm_apply, Finset.sum_eq_single w] at this
      · simpa using this
      · intro w' _ hw
        simp [Pi.single_eq_of_ne hw, hForm_zero_right]
      · simp
    have h1 := key 1
    have h2 := key Complex.I
    rw [hForm_smul_right, one_mul] at h1
    rw [hForm_smul_right, Complex.I_mul_re, neg_eq_zero] at h2
    have hyq : hForm (gramAt h v w) ((y : InfinitePlace E → ι → ℂ) w) q = 0 := Complex.ext h1 h2
    have hya : hForm (gramAt h v w) ((y : InfinitePlace E → ι → ℂ) w) (vecAt v x₀ w) = 0 := by
      rw [← hForm_conj hH, (y.2 w).1, map_zero]
    have hyb : hForm (gramAt h v w) ((y : InfinitePlace E → ι → ℂ) w) (vecAt v w₀ w) = 0 := by
      rw [← hForm_conj hH, (y.2 w).2, map_zero]
    have hz : z = q + hForm (gramAt h v w) (vecAt v w₀ w) z • vecAt v x₀ w +
        hForm (gramAt h v w) (vecAt v x₀ w) z • vecAt v w₀ w := by
      rw [hq]
      abel
    rw [hz, hForm_add_right, hForm_add_right, hForm_smul_right, hForm_smul_right, hyq, hya, hyb]
    ring
  exact ⟨left, fun y hy => left y fun z => by rw [heisForm_comm hp]; exact hy z⟩

theorem heisForm_heisConjLin (g : archUnitary h v)
    (hg : g ∈ vecFixGroup h v x₀ ⊓ vecFixGroup h v w₀) (y z : heisY h v x₀ w₀) :
    heisForm h v x₀ w₀ (heisConjLin g hg y) (heisConjLin g hg z) = heisForm h v x₀ w₀ y z := by
  rw [heisForm_apply, heisForm_apply]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [heisConjLin_apply, heisConjLin_apply, hForm_mulVec_of_unitary _ (archUnitary_at_place g w)]

end Form

theorem UnipotentModulus.proof (h : HermitianForm F E W) (v : Basis ι E W) :
    UnipotentModulus.Statement h v := by
  intro x₀ w₀ hp μ _ g hg
  have : BorelSpace (unipRadical h v x₀) :=
    Subtype.borelSpace (unipRadical h v x₀ : Set (archUnitary h v))
  set φ := heisHomeo (v := v) hp with hφ
  set lam : Measure (HeisCoord h v x₀ w₀) :=
    (Measure.addHaar : Measure (heisY h v x₀ w₀)).prod volume with hlam
  set G := heisConjLin g hg with hG
  set c : unipRadical h v x₀ → unipRadical h v x₀ := fun n => φ ((G (φ.symm n).1, (φ.symm n).2))
    with hcdef
  have hc : ∀ n, ((c n : unipRadical h v x₀) : archUnitary h v) = g * n * g⁻¹ := by
    intro n
    conv_rhs => rw [← φ.apply_symm_apply n]
    exact (heisPoint_conj hp g hg _).symm
  have hGc : Continuous G := LinearMap.continuous_of_finiteDimensional G
  have hcm : Measurable c :=
    (φ.continuous.comp ((hGc.comp (continuous_fst.comp φ.symm.continuous)).prodMk
      (continuous_snd.comp φ.symm.continuous))).measurable
  have hmap : (fun n : unipRadical h v x₀ => g * (n : archUnitary h v) * g⁻¹) =
      Subtype.val ∘ c := by
    funext n
    exact (hc n).symm
  have hGm : MeasurePreserving G Measure.addHaar Measure.addHaar :=
    measurePreserving_of_preserves_bilin _ (heisForm h v x₀ w₀) (heisForm_nondegenerate hp) G
      (heisForm_heisConjLin g hg)
  have hC : MeasurePreserving (fun x => φ.symm (c (φ x))) lam lam := by
    have e : (fun x => φ.symm (c (φ x))) = Prod.map G id := by
      funext x
      simp only [hcdef, Homeomorph.symm_apply_apply, Prod.map, id]
    rw [e]
    exact hGm.prod (MeasurePreserving.id volume)
  have hL : ∀ n, MeasurePreserving (fun x => φ.symm (n * φ x)) lam lam := by
    intro n
    obtain ⟨p, rfl⟩ := φ.surjective n
    set f : heisY h v x₀ w₀ → InfinitePlace E → ℝ := fun y w =>
      (hForm (gramAt h v w) ((p.1 : InfinitePlace E → ι → ℂ) w)
        ((y : InfinitePlace E → ι → ℂ) w)).im with hf
    have e : (fun x => φ.symm (φ p * φ x)) = fun x => (p.1 + x.1, (p.2 - f x.1) + x.2) := by
      funext x
      rw [hφ, heisHomeo_apply, heisHomeo_apply, heisPoint_mul, ← heisHomeo_apply,
        Homeomorph.symm_apply_apply]
      refine Prod.ext rfl ?_
      simp only [hf]
      abel
    rw [e]
    have hfc : Continuous f := continuous_pi fun w => Complex.continuous_im.comp
      (continuous_hForm_right _ _ ((continuous_apply w).comp continuous_subtype_val))
    refine MeasurePreserving.skew_product (f := fun y => p.1 + y)
      (g := fun y t => (p.2 - f y) + t) (measurePreserving_add_left _ p.1) ?_
      (Filter.Eventually.of_forall fun y => (measurePreserving_add_left volume _).map_eq)
    exact ((continuous_const.sub (hfc.comp continuous_fst)).add continuous_snd).measurable
  rw [hmap, ← Measure.map_map continuous_subtype_val.measurable hcm,
    map_eq_of_measurePreserving_coordinates lam φ hL c hC μ]

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix Topology

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem UnipotentCocompact.proof (h : HermitianForm F E W) (v : Basis ι E W)
    (hP : UnipotentCoordProper.Statement h v) (hH : UnipotentHorizontal.Statement h v)
    (hC : UnipotentCentral.Statement h v) : UnipotentCocompact.Statement h v := by
  intro D La x₀ hLa hx₀ hne hiso
  obtain ⟨w₀, h1, h2⟩ := WittPartner.proof h x₀ hne hiso
  have hp : IsHyperbolicPair h x₀ w₀ := ⟨hiso, h2, h1⟩
  obtain ⟨K₁, hK₁, hred⟩ := hH D La x₀ w₀ hLa hx₀ hp
  obtain ⟨K, hK, hcen⟩ := hC D La x₀ w₀ hLa hx₀ hp K₁ hK₁
  refine ⟨{n | unipCoord h v x₀ w₀ n ∈ K}, hP x₀ w₀ hp K hK, fun n => ?_⟩
  obtain ⟨δ₁, hδ₁, t, ht⟩ := hred n
  obtain ⟨δ₂, hδ₂, hK'⟩ := hcen (δ₁ * n) ⟨t, ht⟩
  refine ⟨δ₂ * δ₁, ?_, ?_⟩
  · exact Subgroup.mul_mem _ hδ₂ hδ₁
  · change unipCoord h v x₀ w₀ (δ₂ * δ₁ * n) ∈ K
    rwa [mul_assoc]

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module
open scoped Pointwise

noncomputable section

namespace CongruenceLift

theorem exists_nsmul_mem {E W : Type*} [Field E] [NumberField E] [AddCommGroup W] [Module E W]
    {La : AddSubgroup W} (hLa : IsLattice E La) (w : W) : ∃ d : ℕ, 0 < d ∧ d • w ∈ La :=
  _root_.UpperTheory.Reformulated.B.ExistsNsmulMem.exists_nsmul_mem hLa w

theorem exists_congruence {V G : Type*} [AddCommGroup V] [Group G] [DistribMulAction G V]
    (L : AddSubgroup V) (hL : L.FG) (d : ℕ) (hd : 0 < d) :
    ∃ K : Subgroup (MulAction.stabilizer G L), K.index ≠ 0 ∧
      ∀ k ∈ K, ∀ y ∈ L, ∃ u ∈ L, d • u = (k : G) • y - y := by
  set S := MulAction.stabilizer G L
  have hS : ∀ (s : S) (y : V), y ∈ L → (s : G) • y ∈ L := fun s y hy => by
    have := AddSubgroup.smul_mem_pointwise_smul y (s : G) L hy
    rwa [MulAction.mem_stabilizer_iff.1 s.2] at this
  let f : S → L →+ L := fun s =>
    { toFun := fun y => ⟨(s : G) • (y : V), hS s y y.2⟩
      map_zero' := Subtype.ext (smul_zero _)
      map_add' := fun y z => Subtype.ext (smul_add _ _ _) }
  set N : AddSubgroup L := (nsmulAddMonoidHom (α := L) d).range
  have hN : ∀ s, N ≤ N.comap (f s) := by
    rintro s _ ⟨u, rfl⟩
    exact ⟨f s u, by simp [map_nsmul]⟩
  let _ : MulAction S (L ⧸ N) :=
    { smul := fun s q => QuotientAddGroup.map N N (f s) (hN s) q
      one_smul := fun q => QuotientAddGroup.induction_on q fun y => by
        change QuotientAddGroup.map N N (f 1) (hN 1) (y : L ⧸ N) = y
        rw [QuotientAddGroup.map_mk]
        congr 1
        exact Subtype.ext (one_smul G (y : V))
      mul_smul := fun s t q => QuotientAddGroup.induction_on q fun y => by
        change QuotientAddGroup.map N N (f (s * t)) (hN _) (y : L ⧸ N) =
          QuotientAddGroup.map N N (f s) (hN s) (QuotientAddGroup.map N N (f t) (hN t) y)
        rw [QuotientAddGroup.map_mk, QuotientAddGroup.map_mk, QuotientAddGroup.map_mk]
        congr 1
        exact Subtype.ext (mul_smul (s : G) (t : G) (y : V)) }
  have hfg : AddGroup.FG L := (AddGroup.fg_iff_addSubgroup_fg L).2 hL
  have hfin : Finite (L ⧸ N) := by
    refine AddCommGroup.finite_of_fg_isAddTorsion _ fun q => ?_
    refine QuotientAddGroup.induction_on q fun y => ?_
    rw [isOfFinAddOrder_iff_nsmul_eq_zero]
    refine ⟨d, hd, ?_⟩
    rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff]
    exact ⟨y, rfl⟩
  refine ⟨(MulAction.toPermHom S (L ⧸ N)).ker, Subgroup.FiniteIndex.index_ne_zero, ?_⟩
  intro k hk y hy
  have hq := DFunLike.congr_fun (MonoidHom.mem_ker.1 hk) ((⟨y, hy⟩ : L) : L ⧸ N)
  simp only [MulAction.toPermHom_apply, MulAction.toPerm_apply, Equiv.Perm.coe_one, id_eq] at hq
  change QuotientAddGroup.map N N (f k) (hN k) _ = _ at hq
  rw [QuotientAddGroup.map_mk, QuotientAddGroup.eq] at hq
  obtain ⟨u, hu⟩ := hq
  refine ⟨-(u : V), L.neg_mem u.2, ?_⟩
  have := congrArg Subtype.val hu
  simp only [nsmulAddMonoidHom_apply, AddSubgroup.coe_nsmul, AddSubgroup.coe_add,
    AddSubgroup.coe_neg] at this
  rw [smul_neg, this]
  change -(-((k : G) • y) + y) = (k : G) • y - y
  abel

end CongruenceLift

variable {F E : Type*} [Field F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W]

theorem CongruenceLift.proof [FiniteDimensional E W] (h : HermitianForm F E W) :
    CongruenceLift.Statement h := by
  intro D La x₀ w₀ hLa hx₀ hp h' hh'
  obtain ⟨d, hd, hdw⟩ := CongruenceLift.exists_nsmul_mem hLa.isLattice w₀
  set La' : AddSubgroup (hypComplement h x₀ w₀) := La.comap (hypComplement h x₀ w₀).subtype.toAddMonoidHom
  have dec : ∀ x ∈ La, h.toSesq (d • w₀) x • x₀ ∈ La ∧ (h.toSesq x₀ x * d) • w₀ ∈ La ∧
      d • x - h.toSesq (d • w₀) x • x₀ - (h.toSesq x₀ x * d) • w₀ =
        ((d • ComplementExtension.proj hp x : hypComplement h x₀ w₀) : W) := by
    intro x hx
    refine ⟨hLa.isLattice.smul_mem ⟨_, hLa.integral _ hdw x hx⟩ x₀ hx₀, ?_, ?_⟩
    · have := hLa.isLattice.smul_mem ⟨_, hLa.integral _ hx₀ x hx⟩ _ hdw
      rwa [← Nat.cast_smul_eq_nsmul E, smul_smul] at this
    · rw [Submodule.coe_smul_of_tower, ComplementExtension.proj_apply, map_nsmul,
        LinearMap.smul_apply]
      simp only [← Nat.cast_smul_eq_nsmul E, smul_eq_mul]
      module
  obtain ⟨D', hD'⟩ := ComplementLattice.proof h x₀ w₀ hp h' hh' D d hd
  have hLa' : IsDIntegral h' D' La' := hD' La hLa fun x hx =>
    ⟨_, (dec x hx).1, _, (dec x hx).2.1, by rw [(dec x hx).2.2]; exact Submodule.coe_mem _⟩
  obtain ⟨K, hK, hcong⟩ : ∃ K : Subgroup (latticeStab h' La'), K.index ≠ 0 ∧
      ∀ k ∈ K, ∀ y ∈ La', ∃ u ∈ La', d • u = (k : h'.unitaryGroup) • y - y :=
    CongruenceLift.exists_congruence (G := h'.unitaryGroup) La' hLa'.isLattice.fg d hd
  have key : ∀ k ∈ K, ∀ γ : h.unitaryGroup, γ • x₀ = x₀ → γ • w₀ = w₀ →
      (∀ x : hypComplement h x₀ w₀, γ • (x : W) = ((((k : latticeStab h' La') : h'.unitaryGroup) • x : hypComplement h x₀ w₀) : W)) →
      ∀ x ∈ La, γ • x ∈ La := by
    intro k hk γ h1 h2 h3 x hx
    obtain ⟨hA, hB, hC⟩ := dec x hx
    set y : hypComplement h x₀ w₀ := d • ComplementExtension.proj hp x
    have hy : y ∈ La' := by
      change (y : W) ∈ La
      rw [← hC]
      exact La.sub_mem (La.sub_mem (La.nsmul_mem hx d) hA) hB
    obtain ⟨u, hu, hdu⟩ := hcong k hk y hy
    have hx' : d • x = h.toSesq (d • w₀) x • x₀ + (y : W) + (h.toSesq x₀ x * d) • w₀ := by
      rw [← hC]
      abel
    have hγ : d • (γ • x) = d • (x + (u : W)) := by
      have hdu' : (((k : latticeStab h' La') : h'.unitaryGroup) • y : hypComplement h x₀ w₀) = (y : W) + d • (u : W) := by
        rw [← Submodule.coe_smul_of_tower, hdu]
        simp
      rw [← smul_comm, hx', smul_add, smul_add, smul_comm γ (h.toSesq (d • w₀) x),
        smul_comm γ (h.toSesq x₀ x * d), h1, h2, h3, hdu', smul_add, hx']
      abel
    have hne : (d : E) ≠ 0 := Nat.cast_ne_zero.2 hd.ne'
    have := smul_right_injective W hne (by simpa only [Nat.cast_smul_eq_nsmul] using hγ)
    rw [this]
    exact La.add_mem hx hu
  refine ⟨D', La', K.map (latticeStab h' La').subtype, hLa', Subgroup.map_subtype_le K, ?_, ?_⟩
  · rw [Subgroup.relIndex, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective (latticeStab h' La').subtype_injective]
    exact hK
  · rintro _ ⟨k, hk, rfl⟩ γ h1 h2 h3
    refine MulAction.mem_stabilizer_iff.2 (le_antisymm ?_ ?_)
    · intro z hz
      obtain ⟨x, hx, rfl⟩ := (AddSubgroup.mem_smul_pointwise_iff_exists z γ La).1 hz
      exact key k hk γ h1 h2 h3 x hx
    · intro z hz
      refine AddSubgroup.mem_pointwise_smul_iff_inv_smul_mem.2 ?_
      refine key k⁻¹ (K.inv_mem hk) γ⁻¹ (inv_smul_eq_iff.2 h1.symm) (inv_smul_eq_iff.2 h2.symm)
        (fun x => inv_smul_eq_iff.2 ?_) z hz
      rw [h3]
      simp

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section
namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix Topology MeasureTheory
open scoped Pointwise ComplexOrder ENNReal NumberField.AdeleRing

noncomputable section

universe u

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]

variable
    (hTE : ∀ (W : Type u) [AddCommGroup W] [Module E W] [FiniteDimensional E W]
      (h : HermitianForm F E W) (n : ℕ) (v : Basis (Fin n) E W), TorusEmbedding.Statement h v)
    (hLE : ∀ (W : Type u) [AddCommGroup W] [Module E W] [FiniteDimensional E W]
      (h : HermitianForm F E W) (n : ℕ) (v : Basis (Fin n) E W), LineEigenvalue.Statement h v)
    (hTM : ∀ (W : Type u) [AddCommGroup W] [Module E W] [FiniteDimensional E W]
      (h : HermitianForm F E W) (n : ℕ) (v : Basis (Fin n) E W), TorusModulus.Statement h v)
    (hSH : ∀ (W : Type u) [AddCommGroup W] [Module E W] [FiniteDimensional E W]
      (h : HermitianForm F E W) (n : ℕ) (v : Basis (Fin n) E W), SemidirectHaar.Statement (archUnitary h v) (InfinitePlace E → ℂˣ))
    (hUI : UnitsInvHaar.Statement (InfinitePlace E))
    (hCP : ∀ (W : Type u) [AddCommGroup W] [Module E W] [FiniteDimensional E W]
      (h : HermitianForm F E W) (n : ℕ) (v : Basis (Fin n) E W), UnipotentCoordProper.Statement h v)
    (hUH : ∀ (W : Type u) [AddCommGroup W] [Module E W] [FiniteDimensional E W]
      (h : HermitianForm F E W) (n : ℕ) (v : Basis (Fin n) E W), UnipotentHorizontal.Statement h v)
    (hUZ : ∀ (W : Type u) [AddCommGroup W] [Module E W] [FiniteDimensional E W]
      (h : HermitianForm F E W) (n : ℕ) (v : Basis (Fin n) E W), UnipotentCentral.Statement h v)

variable {W : Type u} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (h : HermitianForm F E W) (v : Basis ι E W)
variable (hTE' : TorusEmbedding.Statement h v) (hLE' : LineEigenvalue.Statement h v)
    (hTM' : TorusModulus.Statement h v)
    (hSH' : SemidirectHaar.Statement (archUnitary h v) (InfinitePlace E → ℂˣ))
    (hCP' : UnipotentCoordProper.Statement h v) (hUH' : UnipotentHorizontal.Statement h v)
    (hUZ' : UnipotentCentral.Statement h v)

include hTE hLE hTM hSH hUI hCP hUH hUZ hTE' hLE' hTM' hSH' hCP' hUH' hUZ'

theorem UnfoldingIntegral.of_remaining : UnfoldingIntegral.Statement h v :=
  UnfoldingIntegral.of_open
    (fun _ _ _ _ h _ v => ArchUnimodular.proof h v)
    (fun _ _ _ _ h _ v => MajorantStabCompact.proof h v)
    (fun W _ _ _ h n v => LineStabHaar.proof h v (WittPartner.full h) (VecAtNeZero.full v)
      (hTE W h n v) (hLE W h n v) (hTM W h n v) (hSH W h n v) hUI)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ => SemidirectCovering.proof _ _ _)
    (fun _ _ _ _ h _ v => StabilizerLevi.proof h v)
    (fun _ _ _ _ h _ v => UnipotentModulus.proof h v)
    (fun W _ _ _ h n v => UnipotentCocompact.proof h v (hCP W h n v) (hUH W h n v) (hUZ W h n v))
    (fun _ _ _ _ h => CongruenceLift.proof h)
    h v (fun _ _ _ _ _ => SemidirectCovering.proof _ _ _) (StabilizerLevi.proof h v)
    (UnipotentModulus.proof h v) (UnipotentCocompact.proof h v hCP' hUH' hUZ')
    (ArchUnimodular.proof h v) (MajorantStabCompact.proof h v)
    (LineStabHaar.proof h v (WittPartner.full h) (VecAtNeZero.full v) hTE' hLE' hTM' hSH' hUI)

theorem ScalingLaw.of_remaining : ScalingLaw.Statement h v :=
  ScalingLaw.of_open
    (fun _ _ _ _ h _ v => ArchUnimodular.proof h v)
    (fun _ _ _ _ h _ v => MajorantStabCompact.proof h v)
    (fun W _ _ _ h n v => LineStabHaar.proof h v (WittPartner.full h) (VecAtNeZero.full v)
      (hTE W h n v) (hLE W h n v) (hTM W h n v) (hSH W h n v) hUI)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ => SemidirectCovering.proof _ _ _)
    (fun _ _ _ _ h _ v => StabilizerLevi.proof h v)
    (fun _ _ _ _ h _ v => UnipotentModulus.proof h v)
    (fun W _ _ _ h n v => UnipotentCocompact.proof h v (hCP W h n v) (hUH W h n v) (hUZ W h n v))
    (fun _ _ _ _ h => CongruenceLift.proof h)
    h v (fun _ _ _ _ _ => SemidirectCovering.proof _ _ _) (StabilizerLevi.proof h v)
    (UnipotentModulus.proof h v) (UnipotentCocompact.proof h v hCP' hUH' hUZ')
    (ArchUnimodular.proof h v) (MajorantStabCompact.proof h v)
    (LineStabHaar.proof h v (WittPartner.full h) (VecAtNeZero.full v) hTE' hLE' hTM' hSH' hUI)

theorem ArithmeticCovolumeFinite.of_remaining : ArithmeticCovolumeFinite.Statement h v :=
  ArithmeticCovolumeFinite.of_open
    (fun _ _ _ _ h _ v => ArchUnimodular.proof h v)
    (fun _ _ _ _ h _ v => MajorantStabCompact.proof h v)
    (fun W _ _ _ h n v => LineStabHaar.proof h v (WittPartner.full h) (VecAtNeZero.full v)
      (hTE W h n v) (hLE W h n v) (hTM W h n v) (hSH W h n v) hUI)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ => SemidirectCovering.proof _ _ _)
    (fun _ _ _ _ h _ v => StabilizerLevi.proof h v)
    (fun _ _ _ _ h _ v => UnipotentModulus.proof h v)
    (fun W _ _ _ h n v => UnipotentCocompact.proof h v (hCP W h n v) (hUH W h n v) (hUZ W h n v))
    (fun _ _ _ _ h => CongruenceLift.proof h)
    h v (fun _ _ _ _ _ => SemidirectCovering.proof _ _ _) (StabilizerLevi.proof h v)
    (UnipotentModulus.proof h v) (UnipotentCocompact.proof h v hCP' hUH' hUZ')
    (ArchUnimodular.proof h v) (MajorantStabCompact.proof h v)
    (LineStabHaar.proof h v (WittPartner.full h) (VecAtNeZero.full v) hTE' hLE' hTM' hSH' hUI)

theorem AdelicCovolumeFinite.of_remaining : AdelicCovolumeFinite.Statement h v :=
  AdelicCovolumeFinite.of_open
    (fun _ _ _ _ h _ v => ArchUnimodular.proof h v)
    (fun _ _ _ _ h _ v => MajorantStabCompact.proof h v)
    (fun W _ _ _ h n v => LineStabHaar.proof h v (WittPartner.full h) (VecAtNeZero.full v)
      (hTE W h n v) (hLE W h n v) (hTM W h n v) (hSH W h n v) hUI)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ => SemidirectCovering.proof _ _ _)
    (fun _ _ _ _ h _ v => StabilizerLevi.proof h v)
    (fun _ _ _ _ h _ v => UnipotentModulus.proof h v)
    (fun W _ _ _ h n v => UnipotentCocompact.proof h v (hCP W h n v) (hUH W h n v) (hUZ W h n v))
    (fun _ _ _ _ h => CongruenceLift.proof h)
    h v (fun _ _ _ _ _ => SemidirectCovering.proof _ _ _) (StabilizerLevi.proof h v)
    (UnipotentModulus.proof h v) (UnipotentCocompact.proof h v hCP' hUH' hUZ')
    (ArchUnimodular.proof h v) (MajorantStabCompact.proof h v)
    (LineStabHaar.proof h v (WittPartner.full h) (VecAtNeZero.full v) hTE' hLE' hTM' hSH' hUI)

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end
