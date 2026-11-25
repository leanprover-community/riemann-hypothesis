module

public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPairingStdP
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Development.AbelianVarietyTheory.Definitions.Foundations.ConstTermOnMulLeftOfNormalizer
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActsRhoOfAtInf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodinger
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIntegralPointsIndicatorIsVacuum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryAdelicSchwartzRestFunction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarOfIsCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerPreservesSchwartzBruhat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace GlobalTheory.ThK

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.Doubling (absE absEv unitFin ideleAt)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

section Parts

variable {M : Type} [AddCommGroup M] [Module (AF F) M]

def partFin (v : Pl F) (z : M) : M := GlobalTheory.LatVac.liftV v 1 • z

variable (F) in
def partInf (z : M) : M := realAd F 1 • z

theorem partFin_of_at {v : Pl F} {z : M} (hz : At (evFin F v) z) : partFin v z = z := by
  have h := hz (1 - GlobalTheory.LatVac.liftV v 1) (by rw [map_sub, map_one, GlobalTheory.LatVac.evFin_liftV, sub_self])
  rw [sub_smul, one_smul, sub_eq_zero] at h
  exact h.symm

theorem evI_realAd_one : evI F (realAd F 1) = 1 :=
  ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply _).trans (map_one _)

theorem at_partInf (z : M) : At (evI F) (partInf F z) := fun u hu => by
  have h1 : u.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (by rw [map_zero]; exact hu)
  have h : u * realAd F 1 = 0 := Prod.ext (show u.1 * _ = 0 by rw [h1, zero_mul]) (show u.2 * 0 = 0 from mul_zero _)
  rw [partInf, smul_smul, h, zero_smul]

theorem partInf_of_at {z : M} (hz : At (evI F) z) : partInf F z = z := by
  have h := hz (1 - realAd F 1) (by
    rw [GlobalTheory.ArchUniq.evI_eq_evIHom, map_sub, map_one, ← GlobalTheory.ArchUniq.evI_eq_evIHom, evI_realAd_one, sub_self])
  rw [sub_smul, one_smul, sub_eq_zero] at h
  exact h.symm

end Parts

section Groups

variable {R : Type} [Zero R] {n : ℕ}

variable (σ) in
def UAtSub (X : Spc F E n) (ev : AF F → R) : Subgroup (UA σ X.J) where
  carrier := UAt σ X ev
  one_mem' := fun u _ => by rw [GlobalTheory.StabHaar.mat_one, sub_self, smul_zero]
  mul_mem' := by
    intro g h hg hh u hu
    have e : mat (g * h) - 1 = (mat g - 1) * mat h + (mat h - 1) := by
      rw [GlobalTheory.StabHaar.mat_mul, Matrix.sub_mul, Matrix.one_mul]; abel
    rw [e, smul_add, ← Matrix.smul_mul, hg u hu, hh u hu, Matrix.zero_mul, add_zero]
  inv_mem' := by
    intro g hg u hu
    have e : mat g⁻¹ - 1 = -((mat g - 1) * mat g⁻¹) := by
      rw [Matrix.sub_mul, Matrix.one_mul, GlobalTheory.StabHaar.mat_mul_inv]; abel
    rw [e, smul_neg, ← Matrix.smul_mul, hg u hu, Matrix.zero_mul, neg_zero]

def KAt {X : Spc F E n} (K : Subgroup (UA σ X.J)) (ev : AF F → R) : Subgroup (UA σ X.J) := K ⊓ UAtSub σ X ev

variable (E) in
def idelesAt (ev : AF F → R) : Subgroup (AE F E)ˣ where
  carrier := {l | At ev ((l : AE F E) - 1)}
  one_mem' := fun u _ => by rw [Units.val_one, sub_self, smul_zero]
  mul_mem' := by
    intro g h hg hh u hu
    have e : ((g * h : (AE F E)ˣ) : AE F E) - 1 = ((g : AE F E) - 1) * h + (h - 1) := by
      rw [Units.val_mul]; ring
    rw [e, smul_add, ← smul_mul_assoc, hg u hu, hh u hu, zero_mul, add_zero]
  inv_mem' := by
    intro g hg u hu
    have e : ((g⁻¹ : (AE F E)ˣ) : AE F E) - 1 = -(((g : AE F E) - 1) * (g⁻¹ : (AE F E)ˣ)) := by
      rw [sub_mul, Units.mul_inv]; ring
    rw [e, smul_neg, ← smul_mul_assoc, hg u hu, zero_mul, neg_zero]

variable (E) in
def unitsAt (v : Pl F) : Subgroup (AE F E)ˣ :=
  idelesAt E (evFin F v) ⊓ (intLoc F E v).toSubmonoid.units.comap (unitFin F E v)

theorem mem_unitsAt {v : Pl F} {l : (AE F E)ˣ} : l ∈ unitsAt E v ↔ l ∈ idelesAt E (evFin F v) ∧
    compFin F E v l ∈ intLoc F E v ∧ compFin F E v (l⁻¹ : (AE F E)ˣ) ∈ intLoc F E v := Iff.rfl

omit [NumberField E] in
theorem compFin_smul (v : Pl F) (a : AF F) (z : AE F E) : compFin F E v (a • z) = evFin F v a • compFin F E v z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul b x => exact congrArg (· ⊗ₜ[F] x) (map_mul (evFin F v) a b)
  | add x y hx hy => rw [smul_add, map_add (f := _), map_add (f := _), hx, hy, smul_add]

omit [NumberField E] in
theorem compInf_smul (w : InfinitePlace F) (a : AF F) (z : AE F E) :
    compInf F E w (a • z) = evInf F w a • compInf F E w z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul b x => exact congrArg (· ⊗ₜ[F] x) (map_mul (evInf F w) a b)
  | add x y hx hy => rw [smul_add, map_add (f := _), map_add (f := _), hx, hy, smul_add]

theorem at_evFin_iff {v : Pl F} {z : AE F E} : At (evFin F v) z ↔
    (∀ w, compInf F E w z = 0) ∧ ∀ w, w ≠ v → compFin F E w z = 0 := by
  constructor
  · intro hz
    rw [← partFin_of_at hz, partFin]
    refine ⟨fun w => ?_, fun w hw => ?_⟩
    · rw [compInf_smul, show evInf F w (GlobalTheory.LatVac.liftV v 1) = 0 from rfl, zero_smul]
    · rw [compFin_smul, show evFin F w (GlobalTheory.LatVac.liftV v 1) = 0 from evalV_singleFin_ne hw 1, zero_smul]
  · rintro ⟨h1, h2⟩ u hu
    refine GlobalTheory.Doubling.adele_ext (fun w => ?_) fun w => ?_
    · rw [compInf_smul, h1, smul_zero, map_zero]
    · rw [compFin_smul, map_zero]
      by_cases hw : w = v
      · subst hw; rw [hu, zero_smul]
      · rw [h2 w hw, smul_zero]

theorem at_evI_iff {z : AE F E} : At (evI F) z ↔ ∀ w, compFin F E w z = 0 := by
  constructor
  · intro hz w
    rw [← partInf_of_at hz, partInf, compFin_smul, show evFin F w (realAd F 1) = 0 from map_zero (evalV F w), zero_smul]
  · intro h u hu
    have h1 : u.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (by rw [map_zero]; exact hu)
    refine GlobalTheory.Doubling.adele_ext (fun w => ?_) fun w => ?_
    · rw [compInf_smul, map_zero, show evInf F w u = 0 from congrFun h1 w, zero_smul]
    · rw [compFin_smul, h, smul_zero, map_zero]

theorem ideleAt_mem (v : Pl F) (x : (Fv F v ⊗[F] E)ˣ) : ideleAt F E v x ∈ idelesAt E (evFin F v) := by
  refine at_evFin_iff.2 ⟨fun w => ?_, fun w hw => ?_⟩
  · rw [map_sub, map_one, sub_eq_zero]
    exact congrArg Units.val (GlobalTheory.Doubling.unitInf_ideleAt w v x)
  · rw [map_sub, map_one, sub_eq_zero]
    exact congrArg Units.val (GlobalTheory.Doubling.unitFin_ideleAt_ne hw x)

theorem ideleAt_unitFin {v : Pl F} {l : (AE F E)ˣ} (hl : l ∈ idelesAt E (evFin F v)) :
    ideleAt F E v (unitFin F E v l) = l := by
  obtain ⟨h1, h2⟩ := at_evFin_iff.1 hl
  refine GlobalTheory.Doubling.idele_ext (fun w => ?_) fun w => ?_
  · rw [GlobalTheory.Doubling.unitInf_ideleAt]
    have := h1 w
    rw [map_sub, map_one, sub_eq_zero] at this
    exact Units.ext this.symm
  · by_cases hw : w = v
    · subst hw; rw [GlobalTheory.Doubling.unitFin_ideleAt_self]
    · rw [GlobalTheory.Doubling.unitFin_ideleAt_ne hw]
      have := h2 w hw
      rw [map_sub, map_one, sub_eq_zero] at this
      exact Units.ext this.symm

variable (E) in
def idelesAtEquiv (v : Pl F) : idelesAt E (evFin F v) ≃ₜ* (Fv F v ⊗[F] E)ˣ where
  toFun l := unitFin F E v l.1
  invFun x := ⟨ideleAt F E v x, ideleAt_mem v x⟩
  left_inv l := Subtype.ext (ideleAt_unitFin l.2)
  right_inv x := GlobalTheory.Doubling.unitFin_ideleAt_self v x
  map_mul' a b := map_mul (unitFin F E v) a.1 b.1
  continuous_toFun := (GlobalTheory.Doubling.continuous_unitFin v).comp continuous_subtype_val
  continuous_invFun := (GlobalTheory.Doubling.continuous_ideleAt v).subtype_mk _

theorem isCompact_isOpen_intLoc (v : Pl F) :
    IsCompact (intLoc F E v : Set (Fv F v ⊗[F] E)) ∧ IsOpen (intLoc F E v : Set (Fv F v ⊗[F] E)) := by
  classical
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (Fv F v ⊗[F] E) := GlobalTheory.Doubling.isTopologicalRing_tens
  let b := integralBasis E
  let φ : (Module.Free.ChooseBasisIndex ℤ (𝓞 E) → Fv F v) →ₗ[Fv F v] Fv F v ⊗[F] E :=
    Fintype.linearCombination (Fv F v) fun i => (1 : Fv F v) ⊗ₜ[F] b i
  have hφ : ∀ a, φ a = ∑ i, a i ⊗ₜ[F] b i := fun a => by
    simp only [φ, Fintype.linearCombination_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have hq : ∀ (c : ℚ) (a : Fv F v) (x : E), a ⊗ₜ[F] (c • x) = ((c : Fv F v) * a) ⊗ₜ[F] x := fun c a x => by
    rw [show c • x = (c : F) • x by rw [Rat.cast_smul_eq_qsmul], ← TensorProduct.smul_tmul, Algebra.smul_def, map_ratCast]
  have hsurj : Function.Surjective φ := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => exact ⟨0, map_zero _⟩
    | tmul a x =>
      refine ⟨fun i => (b.repr x i : Fv F v) * a, ?_⟩
      rw [hφ]
      conv_rhs => rw [← b.sum_repr x, TensorProduct.tmul_sum]
      exact Finset.sum_congr rfl fun i _ => (hq _ _ _).symm
    | add x y hx hy =>
      obtain ⟨a, rfl⟩ := hx
      obtain ⟨c, rfl⟩ := hy
      exact ⟨a + c, map_add _ _ _⟩
  have himg : (intLoc F E v : Set (Fv F v ⊗[F] E)) =
      φ '' Set.univ.pi fun _ => (v.adicCompletionIntegers F : Set (Fv F v)) := by
    ext z
    constructor
    · refine intLoc_induction (p := fun z => z ∈ φ '' Set.univ.pi fun _ => (v.adicCompletionIntegers F : Set (Fv F v)))
        (fun a ha x => ?_) ⟨0, fun _ _ => zero_mem _, map_zero _⟩ ?_ ?_
      · refine ⟨fun i => (RingOfIntegers.basis E).repr x i • a, fun i _ => zsmul_mem ha _, ?_⟩
        rw [hφ]
        conv_rhs => rw [← b.sum_repr (x : E), TensorProduct.tmul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hq, show b.repr (x : E) i = algebraMap ℤ ℚ ((RingOfIntegers.basis E).repr x i) from
          integralBasis_repr_apply E x i]
        simp
      · rintro _ _ ⟨a, ha, rfl⟩ ⟨c, hc, rfl⟩
        exact ⟨a + c, fun i hi => add_mem (ha i hi) (hc i hi), map_add _ _ _⟩
      · rintro _ ⟨a, ha, rfl⟩
        exact ⟨-a, fun i hi => neg_mem (ha i hi), map_neg _ _⟩
    · rintro ⟨a, ha, rfl⟩
      rw [hφ]
      refine sum_mem fun i _ => ?_
      rw [show b i = ((RingOfIntegers.basis E i : 𝓞 E) : E) from integralBasis_apply E i]
      exact tmul_mem_intLoc (ha i (Set.mem_univ i)) _
  have hO : IsOpen (v.adicCompletionIntegers F : Set (Fv F v)) := Valued.isOpen_valuationSubring _
  have hC : IsCompact (v.adicCompletionIntegers F : Set (Fv F v)) :=
    isCompact_iff_compactSpace.2 (GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F v)
  rw [himg]
  exact ⟨(isCompact_univ_pi fun _ => hC).image (IsModuleTopology.continuous_of_linearMap φ),
    (IsModuleTopology.isOpenQuotientMap_of_surjective hsurj).isOpenMap _ (isOpen_set_pi Set.finite_univ fun _ _ => hO)⟩

theorem isCompact_isOpen_unitsAt (v : Pl F) :
    IsCompact {l : idelesAt E (evFin F v) | l.1 ∈ unitsAt E v} ∧ IsOpen {l : idelesAt E (evFin F v) | l.1 ∈ unitsAt E v} := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsTopologicalRing (Fv F v ⊗[F] E) := GlobalTheory.Doubling.isTopologicalRing_tens
  haveI : T2Space (Fv F v ⊗[F] E) := GlobalTheory.Doubling.t2Space_tensorProduct_finiteExtension
  have e : {l : idelesAt E (evFin F v) | l.1 ∈ unitsAt E v} =
      (idelesAtEquiv E v).toHomeomorph ⁻¹' ((intLoc F E v).toSubmonoid.units : Set _) := by
    ext l
    exact ⟨fun h => h.2, fun h => ⟨l.2, h⟩⟩
  rw [e]
  exact ⟨(Homeomorph.isCompact_preimage _).2 (Submonoid.units_isCompact (isCompact_isOpen_intLoc v).1),
    (Submonoid.isOpen_units (isCompact_isOpen_intLoc v).2).preimage (Homeomorph.continuous _)⟩

end Groups

section Haar

variable {R : Type} [Zero R] {n : ℕ} {X : Spc F E n}

def IsNormK (K : Subgroup (UA σ X.J)) (ev : AF F → R) (μ : Measure (KAt K ev)) : Prop :=
  μ.IsHaarMeasure ∧ μ Set.univ = 1

variable (E) in
def IsNormE (v : Pl F) (μ : Measure (idelesAt E (evFin F v))) : Prop :=
  μ.IsHaarMeasure ∧ μ {l | l.1 ∈ unitsAt E v} = 1

theorem absE_of_mem_unitsAt {v : Pl F} {l : (AE F E)ˣ} (hl : l ∈ unitsAt E v) : absE F E l = 1 := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsTopologicalRing (AE F E) := GlobalTheory.Doubling.isTopologicalRing_tens
  have hb : IsCompact (absE F E '' (Subtype.val '' {l : idelesAt E (evFin F v) | l.1 ∈ unitsAt E v})) :=
    ((isCompact_isOpen_unitsAt v).1.image continuous_subtype_val).image GlobalTheory.Doubling.continuous_absE
  obtain ⟨C, hC⟩ := hb.bddAbove
  have key : ∀ m ∈ unitsAt E v, absE F E m ≤ 1 := fun m hm => by
    by_contra h
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt C (not_le.1 h)
    have hk' : m ^ k ∈ unitsAt E v := pow_mem hm k
    exact not_le.2 hk (by rw [← map_pow]; exact hC ⟨_, ⟨⟨_, hk'.1⟩, hk', rfl⟩, rfl⟩)
  refine le_antisymm (key l hl) ?_
  have h1 := key _ (inv_mem hl)
  calc (1 : ℝ≥0) = absE F E l * absE F E l⁻¹ := by rw [← map_mul, mul_inv_cancel, map_one]
    _ ≤ absE F E l * 1 := by gcongr
    _ = _ := mul_one _

end Haar

section Ops

variable {κ : Type} [Fintype κ]

open Classical in
def locOp (v : Pl F) (T : ((κ → AF F) → ℂ) → ((κ → AF F) → ℂ)) (φ : (κ → Fv F v) → ℂ) : (κ → Fv F v) → ℂ :=
  if h : ∃ φ₁, φ₁ ∈ SB (κ → Fv F v) ∧ Acts (evFin F v) T φ φ₁ then h.choose else 0

open Classical in
def locOpInf (T : ((κ → AF F) → ℂ) → ((κ → AF F) → ℂ)) (f : SInf F κ) : SInf F κ :=
  if h : ∃ f₁ : SInf F κ, Acts (evI F) T f f₁ then h.choose else 0

variable (F κ) in
theorem exists_rest_inf : ∃ r : ((κ → AF F) → ℂ), r 0 ≠ 0 ∧ ∀ f : SInf F κ, Rest (evI F) f r := by
  let φ : ∀ w : Pl F, (κ → Fv F w) → ℂ := fun w => Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1
  refine ⟨fun x => ∏ᶠ w, φ w fun i => evFin F w (x i), ?_, fun f => ⟨fun x z hz => ?_, ?_⟩⟩
  · beta_reduce
    rw [finprod_eq_one_of_forall_eq_one fun w => ?_]
    · exact one_ne_zero
    · simp only [φ, Pi.zero_apply, map_zero]
      rw [Set.indicator_of_mem (by intro i; exact zero_mem _)]
      rfl
  · have h : ∀ w i, evFin F w (z i) = 0 := fun w i => by
      rw [← partInf_of_at hz, partInf, Pi.smul_apply, smul_eq_mul, map_mul,
        show evFin F w (realAd F 1) = 0 from map_zero (evalV F w), zero_mul]
    simp only [Pi.add_apply, map_add (f := _), h, add_zero]
  · exact GlobalTheory.TensUniq.pure_mem_schA f φ (fun w => GlobalTheory.StdVacuum.indicator_mem_SB w) (Eventually.of_forall fun _ => rfl)

end Ops

section Cone

variable {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d}

variable (B : Base F E) (M : Model σ X W) (om : Rep σ X W)

section Fin

variable (v : Pl F) (ev : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Fin n₁ × Fin d₁ → Fv F v) → ℂ)
  (K : Subgroup (UA σ X.J)) (μK : Measure (KAt K (evFin F v))) (μ : Measure (idelesAt E (evFin F v)))
  (u : (AE F E)ˣ → Matrix (Fin n) (Fin d) (AE F E)) (ν : Chr F E) (z : ℕ)

def coneFinInt (φ : (Fin n × Fin d → Fv F v) → ℂ) (k : UA σ X.J) (l : (AE F E)ˣ) (y : Fin n₁ × Fin d₁ → Fv F v) : ℂ :=
  ev (locOp v (M.co.rho B.ψ (partFin v (u l))) (locOp v (om (k, 1)) φ)) y * (ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ z

def coneFin (φ : (Fin n × Fin d → Fv F v) → ℂ) : (Fin n₁ × Fin d₁ → Fv F v) → ℂ :=
  fun y => ∫ k, ∫ l, coneFinInt B M om v ev u ν z φ k.1 l.1 y ∂μ ∂μK

variable {B M om v ev K μK μ u ν z}

end Fin

section Inf

variable (ei : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n₁ × Fin d₁))
  (K : Subgroup (UA σ X.J)) (μK : Measure (KAt K (evI F))) (μ : Measure (idelesAt E (evI F)))
  (u : (AE F E)ˣ → Matrix (Fin n) (Fin d) (AE F E)) (ν : Chr F E) (z : ℕ)

def coneInfInt (f : SInf F (Fin n × Fin d)) (k : UA σ X.J) (l : (AE F E)ˣ) : SInf F (Fin n₁ × Fin d₁) :=
  ((ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ z) • ei (locOpInf (M.co.rho B.ψ (partInf F (u l))) (locOpInf (om (k, 1)) f))

def coneInfFun (f : SInf F (Fin n × Fin d)) : (Fin n₁ × Fin d₁ → mixedEmbedding.mixedSpace F) → ℂ :=
  fun y => ∫ k, ∫ l, coneInfInt B M om ei u ν z f k.1 l.1 y ∂μ ∂μK

open Classical in
def coneInf (f : SInf F (Fin n × Fin d)) : SInf F (Fin n₁ × Fin d₁) :=
  if h : ∃ g : SInf F (Fin n₁ × Fin d₁), ⇑g = coneInfFun B M om ei K μK μ u ν z f then h.choose else 0

variable {B M om ei K μK μ u ν z}

end Inf

end Cone

end GlobalTheory.ThK

end
