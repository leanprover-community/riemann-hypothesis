module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DefiniteBound

@[expose] public section

noncomputable section

namespace GlobalTheory.SUVol

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology GlobalTheory.AdLat GlobalTheory.UCls ReciprocityTheory.ChartRestriction.G.FD
open scoped ENNReal NNReal

section General

variable {ι : Type} [Fintype ι] {r : ℕ}

def tanBall (ι : Type) (r : ℕ) (ε : ℝ) : Set (ι → Fin r → Fin r → ℂ) := {X | ∀ τ a b, ‖X τ a b‖ < ε}

def grpBall (H : Subgroup (ι → GL (Fin r) ℂ)) (ε : ℝ) : Set H :=
  {g | ∀ τ a b, ‖(g.1 τ : Matrix (Fin r) (Fin r) ℂ) a b - (1 : Matrix (Fin r) (Fin r) ℂ) a b‖ < ε}

def HasDensityOne (H : Subgroup (ι → GL (Fin r) ℂ)) [MeasurableSpace H] (μ : Measure H)
    (ν : Measure (ι → Fin r → Fin r → ℂ)) : Prop :=
  Tendsto (fun ε : ℝ => μ (grpBall H ε) / ν (tanBall ι r ε)) (𝓝[>] 0) (𝓝 1)

def tangentHaar (H : Subgroup (ι → GL (Fin r) ℂ)) [LocallyCompactSpace H] [MeasurableSpace H] [BorelSpace H]
    (ν : Measure (ι → Fin r → Fin r → ℂ)) : Measure H :=
  limsup (fun ε : ℝ => ν (tanBall ι r ε) / (Measure.haar : Measure H) (grpBall H ε)) (𝓝[>] 0) •
    (Measure.haar : Measure H)

instance (H : Subgroup (ι → GL (Fin r) ℂ)) [LocallyCompactSpace H] [MeasurableSpace H] [BorelSpace H]
    (ν : Measure (ι → Fin r → Fin r → ℂ)) : (tangentHaar H ν).IsMulLeftInvariant := by
  unfold tangentHaar; infer_instance

end General

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def realSU (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) : Subgroup (Ψ → GL (Fin r) ℂ) where
  carrier := {g | ∀ τ : Ψ, (g τ : Matrix (Fin r) (Fin r) ℂ).det = 1 ∧ ∀ u w,
    hermC τ.1 G ((g τ : Matrix (Fin r) (Fin r) ℂ) *ᵥ u) ((g τ : Matrix (Fin r) (Fin r) ℂ) *ᵥ w) = hermC τ.1 G u w}
  one_mem' τ := by simp
  mul_mem' {g g'} hg hg' τ := by
    refine ⟨by simp [(hg τ).1, (hg' τ).1], fun u w => ?_⟩
    simp only [Pi.mul_apply, Units.val_mul, ← mulVec_mulVec, (hg τ).2, (hg' τ).2]
  inv_mem' {g} hg τ := by
    refine ⟨?_, fun u w => ?_⟩
    · have := congrArg Matrix.det (g τ).mul_inv
      rwa [det_mul, (hg τ).1, one_mul, det_one] at this
    · rw [← (hg τ).2]
      simp only [Pi.inv_apply, mulVec_mulVec, Units.mul_inv, one_mulVec]

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology in
open scoped ENNReal NNReal in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
theorem _root_.GlobalTheory.SUVol.isClosed_realSU (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) :
    IsClosed (_root_.GlobalTheory.SUVol.realSU Ψ G : Set (Ψ → GL (Fin r) ℂ)) := by
  show IsClosed {g : Ψ → GL (Fin r) ℂ | ∀ τ : Ψ, (g τ : Matrix (Fin r) (Fin r) ℂ).det = 1 ∧ ∀ u w,
    _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ.1 G ((g τ : Matrix (Fin r) (Fin r) ℂ) *ᵥ u) ((g τ : Matrix (Fin r) (Fin r) ℂ) *ᵥ w) =
      _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ.1 G u w}
  have hc : ∀ τ : Ψ, Continuous fun g : Ψ → GL (Fin r) ℂ => (g τ : Matrix (Fin r) (Fin r) ℂ) :=
    fun τ => Units.continuous_val.comp (continuous_apply τ)
  simp only [Set.setOf_forall, Set.setOf_and]
  refine isClosed_iInter fun τ => ((isClosed_eq (hc τ).matrix_det continuous_const).inter
    (isClosed_iInter fun u => isClosed_iInter fun w => isClosed_eq ?_ continuous_const))
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC
  have hu := (hc τ).matrix_mulVec (continuous_const (y := u))
  have hw := (hc τ).matrix_mulVec (continuous_const (y := w))
  refine continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun b _ => ?_
  exact (((continuous_apply a).comp hu).mul continuous_const).mul
    (Complex.continuous_conj.comp ((continuous_apply b).comp hw))

instance (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) : LocallyCompactSpace (realSU Ψ G) := by
  haveI : LocallyCompactSpace (Matrix (Fin r) (Fin r) ℂ) :=
    inferInstanceAs (LocallyCompactSpace (Fin r → Fin r → ℂ))
  haveI : LocallyCompactSpace (Matrix (Fin r) (Fin r) ℂ)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  haveI : LocallyCompactSpace (GL (Fin r) ℂ) := Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  exact (isClosed_realSU Ψ G).locallyCompactSpace

instance (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) : SecondCountableTopology (realSU Ψ G) := by
  haveI : SecondCountableTopology (Matrix (Fin r) (Fin r) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin r → Fin r → ℂ))
  haveI : SecondCountableTopology (Matrix (Fin r) (Fin r) ℂ)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.secondCountableTopology
  haveI : SecondCountableTopology (GL (Fin r) ℂ) := Units.isEmbedding_embedProduct.secondCountableTopology
  exact TopologicalSpace.Subtype.secondCountableTopology _

def realLie (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) : Submodule ℝ (Ψ → Fin r → Fin r → ℂ) where
  carrier := {X | ∀ τ : Ψ, (Matrix.of (X τ)).trace = 0 ∧ ∀ u w,
    hermC τ.1 G (Matrix.of (X τ) *ᵥ u) w + hermC τ.1 G u (Matrix.of (X τ) *ᵥ w) = 0}
  zero_mem' τ := by simp [hermC]
  add_mem' {X Y} hX hY τ := by
    have e : Matrix.of ((X + Y) τ) = Matrix.of (X τ) + Matrix.of (Y τ) := rfl
    refine ⟨by rw [e, trace_add, (hX τ).1, (hY τ).1, add_zero], fun u w => ?_⟩
    have h1 := (hX τ).2 u w
    have h2 := (hY τ).2 u w
    rw [e]
    simp only [hermC, add_mulVec, Pi.add_apply, map_add (f := _), add_mul, mul_add, Finset.sum_add_distrib] at h1 h2 ⊢
    linear_combination h1 + h2
  smul_mem' c X hX τ := by
    have e : Matrix.of ((c • X) τ) = (c : ℂ) • Matrix.of (X τ) := rfl
    refine ⟨by rw [e, trace_smul, (hX τ).1, smul_zero], fun u w => ?_⟩
    have h1 := congrArg (fun z => (c : ℂ) * z) ((hX τ).2 u w)
    rw [e]
    simp only [hermC, smul_mulVec, Pi.smul_apply, smul_eq_mul, map_mul, Complex.conj_ofReal, mul_add,
      Finset.mul_sum, mul_zero] at h1 ⊢
    rw [← h1]
    congr 1 <;> refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_ <;> ring

def fromFrame {Ψ : Finset (E →+* ℂ)} (x : Frame Ψ r) :
    EuclideanSpace ℂ (Ψ × Fin r × Fin r) →ₗ[ℝ] (Ψ → Fin r → Fin r → ℂ) where
  toFun Y τ := (mat x τ * Matrix.of (fun a b => Y (τ, a, b)) * (mat x τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ)
  map_add' Y Z := by
    funext τ
    have e : Matrix.of (fun a b => (Y + Z) (τ, a, b)) =
      Matrix.of (fun a b => Y (τ, a, b)) + Matrix.of (fun a b => Z (τ, a, b)) := rfl
    rw [e, Matrix.mul_add, Matrix.add_mul]; rfl
  map_smul' c Y := by
    funext τ
    have e : Matrix.of (fun a b => (c • Y) (τ, a, b)) = c • Matrix.of (fun a b => Y (τ, a, b)) := rfl
    rw [e, Matrix.mul_smul, Matrix.smul_mul]; rfl

def riemLie (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (x : Frame Ψ r) :
    Measure (Ψ → Fin r → Fin r → ℂ) :=
  Measure.map (fun Y : (realLie Ψ G).comap (fromFrame x) => fromFrame x Y.1)
    (stdOrthonormalBasis ℝ ((realLie Ψ G).comap (fromFrame x))).toBasis.addHaar

def riemHaar (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (x : Frame Ψ r)
    [MeasurableSpace (realSU Ψ G)] [BorelSpace (realSU Ψ G)] : Measure (realSU Ψ G) :=
  tangentHaar (realSU Ψ G) (riemLie Ψ G x)

def embGL (Ψ : Finset (E →+* ℂ)) (r : ℕ) : GL (Fin r) E →* (Ψ → GL (Fin r) ℂ) :=
  Pi.monoidHom fun τ => Matrix.GeneralLinearGroup.map τ.1

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology in
open scoped ENNReal NNReal in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
private lemma hermC_map_mulVec_eq_of_preserves_form (τ : E →+* ℂ) (G M : Matrix (Fin r) (Fin r) E)
    (hK : ∀ a b, ∑ i, ∑ j, M i a * G i j * IsCMField.complexConj E (M j b) = G a b) (u w : Fin r → ℂ) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ G (M.map τ *ᵥ u) (M.map τ *ᵥ w) = _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ G u w := by
  have hK' : ∀ a b, τ (G a b) = ∑ i, ∑ j, τ (M i a) * τ (G i j) * starRingEnd ℂ (τ (M j b)) := by
    intro a b
    rw [← hK a b]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum, IsCMField.complexEmbedding_complexConj]
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC
  conv_rhs => rw [Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by rw [hK' a b]]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
  conv_lhs => enter [2, i, 2, j]; rw [Finset.sum_comm]
  conv_lhs => enter [2, i]; rw [Finset.sum_comm]
  conv_lhs => enter [2, i, 2, a]; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs => enter [2, a]; rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology in
open scoped ENNReal NNReal in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
theorem _root_.GlobalTheory.SUVol.embGL_mem_realSU (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E)
    (γ : GL (Fin r) E) (h1 : (γ : Matrix (Fin r) (Fin r) E).det = 1)
    (h2 : ∀ x y, _root_.ReciprocityTheory.ChartRestriction.G.FD.herm G ((γ : Matrix (Fin r) (Fin r) E) *ᵥ x) ((γ : Matrix (Fin r) (Fin r) E) *ᵥ y) =
      _root_.ReciprocityTheory.ChartRestriction.G.FD.herm G x y) :
    _root_.GlobalTheory.SUVol.embGL Ψ r γ ∈ _root_.GlobalTheory.SUVol.realSU Ψ G := by
  have hK : ∀ a b, ∑ i, ∑ j, (γ : Matrix (Fin r) (Fin r) E) i a * G i j *
      IsCMField.complexConj E ((γ : Matrix (Fin r) (Fin r) E) j b) = G a b := by
    intro a b
    have h := h2 (Pi.single a 1) (Pi.single b 1)
    unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.herm _root_.ReciprocityTheory.ChartRestriction.G.FD.cc at h
    simpa [Pi.single_apply, Matrix.mulVec_single_one] using h
  refine fun τ => ?_
  have hv : ((_root_.GlobalTheory.SUVol.embGL Ψ r γ τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) =
      (γ : Matrix (Fin r) (Fin r) E).map τ.1 :=
    Matrix.GeneralLinearGroup.val_map_apply τ.1 γ
  rw [hv]
  exact ⟨by rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, h1, map_one],
    hermC_map_mulVec_eq_of_preserves_form τ.1 G _ hK⟩

def inReal (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (Γ : Subgroup (GL (Fin r) E)) :
    Subgroup (realSU Ψ G) :=
  (Γ.map (embGL Ψ r)).subgroupOf (realSU Ψ G)

end GlobalTheory.SUVol
