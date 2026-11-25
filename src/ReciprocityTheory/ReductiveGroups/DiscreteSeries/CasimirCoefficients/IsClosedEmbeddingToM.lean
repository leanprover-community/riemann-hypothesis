module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DefsRep
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Tactic.Lemma

@[expose] public section

noncomputable section

open Matrix Topology MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

def hs (g : Matrix (Fin n) (Fin n) ℂ) : ℝ := ∑ i, ∑ j, ‖g i j‖ ^ 2

lemma Jm_mul_self (ε : Fin n → Bool) : Jm ε * Jm ε = 1 := by
  unfold Jm
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  split_ifs <;> norm_num

lemma Jm_conjTranspose (ε : Fin n → Bool) : (Jm ε)ᴴ = Jm ε := by
  unfold Jm
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext a
  by_cases h : ε a = true <;> simp [h]

def UJ (ε : Fin n → Bool) : Subgroup (Matrix (Fin n) (Fin n) ℂ)ˣ where
  carrier := {g | inUJ ε (g : Matrix (Fin n) (Fin n) ℂ)}
  mul_mem' := by
    intro g h hg hh
    simp only [Set.mem_ofPred_eq, inUJ, Units.val_mul, Matrix.conjTranspose_mul] at *
    let A : Matrix (Fin n) (Fin n) ℂ := g
    let B : Matrix (Fin n) (Fin n) ℂ := h
    calc Bᴴ * Aᴴ * Jm ε * (A * B)
        = Bᴴ * (Aᴴ * Jm ε * A) * B := by simp only [Matrix.mul_assoc]
      _ = Jm ε := by rw [hg, hh]
  one_mem' := by
    simp only [Set.mem_ofPred_eq, inUJ, Units.val_one, Matrix.conjTranspose_one, Matrix.one_mul,
      Matrix.mul_one]
  inv_mem' := by
    intro g hg
    simp only [Set.mem_ofPred_eq, inUJ] at *
    let A : Matrix (Fin n) (Fin n) ℂ := g
    let B : Matrix (Fin n) (Fin n) ℂ := ↑g⁻¹
    have hAB : A * B = 1 := Units.mul_inv g
    calc Bᴴ * Jm ε * B
        = Bᴴ * (Aᴴ * Jm ε * A) * B := by rw [hg]
      _ = (A * B)ᴴ * Jm ε * (A * B) := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Jm ε := by simp [hAB]

abbrev toM {ε : Fin n → Bool} (g : UJ ε) : Matrix (Fin n) (Fin n) ℂ :=
  ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)

lemma left_inv_of_inUJ (ε : Fin n → Bool) (g : Matrix (Fin n) (Fin n) ℂ) (hg : inUJ ε g) :
    (Jm ε * gᴴ * Jm ε) * g = 1 := by
  unfold inUJ at hg
  simpa only [Matrix.mul_assoc, Jm_mul_self] using congrArg (fun x => Jm ε * x) hg

lemma toM_inv (ε : Fin n → Bool) (g : UJ ε) : toM g⁻¹ = Jm ε * (toM g)ᴴ * Jm ε :=
  Units.inv_eq_of_mul_eq_one_left (left_inv_of_inUJ ε _ g.2)

lemma continuous_toM (ε : Fin n → Bool) : Continuous (fun g : UJ ε => toM g) :=
  Units.continuous_val.comp continuous_subtypeVal

lemma isClosed_inUJ (ε : Fin n → Bool) : IsClosed {g : Matrix (Fin n) (Fin n) ℂ | inUJ ε g} := by
  unfold inUJ
  exact isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul
    continuous_id) continuous_const

lemma range_toM (ε : Fin n → Bool) : Set.range (fun g : UJ ε => toM g) = {g | inUJ ε g} := by
  ext g
  constructor
  · rintro ⟨u, rfl⟩; exact u.2
  · intro hg
    have h2 := left_inv_of_inUJ ε g hg
    exact ⟨⟨⟨g, Jm ε * gᴴ * Jm ε, mul_eq_one_comm.mp h2, h2⟩, hg⟩, rfl⟩

/-- The inclusion `UJ ε → Matrix (Fin n) (Fin n) ℂ` is a closed embedding, since the inverse in
`UJ ε` is given continuously by `A ↦ Jm ε * Aᴴ * Jm ε`. -/
lemma isClosedEmbedding_toM (ε : Fin n → Bool) : IsClosedEmbedding (fun g : UJ ε => toM g) := by
  refine ⟨?_, by rw [range_toM]; exact isClosed_inUJ ε⟩
  let F : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ × (Matrix (Fin n) (Fin n) ℂ)ᵐᵒᵖ :=
    fun A => (A, MulOpposite.op (Jm ε * Aᴴ * Jm ε))
  have hF : Continuous F :=
    continuous_id.prodMk (MulOpposite.continuous_op.comp
      ((continuous_const.matrix_mul continuous_id.matrix_conjTranspose).matrix_mul
        continuous_const))
  refine IsEmbedding.of_comp (continuous_toM ε) hF ?_
  have heq : F ∘ (fun g : UJ ε => toM g) =
      Units.embedProduct (Matrix (Fin n) (Fin n) ℂ) ∘ Subtype.val := by
    funext g
    simp only [Function.comp_apply, F, Units.embedProduct_apply, ← toM_inv]
    rfl
  rw [heq]
  exact Units.isEmbedding_embedProduct.comp IsEmbedding.subtypeVal

instance (ε : Fin n → Bool) : LocallyCompactSpace (UJ ε) := by
  have : LocallyCompactSpace (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → ℂ))
  exact (isClosedEmbedding_toM ε).locallyCompactSpace

instance (ε : Fin n → Bool) : SecondCountableTopology (UJ ε) := by
  have : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))
  exact (isClosedEmbedding_toM ε).isInducing.secondCountableTopology

instance (ε : Fin n → Bool) : MeasurableSpace (UJ ε) := borel _

instance (ε : Fin n → Bool) : BorelSpace (UJ ε) := ⟨rfl⟩

lemma haar_isHaar (ε : Fin n → Bool) : (Measure.haar : Measure (UJ ε)).IsHaarMeasure := inferInstance

lemma Kset_mul (ε : Fin n → Bool) {g h : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Kset ε)
    (hh : h ∈ Kset ε) : g * h ∈ Kset ε := by
  refine ⟨Submonoid.mul_mem _ hg.1 hh.1, ?_⟩
  rw [Matrix.mul_assoc, hh.2, ← Matrix.mul_assoc, hg.2, Matrix.mul_assoc]

lemma Kset_star (ε : Fin n → Bool) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Kset ε) :
    star g ∈ Kset ε := by
  refine ⟨Unitary.star_mem hg.1, ?_⟩
  simpa only [star_mul, Matrix.star_eq_conjTranspose, Jm_conjTranspose] using
    (congrArg star hg.2).symm

def KG (ε : Fin n → Bool) : Subgroup (UJ ε) where
  carrier := {g | toM g ∈ Kset ε}
  mul_mem' := by
    intro g h hg hh
    show toM g * toM h ∈ Kset ε
    exact Kset_mul ε hg hh
  one_mem' := by
    show (1 : Matrix (Fin n) (Fin n) ℂ) ∈ Kset ε
    refine ⟨Submonoid.one_mem _, ?_⟩
    rw [Matrix.one_mul, Matrix.mul_one]
  inv_mem' := by
    intro g hg
    have h2 : toM g⁻¹ = star (toM g) :=
      Units.inv_eq_of_mul_eq_one_right (Unitary.mul_star_self_of_mem hg.1)
    show toM g⁻¹ ∈ Kset ε
    rw [h2]
    exact Kset_star ε hg

abbrev toMK {ε : Fin n → Bool} (k : KG ε) : Matrix (Fin n) (Fin n) ℂ := toM (k : UJ ε)

end ReciprocityTheory.ChartRestriction.DS.S7
