module

public import Lib.Adelic.Reduction.FrameNormalization
public import Lib.Adelic.Adeles.IdeleModulus
import Lib.Adelic.Reduction.MinkowskiTheorems
import Lib.General.LinearAlgebra.PartnerAlgebra

/-!
# Independence of the determinant of a normalising basis change

For a frame over a CM field, two adelic normalisations differ by unitary matrices at infinity
and an integral change of basis at the finite places. These factors all have determinant of
absolute value one. The product formula gives the same independence for rational basis changes.
-/

@[expose] public section

noncomputable section

open NumberField Matrix

namespace New

variable {E n k : Type} [Field E] [Fintype n] [Fintype k] [DecidableEq k]

section NumberField

variable [NumberField E]

/-- Right multiplication preserves a normalised frame precisely for basis changes that are
unitary at infinity and belong to the integral general linear group at the finite places. -/
theorem IsNormalizedAdelicFrame.mul_iff {X : Matrix n k (𝔸 E)} (hX : IsNormalizedAdelicFrame X)
    (b : GL k (𝔸 E)) :
    IsNormalizedAdelicFrame (X * b.val) ↔
      (∀ w : InfinitePlace E, (b.val.map (evalInf w))ᴴ * b.val.map (evalInf w) = 1) ∧
        b.map (RingHom.snd (InfinitePlace E → ℂ) (𝔸f E)) ∈ intGL k (Ô E) := by
  have hinf (w : InfinitePlace E) :
      ((X * b.val).map (evalInf w))ᴴ * (X * b.val).map (evalInf w) =
        (b.val.map (evalInf w))ᴴ * b.val.map (evalInf w) := by
    rw [Matrix.map_mul, conjTranspose_mul, Matrix.mul_assoc, ← (X.map (evalInf w))ᴴ.mul_assoc,
      hX.orthonormal, Matrix.one_mul]
  have hfin : IsPrimitiveMatrix (Ô E) ((X * b.val).map (RingHom.snd ..)) ↔
      b.map (RingHom.snd (InfinitePlace E → ℂ) (𝔸f E)) ∈ intGL k (Ô E) := by
    rw [Matrix.map_mul, hX.primitive.mul_iff]
    exact isPrimitiveMatrix_iff_mem_intGL (b.map (RingHom.snd ..))
  exact ⟨fun h ↦ ⟨fun w ↦ (hinf w).symm.trans (h.orthonormal w), hfin.mp h.primitive⟩,
    fun ⟨hu, hi⟩ ↦ ⟨fun w ↦ (hinf w).trans (hu w), hfin.mpr hi⟩⟩

end NumberField

variable [CMType E]

/-- The adelic absolute value of the determinant of a normalising change of basis is independent
of the choice of normalisation. -/
theorem ideleAbs_det_eq_of_normalizedFrame {X : Matrix n k (𝔸 E)} {b c : GL k (𝔸 E)}
    (hb : IsNormalizedAdelicFrame (X * b.val)) (hc : IsNormalizedAdelicFrame (X * c.val)) :
    ideleAbs b.det = ideleAbs c.det := by
  let t := b⁻¹ * c
  have ht : IsNormalizedAdelicFrame ((X * b.val) * t.val) := by
    simpa [t, Matrix.mul_assoc] using hc
  obtain ⟨h_inf, h_fin⟩ := (hb.mul_iff t).1 ht
  let a (w : InfinitePlace E) := t.map (evalInf w)
  let d := t.map (RingHom.snd (InfinitePlace E → ℂ) (𝔸f E))
  have h_arch (w : InfinitePlace E) : ‖(a w).val.det‖ ^ 2 = 1 := by
    have hdet := congrArg (fun M : Matrix k k ℂ ↦ ‖M.det‖) (h_inf w)
    simpa [sq, a] using hdet
  have hd : finIdeleAbs d.det = 1 := by
    have hvol := genIndex_det_eq_one isOpen_Ô isCompact_Ô h_fin
    have hindex := genIndex_eq_inv_finIdeleAbs d.det
    simpa using (hindex.symm.trans hvol)
  have hprod : t = mkAdelicGL (a, d) := Units.ext (matrix_ext_𝔸 (fun _ ↦ rfl) rfl)
  have hunit : ideleAbs t.det = 1 := by
    rw [hprod, Core.ideleAbs_det_mkAdelicGL, hd]
    simp [h_arch]
  have hbc : b * t = c := by simp [t]
  rw [← hbc, map_mul, map_mul, hunit, mul_one]

/-- Changing the rational basis before normalising a frame preserves the adelic absolute value
of the normalising determinant. -/
theorem ideleAbs_det_eq_of_rational_basis_change {X : Matrix n k (𝔸 E)} (q : GL k E)
    {b c : GL k (𝔸 E)} (hb : IsNormalizedAdelicFrame (X * b.val))
    (hc : IsNormalizedAdelicFrame ((X * (q.map toAdele).val) * c.val)) :
    ideleAbs b.det = ideleAbs c.det := by
  have hqc : IsNormalizedAdelicFrame (X * (q.map toAdele * c).val) := by
    simpa [Matrix.mul_assoc] using hc
  simpa [Core.ideleAbs_det_map_toAdele] using ideleAbs_det_eq_of_normalizedFrame hb hqc

end New
