module

public import Lib.Adelic.Unitary.Defs
public import Lib.General.LinearAlgebra.IntegralLattices
import Lib.Adelic.Adeles.IdeleModulus
import Lib.General.LinearAlgebra.HermiteForm
import Lib.General.LinearAlgebra.PolarDecomposition

/-!
# Normalisation of adelic frames

A rectangular frame with a left inverse can be made orthonormal at infinity and primitive at
the finite places by a change of basis preserving the flag of column weights.
-/

@[expose] public section

noncomputable section

open Matrix NumberField

namespace New

variable {E : Type*} [Field E] [NumberField E] {n k : Type*}
  [Fintype n] [Fintype k] [DecidableEq k]

/-- The columns are orthonormal at each infinite place. At the finite places both the matrix and
a left inverse have integral entries. -/
structure IsNormalizedAdelicFrame (X : Matrix n k (𝔸 E)) : Prop where
  orthonormal (w : InfinitePlace E) : (X.map (evalInf w))ᴴ * X.map (evalInf w) = 1
  primitive : IsPrimitiveMatrix (Ô E) (X.map (RingHom.snd (InfinitePlace E → ℂ) (𝔸f E)))

/-- The columns of an adelic frame can be normalised by a block upper triangular change of basis
for any natural-number weights on the columns. -/
theorem exists_blockTriangular_normalizedFrame [DecidableEq n] {X : Matrix n k (𝔸 E)}
    (hX : HasLeftInv X) (wt : k → ℕ) :
    ∃ b : GL k (𝔸 E), b.val.BlockTriangular wt ∧ IsNormalizedAdelicFrame (X * b.val) := by
  let fin := RingHom.snd (InfinitePlace E → ℂ) (𝔸f E)
  choose a ha horth using fun w : InfinitePlace E ↦ exists_orthonormal_mul wt (hX.map (evalInf w))
  obtain ⟨c, hc, hprim⟩ := isValuationPair_Ô.exists_isPrimitiveMatrix_mul (hX.map fin) wt
  refine ⟨mkAdelicGL (a, c), fun i j hij ↦ Prod.ext (funext fun w ↦ ha w hij) (hc hij), ?_⟩
  constructor
  · intro w
    rw [Matrix.map_mul]
    exact horth w
  · rw [Matrix.map_mul]
    exact hprim

end New
