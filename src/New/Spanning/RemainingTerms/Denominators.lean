import New.Spanning.Unfolding.TermStructure

/-!
# Denominators: bases of `A⁺ / I_γ` and `γ A⁺ / I_γ`

Let `γ` be a rational point of the unitary group that has the cell rank `j`. This file gives bases
of `A⁺ / I_γ` and `γ A⁺ / I_γ`: the first `j` vectors of the frame with `z_N`, and their images
under `γ`. The basis of `γ A⁺ / I_γ` is proved from the cell rank alone; the basis of `A⁺ / I_γ` is
proved when `E` contains a primitive `5040`-th root of unity (`HasPrimitiveRoot5040 E`). Under the
same hypothesis the determinant `New.Filling.subframeMinor` of the products of the two lists is not
zero (`New.Filling.HasCellRank.subframeMinor_ne_zero`); so the two quotients pair perfectly.

Here `n = ϱ + 1` and `N = S.N` is the prime of the data `S`. The basis vectors `e_1, …, e_{n-1}`
span the isotropic space `A`, the basis vector `z_N` has the product `-N` with itself, and
`A⁺ = A + E z_N` is the span of the frame `e_• = (e_1, …, e_{n-1}, z_N)`, which the code indexes
from `0`. The rank of `A / I_γ` is `min j (n - 1)`.

* `New.Filling.HasCellRank.linearIndependent_mkQ_frameImage_one_and_sup_eq`,
  `New.Filling.HasCellRank.linearIndependent_mkQ_frameImage_coe_and_sup_eq`: the two bases modulo
  `I_γ`; `New.Filling.HasCellRank.linearIndependent_mkQ_frameImage_and_sup_eq` states both.

Notions from other files:
* `frameImage M` is the matrix whose columns are the frame `M e_•`, and `colSpan` is the span of the
  columns, so `A⁺ = colSpan (frameImage 1)`.
* `commonIsotropic γ` is the space `I_γ = A ∩ γ A`.
* `subframeIndices j` is the set of indices of the first `j` vectors of `e_•` and of `z_N`.
* `S.frameProducts γ` is the matrix of the hermitian products (Gram matrix `S.ratGram`) of `e_•`
  with `γ e_•`, and `δ_j` is its leading minor of order `j`.
* `S.HasCellRank j γ` says: for one `ζ` with `ζ ζ̄ = 1` and every index `l ≥ j`, the flags of `e_•`
  and `γ e_•` share a vector with leading coefficients `ζ` and `1` at `l`; `δ_j ≠ 0`; and `j = n`
  exactly when `𝗀 = S.termDisc γ = |δ_n|² - N² |δ_{n-1}|²` is nonzero.
-/

noncomputable section

open Matrix Fin Function

namespace New

namespace Filling

variable {E : Type} [Field E] [CMType E] {𝔰 : Shape} {S : Filling E 𝔰} {j : Fin (𝔰.ϱ + 2)}
  {γ : S.G E}

/-! ### The subframe of the first `j` vectors and `z_N` -/

end Filling

end New
