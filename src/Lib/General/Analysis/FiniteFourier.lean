module

import TauCeti.LinearAlgebra.Matrix.Determinant.GaussSum

import Mathlib.NumberTheory.MulChar.Lemmas
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.SimpleRing.Principal
import TauCeti.Algebra.Group.AddChar.Basic
public import Lib.Speed

/-!
# Orthogonality, Fourier inversion and matrix Gauss sums over a finite ring

Finite Fourier analysis on matrices over a finite commutative ring `R`, for a primitive additive
character `ψ` (no multiple `ψ (r * ·)` with `r ≠ 0` is trivial).

* `New.exists_primitive_residue_addChar`: a
  character of a ring `F` for which the subring `O` is self-dual induces a primitive character of a
  suitable quotient ring of `O`.
* `New.sum_addChar_dotProduct`, `New.sum_addChar_trace_mul`: orthogonality; the sum of `ψ` along
  a nonzero linear form on vectors or on matrices is `0`.
* `New.Exchange.matrixFourier`, `New.Exchange.matrixFourier_matrixFourier`: the transform
  `ρ ↦ ∑ v, f v * ψ (tr (ρ v))`, not normalised, and its inversion formula.
* `New.exists_sum_smul_addChar_trace_eq`: every function on matrices is a linear combination of
  the characters `y ↦ ψ (tr (y u))`.
* `New.Exchange.exists_matrixFourier_eq_mul_inv_det`: the transform of a function with
  `S (g d) = χ (det g) S d`, for a multiplicative character `χ` (zero off the units) that is
  primitive, `New.Exchange.IsPrimitiveMulChar`, and the modulus of the Gauss sum of `χ ∘ det`.

## Relation to the literature

Known; see `Lib.Weil.TameGaussSum` for sources.
-/

@[expose] public section

open Matrix Finset Fintype AddChar Function

namespace New

variable {R F a N : Type*} [CommRing R]

/-- Let `O` be a subring of `F`, `π : O → R` a surjective ring homomorphism with kernel
`{x | g * x ∈ O}` (`hπ`), and `ψ` an additive character of `F` such that `ψ (t * ·)` is
trivial on `O` exactly when `t ∈ O` (`hψ`). Then `π x ↦ ψ (g * x)` is a well-defined primitive
character of `R`. -/
lemma exists_primitive_residue_addChar [CommRing F] {O : Subring F} {π : O →+* R} {g : F}
    {ψ : AddChar F ℂ} (hπ : Surjective π ∧ ∀ x : O, π x = 0 ↔ g * x.val ∈ O)
    (hψ : ∀ t : F, (∀ s ∈ O, ψ (t * s) = 1) ↔ t ∈ O) :
    ∃ φ : AddChar R ℂ, φ.IsPrimitive ∧ ∀ x : O, φ (π x) = ψ (g * x) := by
  obtain ⟨hπ_surj, hπ_ker⟩ := hπ
  -- `x ↦ ψ (g * x)` is constant on the fibres of `π`, since `π x = π y` puts `g * (x - y)` in `O`.
  have h_factors : Function.FactorsThrough (fun x : O ↦ ψ (g * x)) π := by
    intro x y hxy
    have h_mem : g * (x - y : O).val ∈ O := (hπ_ker (x - y)).mp (by simp [hxy])
    exact eq_of_div_eq_one <| by
      simpa [mul_sub, map_sub_eq_div] using (hψ _).mpr h_mem 1 O.one_mem
  let φ : R → ℂ := Function.extend π (fun x : O ↦ ψ (g * x)) 1
  have hφ (x : O) : φ (π x) = ψ (g * x) := h_factors.extend_apply 1 x
  have h_add (r s : R) : φ (r + s) = φ r * φ s := by
    obtain ⟨x, rfl⟩ := hπ_surj r
    obtain ⟨y, rfl⟩ := hπ_surj s
    simp [← map_add, hφ, mul_add, map_add_eq_mul]
  let φ' : AddChar R ℂ :=
    { toFun := φ, map_zero_eq_one' := by simpa using hφ 0, map_add_eq_mul' := h_add }
  -- Primitivity: if `φ (π x * ·)` is trivial then `ψ (g * x * ·)` is trivial on `O`, so `π x = 0`.
  refine ⟨φ', fun r hr_ne h_triv ↦ ?_, hφ⟩
  obtain ⟨x, rfl⟩ := hπ_surj r
  have h_triv_O : ∀ s ∈ O, ψ (g * x * s) = 1 := fun s hs ↦ by
    simpa [← map_mul, hφ, φ', mul_assoc] using DFunLike.congr_fun h_triv (π ⟨s, hs⟩)
  exact hr_ne ((hπ_ker x).mpr ((hψ _).mp h_triv_O))

variable [Fintype R] [DecidableEq R] [Fintype a] [DecidableEq a] [Fintype N] [DecidableEq N]

/-! ### The Fourier transform on matrices -/

/-- The Fourier transform of a function `f` on `N × a` matrices, a function on `a × N` matrices:
`ρ ↦ ∑ v, f v * ψ (tr (ρ v))`, with no normalising factor. -/
noncomputable def Exchange.matrixFourier (ψ : AddChar R ℂ) (f : Matrix N a R → ℂ)
    (ρ : Matrix a N R) : ℂ :=
  ∑ v : Matrix N a R, f v * ψ (ρ * v).trace

variable (χ : MulChar R ℂ) in
/-- The multiplicative character `χ` of the finite ring `R` is primitive: for every `a ≠ 0` some
element `1 + c * a` has `χ`-value different from `0` (so it is a unit) and from `1`. That is,
for no nonzero `a` is `χ` trivial on the units congruent to `1` modulo `a`. -/
def Exchange.IsPrimitiveMulChar : Prop :=
  ∀ a ≠ (0 : R), ∃ c : R, χ (1 + c * a) ≠ 0 ∧ χ (1 + c * a) ≠ 1

variable {χ : MulChar R ℂ} {ψ : AddChar R ℂ}

/-- Orthogonality of characters along a linear form: for a primitive additive character `ψ` of `R`
and a vector `z` in `R^a`, the sum of `ψ (z ⬝ᵥ x)` over all `x` in `R^a` is the number of such `x`
if `z = 0` and `0` otherwise. -/
lemma sum_addChar_dotProduct (hψ : ψ.IsPrimitive) (z : a → R) :
    ∑ x : a → R, ψ (z ⬝ᵥ x) = if z = 0 then Fintype.card (a → R) else 0 := by
  -- The sum splits into a product over the coordinates; by primitivity the factor at `i` is
  -- `card R` if `z i = 0` and `0` otherwise.
  calc ∑ x, ψ (z ⬝ᵥ x)
    _ = ∑ x : a → R, ∏ i, ψ (z i * x i) := by simp only [dotProduct, AddChar.map_sum_eq_prod]
    _ = ∏ i, ∑ t, ψ (z i * t) := (Fintype.prod_sum fun i t ↦ ψ (z i * t)).symm
    _ = _ := by simp [mul_comm, sum_mulShift, hψ, Fintype.prod_ite_zero, funext_iff]

/-- Orthogonality of characters on matrices: for a primitive additive character `ψ` of `R` and an
`a × N` matrix `ρ`, the sum of `ψ (tr (ρ v))` over all `N × a` matrices `v` is the number of such
matrices if `ρ = 0` and `0` otherwise. -/
lemma sum_addChar_trace_mul (hψ : ψ.IsPrimitive) (ρ : Matrix a N R) :
    ∑ v : Matrix N a R, ψ (ρ * v).trace = if ρ = 0 then Fintype.card (Matrix N a R) else 0 := by
  -- `tr (ρ v)` is the dot product of the matrices `ρᵀ` and `v` read as vectors
  simpa [← vec_bijective.sum_comp, vec_dotProduct_vec, card_of_bijective vec_bijective]
    using sum_addChar_dotProduct hψ ρᵀ.vec

/-- Fourier inversion for matrices over a finite commutative ring R with a primitive additive
character ψ: applying the transform `New.Exchange.matrixFourier` twice to f gives y ↦ f(−y) times
the number of matrices. -/
lemma Exchange.matrixFourier_matrixFourier (hψ : ψ.IsPrimitive) (f : Matrix N a R → ℂ)
    (y : Matrix N a R) :
    matrixFourier ψ (matrixFourier ψ f) y = f (-y) * Fintype.card (Matrix a N R) := by
  -- Exchange the two sums: by `sum_addChar_trace_mul` the inner sum `∑ u, ψ (tr ((v + y) u))`
  -- vanishes unless `v = -y`.
  have h_inner (v : Matrix N a R) : ∑ u : Matrix a N R, ψ ((v + y) * u).trace =
      ((if v + y = 0 then Fintype.card (Matrix a N R) else 0 : ℕ) : ℂ) :=
    sum_addChar_trace_mul hψ (v + y)
  have h_exp (u : Matrix a N R) (v : Matrix N a R) :
      ψ (u * v).trace * ψ (y * u).trace = ψ ((v + y) * u).trace := by
    rw [← map_add_eq_mul, trace_mul_comm u v, ← trace_add, ← Matrix.add_mul]
  calc matrixFourier ψ (matrixFourier ψ f) y
      = ∑ u : Matrix a N R, ∑ v, f v * ψ ((v + y) * u).trace := by
        simp only [matrixFourier, sum_mul, mul_assoc, h_exp]
    _ = ∑ v, f v * ∑ u : Matrix a N R, ψ ((v + y) * u).trace := by
        rw [sum_comm]
        simp only [mul_sum]
    _ = ∑ v, if v = -y then f v * Fintype.card (Matrix a N R) else 0 := by
        simp [h_inner, add_eq_zero_iff_eq_neg]
    _ = f (-y) * Fintype.card (Matrix a N R) := by simp

/-- For a primitive additive character ψ of a finite commutative ring R, every complex function
f on N × a matrices over R is a linear combination of the characters y ↦ ψ(tr(yu)), for u
ranging over the a × N matrices. -/
lemma exists_sum_smul_addChar_trace_eq (hψ : ψ.IsPrimitive) (f : Matrix N a R → ℂ) :
    ∃ c : Matrix a N R → ℂ,
      ∑ u : Matrix a N R, c u • (fun y : Matrix N a R ↦ ψ (y * u).trace) = f := by
  -- Fourier inversion: the coefficients are the transform of `t ↦ f (-t)`, normalised.
  refine ⟨Exchange.matrixFourier ψ fun t ↦ f (-t) / card (Matrix a N R), funext fun y ↦ ?_⟩
  simpa [Exchange.matrixFourier, card_ne_zero] using
    Exchange.matrixFourier_matrixFourier hψ (fun t ↦ f (-t) / card (Matrix a N R)) y

/-- Gauss sums of square matrices over a finite ring `R`. Let `ψ` be primitive and `χ` primitive in
the sense of `New.Exchange.IsPrimitiveMulChar`, and let `n` be the cardinality of `a`. There is a
number `γ` with `|γ|² = #R ^ (n²)` such that every function `S` on `n × n` matrices with
`S (g u) = χ (det g) S u` for all invertible `g` has the Fourier transform `y ↦ γ χ⁻¹(det y) S 1`,
which is zero where `y` is not invertible.

TauCeti’s determinant Gauss sum theorem supplies the Fourier identity and the norm of `γ`. -/
lemma Exchange.exists_matrixFourier_eq_mul_inv_det (hψ : ψ.IsPrimitive)
    (hχ : IsPrimitiveMulChar χ) :
    ∃ γ : ℂ,
      ‖γ‖ ^ 2 = (Fintype.card R : ℝ) ^ Fintype.card a ^ 2 ∧
      ∀ S : Matrix a a R → ℂ,
        (∀ (g : GL a R) (u : Matrix a a R), S (g.val * u) = χ g.val.det * S u) →
        ∀ y : Matrix a a R, matrixFourier ψ S y = γ * χ⁻¹ y.det * S 1 := by
  have h_prim (r : R) (hr : r ≠ 0) : ∃ c : R, IsUnit (1 + c * r) ∧ χ (1 + c * r) ≠ 1 := by
    obtain ⟨c, h_ne_zero, h_ne_one⟩ := hχ r hr
    exact ⟨c, by simpa [χ.apply_eq_zero_iff] using h_ne_zero, h_ne_one⟩
  obtain ⟨γ, h_norm, h_fourier⟩ := hψ.exists_traceFourier_eq_mul_inv_det (n := a) h_prim
  have h_card : Fintype.card (Matrix a a R) = Fintype.card R ^ Fintype.card a ^ 2 := by
    rw [Fintype.card_congr Matrix.of.symm, Fintype.card_fun, Fintype.card_fun, ← pow_mul, sq]
  refine ⟨γ, by rw [h_norm, h_card, Nat.cast_pow], ?_⟩
  simpa only [matrixFourier, AddChar.traceFourier_apply] using h_fourier

end New
