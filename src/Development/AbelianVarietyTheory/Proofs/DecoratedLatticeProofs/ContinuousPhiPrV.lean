module

public import Formalism.LocalToGlobal.HermitianForms.PsiZeroNontrivialCharacter
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.BasicNotions Formalism.L2.Forms NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

namespace GlobalTheory.LevelCharOpen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
  {gp : Fin 2 → ℕ}

theorem redM_eq_one (v : HeightOneSpectrum (𝓞 F)) (X : Matrix (Fin n) (Fin n) (v.adicCompletion F))
    (hX : ∀ i j, Valued.v (X i j - (1 : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j) < 1) : redM F v X = 1 := by
  ext i j
  have h1 : (1 : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j ∈ v.adicCompletionIntegers F := by
    rw [Matrix.one_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  have hd : X i j - (1 : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j ∈ v.adicCompletionIntegers F := (hX i j).le
  have hx : X i j ∈ v.adicCompletionIntegers F := by
    have := add_mem hd h1
    rwa [sub_add_cancel] at this
  have h0 : IsLocalRing.residue (v.adicCompletionIntegers F) ⟨_, hd⟩ = 0 := by
    rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
    exact (hX i j).ne
  have e : (⟨X i j, hx⟩ : v.adicCompletionIntegers F) = ⟨_, hd⟩ + ⟨_, h1⟩ := Subtype.ext (sub_add_cancel _ _).symm
  simp only [redM, dif_pos hx]
  rw [e, map_add (f := _), h0, zero_add]
  by_cases hij : i = j
  · subst hij
    have : (⟨_, h1⟩ : v.adicCompletionIntegers F) = 1 := Subtype.ext (Matrix.one_apply_eq i)
    rw [this, map_one, Matrix.one_apply_eq]
  · have : (⟨_, h1⟩ : v.adicCompletionIntegers F) = 0 := Subtype.ext (Matrix.one_apply_ne hij)
    rw [this, map_zero, Matrix.one_apply_ne hij]

theorem continuous_phi_prV (G : GLoc F E σ gp) (a : Fin 2) (v : HeightOneSpectrum (𝓞 F)) (h : (gp a : 𝓞 F) ∈ v.asIdeal) :
    letI := tensTopL (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
    Continuous ((G.phi a v h).comp (prV (E := E) v)) := by
  letI : Algebra (FiniteAdeleRing (𝓞 F) F) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) := Algebra.TensorProduct.rightAlgebra
  letI := tensTopL (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
  haveI : IsModuleTopology (FiniteAdeleRing (𝓞 F) F) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) := ⟨rfl⟩
  refine IsModuleTopology.continuous_of_ringHom (R := FiniteAdeleRing (𝓞 F) F) _ ?_
  have hv : Continuous (Formalism.UG.evalV F v) := RestrictedProduct.continuous_eval v
  refine hv.congr fun r => ?_
  show _ = (G.sp a v h ((1 : E) ⊗ₜ[F] Formalism.UG.evalV F v r)).1
  rw [G.sp_alg]

end GlobalTheory.LevelCharOpen
