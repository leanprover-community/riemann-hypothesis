module

public import Mathlib.Algebra.Central.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import GroundTheory.Brauer.TensorSimple
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.CMField

@[expose] public section

open NumberField Matrix
open scoped TensorProduct ComplexConjugate

namespace GlobalTheory.UPel.HT.RealRepBij

end GlobalTheory.UPel.HT.RealRepBij

namespace GlobalTheory.UPel.HT.RealRepBij

theorem span_range_eq_top {F B : Type} [Field F] [Ring B] [Algebra F B] [Algebra.IsCentral F B]
    [IsSimpleRing B] [FiniteDimensional F B] {n : ℕ} (σ : F →+* ℂ)
    (f : B →+* Matrix (Fin n) (Fin n) ℂ) (hdim : Module.finrank F B = n ^ 2)
    (hf : ∀ a, f (algebraMap F B a) = Matrix.scalar (Fin n) (σ a)) :
    Submodule.span ℂ (Set.range f) = ⊤ := by
  letI : Algebra F ℂ := σ.toAlgebra
  have hg : ∀ a, f (algebraMap F B a) = algebraMap F (Matrix (Fin n) (Fin n) ℂ) a := fun a => by
    rw [hf, Matrix.algebraMap_eq_diagonal]; rfl
  let g : B →ₐ[F] Matrix (Fin n) (Fin n) ℂ := { f with commutes' := hg }
  let L : ℂ ⊗[F] B →ₐ[ℂ] Matrix (Fin n) (Fin n) ℂ :=
    Algebra.TensorProduct.lift (Algebra.ofId ℂ _) g (fun r y => Algebra.commute_algebraMap_left r _)
  have hn : 0 < n := by
    have := Module.finrank_pos (R := F) (M := B)
    rw [hdim] at this
    exact Nat.pos_of_ne_zero fun h => by simp [h] at this
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hinj : Function.Injective L :=
    (IsSimpleRing.injective_ringHom_or_subsingleton_codomain L.toRingHom).resolve_right
      (not_subsingleton _)
  have hdim' : Module.finrank ℂ (ℂ ⊗[F] B) = Module.finrank ℂ (Matrix (Fin n) (Fin n) ℂ) := by
    rw [Module.finrank_baseChange, hdim, Module.finrank_matrix, Module.finrank_self]
    simp [sq]
  have hsurj : Function.Surjective L.toLinearMap :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim').1 hinj
  refine eq_top_iff.2 fun m _ => ?_
  clear ‹m ∈ ⊤›
  obtain ⟨x, rfl⟩ := hsurj m
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul c b =>
    have : L.toLinearMap (c ⊗ₜ b) = c • f b := by
      dsimp only [L]
      rw [AlgHom.toLinearMap_apply]
      erw [Algebra.TensorProduct.lift_tmul]
      rw [Algebra.ofId_apply, Algebra.smul_def]; rfl
    rw [this]
    exact Submodule.smul_mem _ c (Submodule.subset_span ⟨b, rfl⟩)
  | add x y hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy

end GlobalTheory.UPel.HT.RealRepBij

namespace GlobalTheory.UPel.HT.RealRepBij

variable {K F : Type} [Field K] [NumberField K] [NumberField.IsCMField K]
  [Field F] [NumberField F] [NumberField.IsCMField F]
  [Algebra K F] {p : ℕ} [Fact p.Prime]

end GlobalTheory.UPel.HT.RealRepBij
