module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.LeAdicClosure
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
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
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.V.Fr.residually_diagonal_representation :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] {F : Frame l k} {n : ℕ} {Q : Type} [CommRing Q] [IsDomain Q] [IsLocalRing Q] (f : k →+* Q) (ρ : NRep F n Q), (ρ.map (residue Q)).IsBar ((residue Q).comp f) → ρ.triM = ⊥ → (∀ v g, (ρ.r (F.loc0 v g)).charpoly = ∏ i, (Polynomial.X - Polynomial.C (ρ.ψ v i g : Q))) → (∀ (g : F.G0) (i : Fin n), ρ.r g i i = f ((F.Ψ g ^ w n i : kˣ) : k)) → ρ.IsBar f := by
  intro l _ k _ F n Q _ _ _ f ρ hbar htri hchar hdiag
  refine ⟨hdiag, ?_⟩
  intro v i g
  have hz : ∀ (s : F.G0) (a b : Fin n), a < b → ρ.r s a b = 0 := fun s a b hab => by
    have : ρ.r s a b ∈ ρ.triM := Ideal.subset_span ⟨s, a, b, hab, rfl⟩
    rw [htri] at this
    exact (Submodule.mem_bot Q).1 this
  have hT : (ρ.r (F.loc0 v g))ᵀ.BlockTriangular id := fun a b hab => hz _ b a hab
  have h1 := Matrix.charpoly_of_upperTriangular _ hT
  rw [Matrix.charpoly_transpose, hchar] at h1
  have h2 := congrArg (Polynomial.eval (ρ.ψ v i g : Q)) h1
  simp only [Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at h2
  rw [Finset.prod_eq_zero (Finset.mem_univ i) (sub_self _)] at h2
  obtain ⟨j, -, hj⟩ := Finset.prod_eq_zero_iff.1 h2.symm
  rw [sub_eq_zero, Matrix.transpose_apply, hdiag] at hj
  have h3 := hbar.2 v i g
  rw [NRep.map_ψ, hj] at h3
  have h4 := ((residue Q).comp f).injective h3
  rw [hj, h4]
