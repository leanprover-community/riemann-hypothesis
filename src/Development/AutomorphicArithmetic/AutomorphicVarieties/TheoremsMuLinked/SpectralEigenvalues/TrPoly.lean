module

public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TraceIntegralSubringExtension
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Topology.Sheaves.Init
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

@[expose] public section

open IsLocalRing Polynomial

theorem UpperTheory.V.Th.Sp.trp :
    ∀ (O : Type) [CommRing O] [IsDomain O] (n : ℕ) (A : Matrix (Fin n) (Fin n) O) (α : Fin n → O) (p : O[X]), A.charpoly = ∏ i, (X - C (α i)) → (aeval A p).trace = ∑ i, p.eval (α i) := by
  intro O _ _ n A α p h
  let K := AlgebraicClosure (FractionRing O)
  let f : O →+* K := (algebraMap (FractionRing O) K).comp (algebraMap O (FractionRing O))
  have hf : Function.Injective f :=
    (algebraMap (FractionRing O) K).injective.comp (IsFractionRing.injective O (FractionRing O))
  apply hf
  have htr : ∀ M : Matrix (Fin n) (Fin n) O, f M.trace = (M.map f).trace := by
    intro M

    simp [Matrix.trace, map_sum]
  have haeval : (aeval A p).map f = aeval (A.map f) (p.map f) := by
    have := Polynomial.map_aeval_eq_aeval_map (φ := f) (ψ := f.mapMatrix) ?_ p A
    · simpa using this
    · ext c i j
      simp [Matrix.algebraMap_matrix_apply]
      split_ifs <;> simp
  have hchar : (A.map f).charpoly = ((Finset.univ.val.map fun i => f (α i)).map fun a => X - C a).prod := by
    rw [Matrix.charpoly_map, h, Polynomial.map_prod]
    simp [Finset.prod_eq_multiset_prod, Multiset.map_map, Function.comp_def]

  rw [htr, haeval, GlobalTheory.CompanionTheory.TraceSpec.trace_aeval_matrix, hchar, Polynomial.roots_multiset_prod_X_sub_C, map_sum]
  simp [Multiset.map_map, Finset.sum_eq_multiset_sum, Function.comp_def]
