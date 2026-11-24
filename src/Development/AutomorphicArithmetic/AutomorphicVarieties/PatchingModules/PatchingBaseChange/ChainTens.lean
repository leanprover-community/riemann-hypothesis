module

public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.ChainLift
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PairedDualFirstOrderDualMatrixSpace
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.RepAlg

@[expose] public section

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

theorem UpperTheory.V.Pa.BC.chain_tens :
    ∀ (O O' B : Type) [CommRing O] [CommRing O'] [Nontrivial O'] [IsLocalRing O] [Algebra O O'] [Module.Finite O O'] [Module.Free O O'] [CommRing B] [Algebra O B] (h : ℕ) (p : Fin (h + 1) → Ideal B) (e : Fin h → Ideal B), (∀ i, (p i).IsPrime) → (∀ i, (e i).IsPrime ∧ e i ≤ p i.castSucc ∧ e i ≤ p i.succ) → (∃ (P : Fin (h + 1) → Ideal (O' ⊗[O] B)) (E : Fin h → Ideal (O' ⊗[O] B)), (∀ i, (P i).IsPrime ∧ (P i).comap (Algebra.TensorProduct.includeRight : B →ₐ[O] O' ⊗[O] B) = p i) ∧ ∀ i, (E i).IsPrime ∧ (E i).comap (Algebra.TensorProduct.includeRight : B →ₐ[O] O' ⊗[O] B) = e i ∧ E i ≤ P i.castSucc ∧ E i ≤ P i.succ) ∧ ∀ (P : Ideal (O' ⊗[O] B)) (q : Ideal B), P.IsPrime → q.IsPrime → q ≤ P.comap (Algebra.TensorProduct.includeRight : B →ₐ[O] O' ⊗[O] B) → ∃ Q : Ideal (O' ⊗[O] B), Q.IsPrime ∧ Q.comap (Algebra.TensorProduct.includeRight : B →ₐ[O] O' ⊗[O] B) = q ∧ Q ≤ P := by
  intro O O' B _ _ _ _ _ _ _ _ _ h p e hp he
  letI : Algebra B (O' ⊗[O] B) := Algebra.TensorProduct.rightAlgebra
  let φ : B ⊗[O] O' ≃ₐ[B] O' ⊗[O] B := Algebra.TensorProduct.commRight O B O'
  haveI : Module.Finite B (O' ⊗[O] B) := Module.Finite.equiv φ.toLinearEquiv
  haveI : Module.Free B (O' ⊗[O] B) := Module.Free.of_equiv φ.toLinearEquiv
  haveI : Module.FaithfullyFlat O O' := inferInstance
  haveI : Module.FaithfullyFlat B (O' ⊗[O] B) :=
    Module.FaithfullyFlat.of_linearEquiv B (B ⊗[O] O') φ.symm.toLinearEquiv
  haveI : FaithfulSMul B (O' ⊗[O] B) := inferInstance
  exact UpperTheory.V.Pa.BC.chain_lift B (O' ⊗[O] B) h p e hp he
