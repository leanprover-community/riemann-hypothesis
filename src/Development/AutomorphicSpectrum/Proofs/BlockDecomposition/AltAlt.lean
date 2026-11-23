module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.IsCompl
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FaceFaceApply
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CofaceRel
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.WpCoface

theorem alt_alt (A : Type) [CommRing A] (B : Type) [CommRing B] [Algebra A B] (K : ℕ → Type)
    [∀ n, CommRing (K n)] [∀ n, Algebra A (K n)] (ι : ∀ n, Fin n → (B →ₐ[A] K n))
    (δ : ∀ n, Fin (n + 1) → (K n →ₐ[A] K (n + 1))) (hwp : ∀ n, IsWP (ι n))
    (hδ : ∀ n k i, (δ n k).comp (ι n i) = ι (n + 1) (k.succAbove i)) (n : ℕ) (z : K n) :
    alt (δ (n + 1)) (alt (δ n) z) = 0 := by
  have hrel : ∀ (j : Fin (n + 2)) (i : Fin (n + 1)),
      δ (n + 1) (j.succAbove i) (δ n (i.predAbove j) z) = δ (n + 1) j (δ n i z) := fun j i =>
    DFunLike.congr_fun (coface_rel A B K ι δ hwp hδ n j i) z
  have hexp : alt (δ (n + 1)) (alt (δ n) z) = ∑ p : Fin (n + 2) × Fin (n + 1),
      ((-1 : ℤ) ^ (p.1 : ℕ) * (-1 : ℤ) ^ (p.2 : ℕ)) • δ (n + 1) p.1 (δ n p.2 z) := by
    rw [Fintype.sum_prod_type]

    simp only [alt, LinearMap.sum_apply, LinearMap.smul_apply, AlgHom.toLinearMap_apply, map_sum,
    map_zsmul, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by rw [mul_comm]
  rw [hexp]
  refine Finset.sum_involution (fun p _ => (p.1.succAbove p.2, p.2.predAbove p.1)) ?_ ?_ ?_ ?_
  · rintro ⟨j, i⟩ _
    dsimp only
    rw [hrel, GlobalTheory.CatH.DSq.sign_swap, neg_smul, add_neg_cancel]
  · rintro ⟨j, i⟩ _ _ h
    exact Fin.succAbove_ne j i (congrArg Prod.fst h)
  · intro _ _; exact Finset.mem_univ _
  · rintro ⟨j, i⟩ _
    simp only [Fin.succAbove_succAbove_predAbove, Fin.predAbove_predAbove_succAbove]

end GlobalTheory.CompanionTheory.WpCoface
