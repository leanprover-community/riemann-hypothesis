module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ZKApply
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.CapOComp
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.GrSplit
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.BasisBase

theorem sqC_zK : ∀ {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {I : Ideal A} (γ : DividedPowers I) {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of O)) (l s : ℕ) (𝒱 : Set X.Opens) (a : A) (t u r : ℤ) (ht : t ≤ 0)
    (ha : (smO γ q l s 𝒱).LeC a (sFil _ t) (sFil _ 0)) (hb : (smO γ q l s 𝒱).LeC a (sFil _ u) (sFil _ r)) (j : ℕ)
    (x : HdR q j),
    ((smO γ q l s 𝒱).sqC a ha hb).pull j (GlobalTheory.CompanionTheory.BasisBase.zK q (TO q l s 𝒱) t u ht j x) =
      quoM (TS γ q l s 𝒱) r j (a • muB γ q l s 𝒱 j x) := by
  intro O A _ _ _ I γ X q l s 𝒱 a t u r ht ha hb j x
  obtain ⟨⟨f, hf⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [map_smul]
  change Submodule.Quotient.mk _ = a • Submodule.Quotient.mk _
  rw [← Submodule.Quotient.mk_smul]
  refine congrArg _ (Subtype.ext (funext fun c => ?_))
  refine Subtype.ext ?_
  exact congrArg (Ideal.Quotient.mk _) (Algebra.smul_def _ _).symm

end GlobalTheory.CompanionTheory.BasisBase
