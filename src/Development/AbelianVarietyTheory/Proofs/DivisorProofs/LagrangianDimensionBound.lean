module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Dimension.Finrank
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulTransposeInjective
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.MixedLagr
open GlobalTheory.Doubling (absE)

namespace GlobalTheory

theorem finrank_le_card_of_isotropic_prod_pi (F : Type) [Field F] (κ : Type) [Fintype κ]
    (L : Submodule F ((κ → F) × (κ → F)))
    (hL : ∀ a ∈ L, ∀ b ∈ L, a.1 ⬝ᵥ b.2 = b.1 ⬝ᵥ a.2) :
    Module.finrank F L ≤ Fintype.card κ := by
  classical
  let ω : ((κ → F) × (κ → F)) →ₗ[F] Module.Dual F ((κ → F) × (κ → F)) :=
    LinearMap.mk₂ F (fun b a => a.1 ⬝ᵥ b.2 - b.1 ⬝ᵥ a.2)
      (by intro b b' a; simp [dotProduct_add, add_dotProduct]; ring)
      (by intro c b a; simp [dotProduct_smul, smul_dotProduct]; ring)
      (by intro b a a'; simp [dotProduct_add, add_dotProduct]; ring)
      (by intro c b a; simp [dotProduct_smul, smul_dotProduct]; ring)
  have hω : ∀ b a, ω b a = a.1 ⬝ᵥ b.2 - b.1 ⬝ᵥ a.2 := fun b a => rfl
  have hinj : Function.Injective ω := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro b hb
    have h1 : ∀ i, b.2 i = 0 := by
      intro i
      have := congrArg (fun f => f (Pi.single i 1, 0)) hb
      simpa [hω, single_dotProduct] using this
    have h2 : ∀ i, b.1 i = 0 := by
      intro i
      have := congrArg (fun f => f (0, Pi.single i 1)) hb
      simpa [hω, dotProduct_single] using this
    exact Prod.ext (funext h2) (funext h1)
  let g : L →ₗ[F] L.dualAnnihilator :=
    ((ω.domRestrict L).codRestrict L.dualAnnihilator (by
      intro b
      rw [Submodule.mem_dualAnnihilator]
      intro a ha
      simp only [LinearMap.domRestrict_apply, hω]
      rw [hL a ha b b.2, sub_self]))
  have hg : Function.Injective g := by
    intro x y hxy
    apply Subtype.ext
    apply hinj
    have := congrArg Subtype.val hxy
    simpa [g] using this
  have h1 := LinearMap.finrank_le_finrank_of_injective hg
  have h2 := Subspace.finrank_add_finrank_dualAnnihilator_eq L
  have h3 : Module.finrank F ((κ → F) × (κ → F)) = 2 * Fintype.card κ := by
    rw [Module.finrank_prod, Module.finrank_fintype_fun_eq_card]; ring
  omega

end GlobalTheory
