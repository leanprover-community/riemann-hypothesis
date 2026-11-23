module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.OneSTr
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
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

@[expose] public section

open CrystallineSemistableComparison.Pb.Kap

namespace GlobalTheory.CompanionTheory.KapRho

theorem rho_add {Λ A B K : Type} [CommRing Λ] [CommRing A] [CommRing B] [Field K]
    (C : Chain.{1} Λ A B K) {j : ℕ} (x y : ∀ n, C.S n j) (f g : Module.Dual K (C.V j) →+ B) :
    C.Rho x f → C.Rho y g → C.Rho (x + y) (f + g) := by
  rintro ⟨hf, e₁, z₁, hz₁, hb₁⟩ ⟨hg, e₂, z₂, hz₂, hb₂⟩
  refine ⟨fun k φ => by simp only [AddMonoidHom.add_apply, hf, hg, mul_add], e₁ + e₂,
    ((C.ℓ : A) ^ e₂) • z₁ + ((C.ℓ : A) ^ e₁) • z₂, fun n => ?_, fun {m} bs => ?_⟩
  · simp only [map_add (f := _), map_smul, hz₁, hz₂, Pi.add_apply]
    rw [pow_add]
    module
  · simp only [AddMonoidHom.add_apply, add_smul, Finset.sum_add_distrib, map_add (f := _),
      LinearMap.map_smulₛₗ, map_pow, map_natCast, ← hb₁ bs, ← hb₂ bs]
    rw [pow_add]
    module

end GlobalTheory.CompanionTheory.KapRho
