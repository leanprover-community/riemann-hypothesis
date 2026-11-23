module

public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.PushComparisonBijectiveOfIsClosedEmbedding
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.CechToDerived
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.HdimEqZeroOfSubsingleton
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
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.InstAddCommGroup
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.CechDifferentialPullback.PullCochMemCoboundaries
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.HodgeC
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ConsCompSuccAboveZero

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits GroundTheory.Arith.SchemeCoh GlobalTheory.SheafPull CrystallineSemistableComparison CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Cech

namespace GlobalTheory.CompanionTheory.CechLift

theorem exists_injectiveSequence_lift {X Y : TopCat.{0}} (f : X ⟶ Y) {G : AbSheaf Y} {G' : AbSheaf X}
    (φ : G ⟶ (push f).obj G') :
    ∃ α : injectiveSequence G ⟶ (injectiveSequence G').map (push f), α.τ₁ = φ := by
  have hS := injectiveSequence_shortExact G
  have : Mono (injectiveSequence G).f := hS.mono_f
  have : Injective ((push f).obj (injectiveSequence G').X₂) := injective_push f _
  let τ₂ : (injectiveSequence G).X₂ ⟶ (push f).obj (injectiveSequence G').X₂ :=
    Injective.factorThru (φ ≫ (push f).map (injectiveSequence G').f) (injectiveSequence G).f
  have h₁ : (injectiveSequence G).f ≫ τ₂ = φ ≫ (push f).map (injectiveSequence G').f :=
    Injective.comp_factorThru _ _
  have h₀ : (injectiveSequence G).f ≫ τ₂ ≫ (push f).map (injectiveSequence G').g = 0 := by
    rw [← Category.assoc, h₁, Category.assoc, ← Functor.map_comp, (injectiveSequence G').zero,
      Functor.map_zero, comp_zero]
  let τ₃ := hS.gIsCokernel.desc (CokernelCofork.ofπ _ h₀)
  have h₃ : (injectiveSequence G).g ≫ τ₃ = τ₂ ≫ (push f).map (injectiveSequence G').g :=
    Cofork.IsColimit.π_desc hS.gIsCokernel
  exact ⟨{ τ₁ := φ, τ₂ := τ₂, τ₃ := τ₃, comm₁₂ := h₁.symm, comm₂₃ := h₃.symm }, rfl⟩

end GlobalTheory.CompanionTheory.CechLift
