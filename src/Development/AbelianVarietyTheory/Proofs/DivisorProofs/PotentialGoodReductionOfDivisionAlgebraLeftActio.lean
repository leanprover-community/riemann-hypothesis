module

public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PotentialGoodReductionOfDivisionAlgebraOrderActiStatement
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
namespace GlobalTheory

theorem potModel_of_divAlg_leftAction : ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (A : Over (Sp K)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (O : Type) [Ring O] (act : O → (A ⟶ A)), (∀ a, IsMonHom (act a)) → act 1 = 𝟙 A → (∀ a b, act (a * b) = act b ≫ act a) → (∀ a b, act (a + b) = act a * act b) → ∀ (B : Type) [Ring B] [Algebra ℚ B] [Module.Finite ℚ B] (jj : O →+* B), (∀ x : B, x ≠ 0 → IsUnit x) → Function.Injective jj → Submodule.span ℚ (Set.range jj) = ⊤ → g < Module.finrank ℚ B → GlobalTheory.SS.PotModel V K A (fun _ _ _ G _ => IsAbelianScheme G) := by
  intro V K _ _ _ _ _ _ _ _ A _ g hA hg O _ act hmon h1 hmul hadd B _ _ _ jj hunit hinj hspan hdim
  haveI : Module.Finite ℚ Bᵐᵒᵖ :=
    Module.Finite.equiv (MulOpposite.opLinearEquiv ℚ (M := B))
  refine GlobalTheory.T.potentialGoodReduction_of_divisionAlgebra_order_action V K A g hA hg Oᵐᵒᵖ (fun a => act a.unop) (fun a => hmon a.unop) h1
    (fun a b => hmul b.unop a.unop) (fun a b => hadd a.unop b.unop) Bᵐᵒᵖ (RingHom.op jj)
    ?_ ?_ ?_ ?_
  · intro x hx
    have hx' : x.unop ≠ 0 := by simpa using hx
    simpa using (hunit x.unop hx').op
  · intro a b h
    exact MulOpposite.unop_injective (hinj (MulOpposite.op_injective h))
  · have : Set.range (RingHom.op jj) = (MulOpposite.opLinearEquiv ℚ (M := B)) '' Set.range jj := by
      ext x; constructor
      · rintro ⟨a, rfl⟩; exact ⟨jj a.unop, ⟨a.unop, rfl⟩, rfl⟩
      · rintro ⟨_, ⟨a, rfl⟩, rfl⟩; exact ⟨MulOpposite.op a, rfl⟩
    rw [this, ← LinearEquiv.coe_coe, Submodule.span_image, hspan, Submodule.map_top, LinearEquiv.range]
  · rwa [(MulOpposite.opLinearEquiv ℚ (M := B)).symm.finrank_eq]

end GlobalTheory
