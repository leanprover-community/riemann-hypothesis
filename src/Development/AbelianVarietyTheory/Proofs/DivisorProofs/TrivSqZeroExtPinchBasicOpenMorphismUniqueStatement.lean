module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HopfLaurent
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrivSqZeroExtPinchBasicOpenMorphismUnique
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.Definitions.Divisors.CommAlgFunctorCoboundaryZeroMemCocyclesOne
import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap
import Development.AbelianVarietyTheory.Definitions.Divisors.Pullback1MemHodgeFiltration
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh GlobalTheory.AbTan
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.trivSqZeroExt_pinch_basicOpen_morphism_unique : ∀ (R : Type) [CommRing R] (B M : Type) [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M] [Module Bᵐᵒᵖ M] [IsCentralScalar B M] [Module R M] [IsScalarTower R B M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M] (β : TrivSqZeroExt R M →+* TrivSqZeroExt B M), IsSum β (algebraMap R B) id → ∀ (X : Scheme.{0}) (x : Sp R ⟶ X) (V : (Sp (TrivSqZeroExt R M)).Opens) (s : Γ((Sp (TrivSqZeroExt R M)), ⊤)), V = (Sp (TrivSqZeroExt R M)).basicOpen s → ∀ (U : X.affineOpens), spMap (TrivSqZeroExt.fstHom R R M).toRingHom ⁻¹ᵁ V ≤ x ⁻¹ᵁ U.1 → ∀ g₁ g₂ : V.toScheme ⟶ X, (spMap (TrivSqZeroExt.fstHom R R M).toRingHom).resLE V _ le_rfl ≫ g₁ = (spMap (TrivSqZeroExt.fstHom R R M).toRingHom ⁻¹ᵁ V).ι ≫ x → (spMap (TrivSqZeroExt.fstHom R R M).toRingHom).resLE V _ le_rfl ≫ g₂ = (spMap (TrivSqZeroExt.fstHom R R M).toRingHom ⁻¹ᵁ V).ι ≫ x → (spMap β).resLE V _ le_rfl ≫ g₁ = (spMap β).resLE V _ le_rfl ≫ g₂ → g₁ = g₂ := by
  first | exact @GlobalTheory.PinchUniq.uniq | exact GlobalTheory.PinchUniq.uniq | (intros; apply GlobalTheory.PinchUniq.uniq <;> assumption)
