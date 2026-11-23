module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Definitions.Degenerations.IsNormalSchemeSp
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

noncomputable section

namespace GlobalTheory.Models

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

section Amp

variable {D : Datum H} {Xo : ∀ l : Level H, Moduli D l}

end Amp

section Refl

variable {U : Scheme.{0}} {F O : Type} [Field F] [CommRing O] {c : U ⟶ Sp F} {t₀ : SAB H U} {β : O →+* F}

end Refl

section Abelian

variable {O F : Type} [CommRing O] [Field F] (β : O →+* F) {X : Scheme.{0}} (s : X ⟶ Sp O) (t : SAB H X)

variable (A : Over X) [GrpObj A] [IsCommMonObj A] (hA : IsAbelianScheme A)

end Abelian

theorem flat_projSpace (R : Type) [CommRing R] (N : ℕ) : Flat (PSpace.str R N) :=
  haveI : IsZariskiLocalAtSource @Flat.{0} := HasRingHomProperty.instIsZariskiLocalAtSource
  IsZariskiLocalAtSource.of_openCover (P := @Flat) (ProjSpace.chartCover R N) fun (i : Fin (N + 1)) => by
    change Flat (ProjSpace.chartι R N i ≫ _)
    rw [ProjSpace.chartι_str, HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.2 (inferInstanceAs (Module.Flat R (MvPolynomial _ R)))

theorem isNormalScheme_projSpace (R : Type) [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R] (N : ℕ) :
    Geo.Tor.IsNormalScheme (PSpace R N) := by
  refine (isNormalScheme_iff_pred _).1 (IsNormalScheme.of_forall_exists_isOpenImmersion fun x => ?_)
  obtain ⟨i, y, hy⟩ := (ProjSpace.chartCover R N).exists_eq x
  exact ⟨_, ProjSpace.chartι R N i, ProjSpace.isOpenImmersion_chartι R N i, IsNormalScheme.of_pred (ZJ.isNormalScheme_sp _), y, hy⟩

end GlobalTheory.Models

end
