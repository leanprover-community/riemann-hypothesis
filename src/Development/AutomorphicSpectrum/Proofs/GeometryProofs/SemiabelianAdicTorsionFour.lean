module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.NonemptyLinearEquivOfPiFinPowFinite
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Twfunct
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

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField GlobalTheory GlobalTheory.PDivGroup GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.CompanionTheory.Ar.HT

theorem tw_funct : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [IsDomain O] [Algebra O C] (hv : v.Integers O) (hp : v (p : C) < 1) (hO : IsAdicComplete (Ideal.span {(p : O)}) O) (S : Scheme.{0}) [IsLocallyNoetherian S] (G : Over S) [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G) (y : Spec (CommRingCat.of O) ⟶ S) (La : Type) [AddCommGroup La] [Module.Free ℤ La] [Module.Finite ℤ La] (X : TorsTower p G y La) (L : Type) [AddCommGroup L] [Module O L] (M : LieModel G y L), (∀ n f g w, X.IsDer M (n + 1) f w → (∀ a : La, g (lev p n a) = f (lev p (n + 1) (p • a))) → X.IsDer M n g w) ∧ ∀ (u : G ⟶ G) [IsMonHom u] (φ : La →+ La) (dφ : L →ₗ[O] L), X.Induces u φ → M.IsDiffOf u dφ → ∀ n (f g : LevGrp La p n → O), (∀ a, g (lev p n a) = f (lev p n (φ a))) → (f ∈ (X.Γ n).btOrder ⊤ → g ∈ (X.Γ n).btOrder ⊤) ∧ ∀ w, X.IsDer M n f w → X.IsDer M n g (w ∘ₗ dφ) :=
  @PositivityTheory.HtPt.Twfunct.tw_funct

end GlobalTheory.CompanionTheory.Ar.HT
