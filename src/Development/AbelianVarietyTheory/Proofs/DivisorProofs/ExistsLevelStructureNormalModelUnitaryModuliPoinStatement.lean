module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRatPointOfFiniteType
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelStructureNormalModelUnitaryModuliPoin
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UOver

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.ZH GlobalTheory.UPoinc GlobalTheory.UCovSep
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_levelStructure_normalModel_unitaryModuliPoint : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (x₀ : Xo.XF c) (n : ℕ), n.Prime → Odd n → ∃ g₀ : ℕ, ∀ e : ℕ, ∃ (o₁ Ω : Type) (_ : CommRing o₁) (_ : Field Ω) (_ : Algebra o₁ Ω) (_ : ArithBase o₁ Ω) (ze : o₁ˣ) (uη : Sp Ω ⟶ Xo.XF c) (A₁ : PolAV (Sp Ω)) (_ : Out.Level A₁ (n ^ e) (unitOn (Units.map (algebraMap o₁ Ω).toMonoidHom ze))) (M : RatModel o₁ Ω) (U : C.Z.Opens) (g : M.Z ⟶ U.toScheme), A₁.g = g₀ ∧ IsUnit (n : o₁) ∧ (∀ w, uη w = x₀) ∧ UOver Xo c A₁ (RingHom.id Ω) uη ∧ M.pt ≫ g ≫ U.ι = uη ≫ C.i ∧ GlobalTheory.IsNormalScheme M.Z ∧ IsProjOver M.s ∧ IsFinite g ∧ Set.range (pullback.fst C.z (spMap C.b)) ⊆ (U : Set C.Z) := by
  first | exact @GlobalTheory.UCovSep.GenModel.exists_genModel | exact GlobalTheory.UCovSep.GenModel.exists_genModel | (intros; apply GlobalTheory.UCovSep.GenModel.exists_genModel <;> assumption)
