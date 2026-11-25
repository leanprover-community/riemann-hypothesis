module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.BaseOver
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out

namespace GlobalTheory

theorem torsionSection_eq_labelled_of_isDomain : ∀ (R : Type) [CommRing R] [IsDomain R] (P : PolAV (Sp R)) (M : ℕ) (I : Type) (pt : I → (baseOver (Sp R) ⟶ P.A)), (∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ Sp R) (z : Over.mk x ⟶ P.A), z ^ M = 1 → ∃ a, (Over.homMk x (by simp) : Over.mk x ⟶ baseOver (Sp R)) ≫ pt a = z) → ∀ y : baseOver (Sp R) ⟶ P.A, y ^ M = 1 → ∃ a, pt a = y := by
  intro R _ _ P M I pt h y hy
  let K := AlgebraicClosure (FractionRing R)
  let j : R →+* K := (algebraMap (FractionRing R) K).comp (algebraMap R (FractionRing R))
  have hj : Function.Injective j :=
    (algebraMap (FractionRing R) K).injective.comp (IsFractionRing.injective R (FractionRing R))
  have hdom : IsDominant (Geo.Tor.spMap j) :=
    ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical j).2 (by
      rw [(RingHom.injective_iff_ker_eq_bot j).1 hj]; exact bot_le)⟩
  have hprop : IsProper P.A.hom := P.isAb.proper
  obtain ⟨a, ha⟩ := h K (Geo.Tor.spMap j)
    ((Over.homMk (Geo.Tor.spMap j) (by simp) : Over.mk (Geo.Tor.spMap j) ⟶ baseOver (Sp R)) ≫ y)
    (by rw [← MonObj.comp_pow, hy, MonObj.comp_one])
  exact ⟨a, Over.OverMorphism.ext (ext_of_isDominant_of_isSeparated (X := Sp R) P.A.hom
    ((Over.w (pt a)).trans (Over.w y).symm) (Geo.Tor.spMap j) (congrArg Over.Hom.left ha))⟩

end GlobalTheory
