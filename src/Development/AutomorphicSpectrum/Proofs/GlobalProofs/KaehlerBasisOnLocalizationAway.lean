module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R ReciprocityTheory.ChartRestriction.G.Geo.ResK

namespace GlobalTheory.CompanionTheory.Glob.ResKCoords

theorem isCoords_basicOpen_of_away :
    ∀ (K : Type) [Field K] (Y : Scheme.{0}) (g : Y ⟶ Sp K) (U : Y.affineOpens) (s : Γ(Y, U.1)) {n : ℕ}
      (x : Fin n → Γ(Y, U.1)),
      (letI := secAlgebra g U.1;
        ∀ (B : Type) [CommRing B] [Algebra Γ(Y, U.1) B] [Algebra K B] [IsScalarTower K Γ(Y, U.1) B]
          [IsLocalization.Away s B],
          LinearIndependent B (fun i => KaehlerDifferential.D K B (algebraMap Γ(Y, U.1) B (x i))) ∧
            Submodule.span B (Set.range fun i =>
              KaehlerDifferential.D K B (algebraMap Γ(Y, U.1) B (x i))) = ⊤) →
        IsCoords g (Y.basicOpen s) (fun i => Y.presheaf.map (homOfLE (Y.basicOpen_le s)).op (x i)) := by
  intro K _ Y g U s n x h
  letI aU : Algebra K Γ(Y, U.1) := secAlgebra g U.1
  letI aB : Algebra K Γ(Y, Y.basicOpen s) := secAlgebra g (Y.basicOpen s)
  letI aUB : Algebra Γ(Y, U.1) Γ(Y, Y.basicOpen s) :=
    (Y.presheaf.map (homOfLE (Y.basicOpen_le s)).op).hom.toAlgebra
  haveI tower : IsScalarTower K Γ(Y, U.1) Γ(Y, Y.basicOpen s) := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    change ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ g.appLE ⊤ (Y.basicOpen s) (fun _ _ => trivial)).hom = _
    have e : g.appLE ⊤ U.1 (fun _ _ => trivial) ≫ Y.presheaf.map (homOfLE (Y.basicOpen_le s)).op =
        g.appLE ⊤ (Y.basicOpen s) (fun _ _ => trivial) := by
      exact Scheme.Hom.appLE_map _ _ _
    rw [← e]
    rfl
  haveI loc : IsLocalization.Away s Γ(Y, Y.basicOpen s) := U.2.isLocalization_basicOpen s
  exact h Γ(Y, Y.basicOpen s)

end GlobalTheory.CompanionTheory.Glob.ResKCoords
