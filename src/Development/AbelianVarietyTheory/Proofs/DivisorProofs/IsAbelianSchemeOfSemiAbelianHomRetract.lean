module

public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
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
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem isAbelianScheme_of_retract_of_isSemiAbelian : ∀ (S : Scheme.{0}) (A G : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj G] [IsCommMonObj G] (inc : G ⟶ A) (pr : A ⟶ G), IsAbelianScheme A → IsSemiAbelian G → IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 G → IsAbelianScheme G := by
  intro S A G _ _ _ _ inc pr hA hG _ _ h
  have hApr : IsProper A.hom := hA.proper
  have hsep : IsSeparated G.hom := hG.separated
  have hpr : IsSeparated pr.left := by
    have e : pr.left ≫ G.hom = A.hom := Over.w pr
    have : IsSeparated (pr.left ≫ G.hom) := by rw [e]; infer_instance
    exact IsSeparated.of_comp pr.left G.hom
  have hid : inc.left ≫ pr.left = 𝟙 G.left := by rw [← Over.comp_left, h, Over.id_left]
  have hci : IsClosedImmersion inc.left := by
    have : IsClosedImmersion (inc.left ≫ pr.left) := by rw [hid]; infer_instance
    exact IsClosedImmersion.of_comp inc.left pr.left
  refine ⟨hG.comm, hG.smooth, ?_, hG.geomConnected⟩
  have e : inc.left ≫ A.hom = G.hom := Over.w inc
  rw [← e]
  infer_instance

end GlobalTheory
