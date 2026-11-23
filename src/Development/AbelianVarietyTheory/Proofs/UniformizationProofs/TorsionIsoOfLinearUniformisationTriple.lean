module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.VRatioGtStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PeriodicValuation
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.LinearUniformisationTorsionMapIsLinearStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTorsionIdentificationWithPairingStatement
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
namespace GlobalTheory.UT

theorem torsionIso_of_pelUnif : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → ∀ (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [CharZero R] (I : Ideal R), AdmBase R I → ∀ (t : SAB H (Sp R)) (P : PELUnif I t), P.TorsionIso := by
  intro hL h1 h2 h3 h4 E _ _ _ H R _ _ _ I hI t P F _ _ _ k hk
  letI := H.starRing
  obtain ⟨f, hf⟩ := GlobalTheory.T.uniformisation_torsion_identification_with_pairing hL R I hI P.D P.A t.G t.semi P.U F k hk
  have hadj : ∀ a : NumberField.RingOfIntegers E,
      LBIso (cubeLB t.G ![fst t.G t.G ≫ t.act.toRingAct.act a, snd t.G t.G] P.U.LG.L)
        (cubeLB t.G ![fst t.G t.G, snd t.G t.G ≫ t.act.toRingAct.act (star a)] P.U.LG.L) := by
    intro a
    rw [P.bundle]
    exact t.adj a
  have hlin := GlobalTheory.T.linear_uniformisation_torsion_map_isLinear hL h1 h2 h3 h4 R I hI P.D P.A t.G t.semi P.U F
    (NumberField.RingOfIntegers E) P.oD P.oA t.act.toRingAct P.lin hadj k hk f hf
  exact ⟨f, hf.1, hf.2.1, hf.2.2.1, hf.2.2.2.1, hlin, hf.2.2.2.2⟩
end GlobalTheory.UT
