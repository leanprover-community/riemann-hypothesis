module

public import Development.AbelianVarietyTheory.Definitions.Divisors.CommGroupMulMulEqMulInvMulMulMul
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
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsChartOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
import Development.AbelianVarietyTheory.Definitions.Divisors.LinearIndependentBasisCoords
import Development.AbelianVarietyTheory.Definitions.Divisors.MemSubPtsCutBaseChangeIff
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnitaryWeightExponentVectorSignatureWeightMuZero
import Formalism.LocalRingCardinality.SpanPowerMembership.HasStrictFDerivAtExpZero
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.EllipsoidStA

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

namespace GlobalTheory.Vanishing.ProdNe

theorem eq_zero_of_germ_eq_zero {k : Type} [CommRing k] {Y : Scheme.{0}} [IsIntegral Y]
    {p : Y ⟶ Sp k} {B : LB Y} (hc : ∀ z : Y, ∃ j, z ∈ B.U j) (f : H0 p B ⊤) (y : Y) (i : B.ι)
    (hi : y ∈ B.U i) (h0 : H0.germ i y (show y ∈ (⊤ : Y.Opens) from trivial) hi f = 0) : f = 0 := by
  have hi0 : f.loc i = 0 := by
    apply germ_injective_of_isIntegral Y y (memInf (U := ⊤) trivial hi)
    rw [map_zero]
    exact h0
  refine H0.ext_germ fun z hz => ?_
  obtain ⟨j, hj⟩ := hc z
  refine ⟨j, hj, ?_⟩
  have hj0 : f.loc j = 0 := by
    obtain ⟨w, hwi, hwj⟩ :=
      nonempty_preirreducible_inter (B.U i).isOpen (B.U j).isOpen ⟨y, hi⟩ ⟨z, hj⟩
    apply germ_injective_of_isIntegral Y w (memInf (U := ⊤) trivial hwj)
    rw [map_zero]
    have e := H0.germ_change (O := ⊤) i j w (show w ∈ (⊤ : Y.Opens) from trivial) hwi hwj f
    have e2 : H0.germ (O := ⊤) i w (show w ∈ (⊤ : Y.Opens) from trivial) hwi f = 0 := by
      rw [H0.germ_apply, hi0, map_zero]
    rw [e2] at e
    rcases mul_eq_zero.mp e.symm with h | h
    · exact absurd h (Units.ne_zero _)
    · exact h
  rw [H0.germ_apply, hj0, map_zero, map_zero]

theorem mul_ne_zero : ∀ {k : Type} [Field k] {Y : Scheme.{0}} [IsIntegral Y] {p : Y ⟶ Sp k} {P B N : LB Y} (C : ProdChart P B N) (σ : H0 p P ⊤) (f : H0 p B ⊤), σ ≠ 0 → f ≠ 0 → C.mul σ f ≠ 0 := by
  intro k _ Y _ p P B N C σ f hσ hf hmul
  obtain ⟨y⟩ := (inferInstance : Nonempty Y)
  obtain ⟨t, ha, hb, hc⟩ := C.cover y
  have e := C.germ_mul σ f t y trivial ha hb hc
  rw [hmul, map_zero] at e
  rcases mul_eq_zero.mp e.symm with h | h
  · exact hσ (eq_zero_of_germ_eq_zero (fun z => let ⟨t, h⟩ := C.cover z; ⟨C.a t, h.1⟩) σ y _ ha h)
  · exact hf (eq_zero_of_germ_eq_zero (fun z => let ⟨t, h⟩ := C.cover z; ⟨C.b t, h.2.1⟩) f y _ hb h)

end GlobalTheory.Vanishing.ProdNe
