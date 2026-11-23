module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PhiOfDivOf
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DenseSplitFrobInvAway
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TripleAtt

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.Gal.TP.Sub (Cl Above unrPol)
open UpperTheory.Gal.crystallineComparison (GenericMul rootPol)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.BlockSum (blockRep)
open PositivityTheory.AutomorphicGaloisHodgeTate.Div (DivWCoreLac SenWLac HTLac IsSSMat)
open UpperTheory.Gal.Int.Div

theorem UpperTheory.Gal.Int.Div.divUniq_of :
    DenseUs → DivUniq := by
  classical
  intro hD E Ω _ _ _ _ _ _ l _ ι a d hd U hU r r' hr hr'
  obtain ⟨hc, hs, V, X, hVo, hVd, h⟩ := hr
  obtain ⟨hc', hs', V', X', hVo', hVd', h'⟩ := hr'
  have hS := hD E Ω l a d hd U hU (X ∪ X')
  have hI := (hS.inter_of_isOpen_right hVd hVo).inter_of_isOpen_right hVd' hVo'
  refine GlobalTheory.SplitAttUniq.repIso_of_dense r r' hc hc' hs hs' _
    (hI.preimage (Homeomorph.inv (G E Ω)).isOpenMap) ?_
  rintro g ⟨⟨⟨w, hw, hus, hl, ⟨B, hB⟩, A, hP, hF⟩, hV⟩, hV'⟩
  have hwX : w ∉ X := fun hx => hw (Finset.mem_union_left _ hx)
  have hwX' : w ∉ X' := fun hx => hw (Finset.mem_union_right _ hx)
  have e1 := (h w hwX hus hl B hB A hP).2 g⁻¹ hF hV
  have e2 := (h' w hwX' hus hl B hB A hP).2 g⁻¹ hF hV'
  rw [inv_inv] at e1 e2
  exact Polynomial.map_injective ι.toRingHom ι.injective (e1.trans e2.symm)
