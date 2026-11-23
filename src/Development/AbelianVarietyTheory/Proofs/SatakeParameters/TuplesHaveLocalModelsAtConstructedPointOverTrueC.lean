module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HasPartAnd
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaSeriesDataHypothesesBelowMaximalLevel
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TuplesHaveLocalModelsOfStandardColumnObjectsStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TuplesLocalModelsOfOtherDivisionLatticesHeightsStatement
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Ker Formalism.L2.Forms GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Svd NumberField IsDedekindDomain

namespace GlobalTheory.Svd

theorem modelsAt_bpt : GlobalTheory.TwV.Lt.AdmAtEnt2 → GlobalTheory.TwV.Lt.CurveEx → ∀ (K : Ctx) (β : BPt K), β.Is (positionOf HasPart) → ModelsAt β.D β.O := by
  intro h1 h2 K β hβ
  have key : ∀ O : Obj β.X.toD7, ofObj O = β.c.O → ModelsAt β.X.toD7 O := by
    refine positionOf_ind (P := HasPart) (R := fun K X f T c => ∀ O : Obj X.toD7, ofObj O = c.O → ModelsAt X.toD7 O) ?_ hβ
    intro K B f T w Z c hc O hO
    obtain ⟨b⟩ := hc
    have b' : Part w Z (ofObj O) := hO ▸ b
    exact GlobalTheory.T.tuplesHaveLocalModels_of_standardColumnObjects h1 h2 B f T w Z O b'
  have hm := key (β.Y.obj β.p) (by rw [ofObj_obj]; exact β.hY)
  exact GlobalTheory.T.tuplesLocalModels_of_otherDivisionLatticesHeights β.X.toD7 (β.Y.obj β.p) (nPrime β.p.L) β.p.ht hm

end GlobalTheory.Svd
