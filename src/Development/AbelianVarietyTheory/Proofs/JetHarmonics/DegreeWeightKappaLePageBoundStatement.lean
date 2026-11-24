module

public import Formalism.LocalToGlobal.ProjectiveLattices.PartitionExtendByZeroAntitone
public import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.OEOsInjective
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DegreeWeightKappaLePageBound
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
import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.DepthCond

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.Indef.Tree.DepthCond Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF (AvFSt HTFSt UpFSt)
open GlobalTheory.RunDepth GlobalTheory.CharDepth

theorem _root_.GlobalTheory.T.degree_weightKappa_le_pageBound : ∀ (D : D7) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D), 3 ≤ L.sc.x → (D.R.k : ℝ) * L.sc.b' ≤ L.sc.b → ∀ j, InR D j → (WeightAlgebra.DF (kaR Tp hK j) : ℝ) ≤ (D.R.k : ℝ) * (2 * (D.R.f : ℝ) * L.sc.b + (D.R.f : ℝ) * (L.Sc + L.etaSz)) ∧ ∀ i, (WeightAlgebra.DF (kaR Tp hK j) : ℝ) < ((D.host.g i : ℝ) - 2) / 2 := by
  first | exact @GlobalTheory.RunDepth.DF_kaR_le | exact GlobalTheory.RunDepth.DF_kaR_le | (intros; apply GlobalTheory.RunDepth.DF_kaR_le <;> assumption)
