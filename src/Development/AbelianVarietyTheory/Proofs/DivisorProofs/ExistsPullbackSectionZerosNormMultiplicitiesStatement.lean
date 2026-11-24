module

public import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JGenSpecializes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPullbackSectionZerosNormMultiplicities
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

theorem _root_.GlobalTheory.T.exists_pullback_section_zeros_norm_multiplicities : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (σ : k →+* ℂ) (π : Y ⟶ X) (hπ : π ≫ p = q) (M : MLine p σ) (s : M.B.Sec), ∃ s' : (M.pull π hπ).B.Sec, nonzeroLocus s' = π ⁻¹ᵁ nonzeroLocus s ∧ (∀ y, (M.pull π hπ).φ.nsq (secVal q σ s') y = M.φ.nsq (secVal p σ s) (ptMap π hπ σ y)) ∧ ∀ [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian Y] (hη : π (genericPoint Y) ⤳ genericPoint X) (hs : genericPoint X ∈ nonzeroLocus s) (hs' : genericPoint Y ∈ nonzeroLocus s') (w : Y) (i : M.B.ι), π w ∈ M.B.U i → (divOfSec (M.pull π hπ).φ.isLB s' hs').mult w = Scheme.ord (TrueGeo.SmallSec.fnMap π hη (ratOfSec s hs i : X.functionField)) w := by
  first | exact @GlobalTheory.Mix.exists_secPull_props | exact GlobalTheory.Mix.exists_secPull_props | (intros; apply GlobalTheory.Mix.exists_secPull_props <;> assumption)
