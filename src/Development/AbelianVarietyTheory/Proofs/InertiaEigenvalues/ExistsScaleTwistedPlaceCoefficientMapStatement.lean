module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockOfApply
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsScaleTwistedPlaceCoefficientMap
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
import Mathlib.Tactic.NormNum.Prime
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)


theorem _root_.GlobalTheory.T.exists_scale_twisted_place_coefficient_map : ∀ (D : D7) (X : RealSide D) (X0 : BaseLevelRowSide D) (Y : GlobalTheory.Mem.R3.Read (A3 := X.A3) X.R.toRealDat X.F.lv2 X0) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS X.R X.cG S) (Z : ExportTie YS X.geo.v₀) (c : NChoice D) (w : D.what₂.places.Pl) (j : Fin D.R.m) (H : AtPlace Y Z c w j),
  ∃ (u : ∀ τ, lowT (X.R.MW j (sg0 D X.A3.A)) τ) (cc : VsV D j ℂ →ₗ[ℂ] (X.R.cV j).W) (κ : ℂ), IsLow X j u ∧ ExtC X.R.toRealDat j (inC (X.geo.O j).c') (X.geo.O j).c0' cc ∧ κ ≠ 0 ∧
    (∀ x, X.R.ioP j (PiTensorProduct.tprod ℂ u) (cc x) ∈ (baseOf Z c w j).valSpace) ∧
    (∀ x : VsV D j ℂ, harmFn (Wc D j).rank (baseOf Z c w j).w (baseOf Z c w j).F.BS (X.R.ioP j (PiTensorProduct.tprod ℂ u) (cc x)) = κ • coefFn (RingHom.id ℂ) (lamV D j) (x : Pol ℂ D.what₂.Tau (Vc D j).rank)) ∧
    IsScale X.R X.geo.v₀ (baseOf Z c w j) κ ∧ IsRoot1 (Z.ν (c.twI w) j (c.sd w) / κ) := by
  first | exact @GlobalTheory.PlaceScale.exists_scale | exact GlobalTheory.PlaceScale.exists_scale | (intros; apply GlobalTheory.PlaceScale.exists_scale <;> assumption)
