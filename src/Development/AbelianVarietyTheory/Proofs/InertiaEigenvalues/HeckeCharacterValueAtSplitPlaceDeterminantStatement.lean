module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPlaceModelPlaceMap
public import Formalism.LocalToGlobal.IndefiniteReal.BridgeTie
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeCharacterValueAtSplitPlaceDeterminant
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsSplitOfMemAdmissibleConjugatePairPlaces

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.Lev Formalism.L2.DIV Formalism.IndefR.Mult



theorem _root_.GlobalTheory.T.heckeCharacter_value_at_splitPlace_determinant : ∀ {D : D7} (c : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E) (Q : Finset (Pl D.host.E)) (V : HSp D) (P : Pl D.host.E) (k : ℕ) (α : GA D V) (z : (AE D)ˣ), ChrEq c χ → GlobalTheory.ExportSeries.UnramOutside c Q → GlobalTheory.ExportSeries.SplitSet Q → Bridge.SplitOff P (Q : Set (Pl D.host.E)) → IsHeckeAt V P k α → IsDetAt (idemAt P) V α z → ((c z : Circle) : ℂ) = ((χ.val P : ℂˣ) : ℂ) ^ k := by
  first | exact @GlobalTheory.HeckeDetValue.chr_detAt | exact GlobalTheory.HeckeDetValue.chr_detAt | (intros; apply GlobalTheory.HeckeDetValue.chr_detAt <;> assumption)
