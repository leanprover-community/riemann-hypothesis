module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EigenvectorLieDegree
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsLieEigenbasisOfLocalizationsAtPrime
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.CMLattices.IsCyclotomicExtensionCyclotomicField28
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VecMulMapEqZero
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsAbelianGaloisHost
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.CM GlobalTheory.FlatDegreeCompare Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj GlobalTheory.FlatRow

theorem _root_.GlobalTheory.T.isLieEigenbasis_of_localizations_atPrime : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) (R : Type) [CommRing R] (t : SAB H (Sp R)) (χ : 𝓞 E →+* R) (m : ℕ) (v : Fin m → (epsR R ⟶ t.G)), (∀ (p : Ideal R) [p.IsPrime], ∃ (t' : SAB H (Sp (Localization.AtPrime p))) (n : SABMap t' t (spMap (algebraMap R (Localization.AtPrime p)))) (v' : Fin m → (epsR (Localization.AtPrime p) ⟶ t'.G)), (∀ i, IsVecOver (algebraMap R (Localization.AtPrime p)) n.φ (v i) (v' i)) ∧ EigenvectorLieDegree.IsEigBasis t'.act ((algebraMap R (Localization.AtPrime p)).comp χ) v') → EigenvectorLieDegree.IsEigBasis t.act χ v := by
  first | exact @GlobalTheory.FlatRow.isEigBasis_of_local | exact GlobalTheory.FlatRow.isEigBasis_of_local | (intros; apply GlobalTheory.FlatRow.isEigBasis_of_local <;> assumption)
