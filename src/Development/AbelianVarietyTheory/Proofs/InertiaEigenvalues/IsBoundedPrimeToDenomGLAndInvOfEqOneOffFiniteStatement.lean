module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BndMul
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsBoundedPrimeToDenomGLAndInvOfEqOneOffFinite
import Formalism.LocalRingCardinality.DataHost
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.PerCEmb
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmissibleEmptyOfGood
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.DatEqZero
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IMemSiegel
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsInertTop
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector

@[expose] public section

open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ExportSeries (Base Twist Weight PairRep GLR detChar detFam fockGL harm harmLat IsCoefRing finPt series idem)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SingleDatum

open GlobalTheory.StdAtPrime


theorem _root_.GlobalTheory.T.isBoundedPrimeToDenom_GL_and_inv_of_eq_one_off_finite : ∀ {E : Type} [Field E] [NumberField E] (p : ℕ), p.Prime → ∀ (n : ℕ) (G : GL (Fin n) (FiniteAdeleRing (𝓞 E) E)) (S : Set (HeightOneSpectrum (𝓞 E))), S.Finite → (∀ Q ∈ S, (p : 𝓞 E) ∉ Q.asIdeal) → (∀ Q ∉ S, ∀ i j, (G.1 i j) Q = ((1 : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E)) i j) Q) → Bnd p G.1 ∧ Bnd p (G⁻¹).1 := by
  first | exact @GlobalTheory.StdAtPrime.bnd_and_bnd_inv_of_eq_one_off_finite | exact GlobalTheory.StdAtPrime.bnd_and_bnd_inv_of_eq_one_off_finite | (intros; apply GlobalTheory.StdAtPrime.bnd_and_bnd_inv_of_eq_one_off_finite <;> assumption)
