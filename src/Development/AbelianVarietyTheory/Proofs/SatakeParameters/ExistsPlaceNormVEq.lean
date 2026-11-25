module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BcDefs
public import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.FinrankAdjoinSqrtNegOne
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PlaceOverTransportRingIso
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
public import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.RamificationIdxEqOneAndInertiaDegEqOne
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsWeight

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.Published
open Polynomial

namespace GlobalTheory.PlaceNormDec

theorem exists_place_normV_eq : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (Q : GlobalTheory.RealGal.QCM E Ω) (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω), IsPlaceOver A w → Dec (F := E) A ≤ (UpperTheory.V.Af.Bc.res E Ω ↥Q.K).range → ∃ w' : HeightOneSpectrum (𝓞 ↥Q.K), w'.under (𝓞 E) = w ∧ IsPlaceOver A w' ∧ normV w' = normV w := by
  intro E Ω _ _ _ _ _ Q w A hA hD
  obtain ⟨w', hw', i, hi⟩ := GlobalTheory.PlaceIsoDec.exists_placeIso_of_dec_le_range E Ω (↥Q.K) w A hA hD
  refine ⟨w', ?_, hw', ?_⟩
  · have hl := GlobalTheory.PlaceIsoDec.liesOver_of_isPlaceOver hA hw'
    exact HeightOneSpectrum.ext hl.over.symm
  · obtain ⟨c, -, -, hq, -⟩ := GlobalTheory.WeilTransport.weil_equiv E Ω A w hA (↥Q.K) Ω A w' hw' (RingEquiv.refl Ω) (algebraMap E ↥Q.K) i hi
    exact hq

end GlobalTheory.PlaceNormDec
