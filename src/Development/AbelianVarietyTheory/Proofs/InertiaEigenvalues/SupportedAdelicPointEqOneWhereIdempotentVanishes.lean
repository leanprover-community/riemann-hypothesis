module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmissibleEmptyOfGood
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.PerCEmb
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.DatEqZero
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IMemSiegel
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
import Development.AbelianVarietyTheory.Definitions.ThetaValues.PolyDerivSmulLetter
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BndMul
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

theorem GlobalTheory.SuppOneIdentity.finPt_entry_eq_one_of_idem_zero : ∀ (D : D7) (ι : (Af D.host.F ⊗[D.host.F] D.host.E) ≃+* FiniteAdeleRing (𝓞 D.host.E) D.host.E) (V : HSp D) (e : AE D) (g : GA D V), SuppAt e V g → ∀ Q : HeightOneSpectrum (𝓞 D.host.E), ι (finPart D (e + cA D e)) Q = 0 → ∀ i j, ((Matrix.GeneralLinearGroup.map ι.toRingHom (finPt V g).1).1 i j) Q = ((1 : Matrix (Fin V.rank) (Fin V.rank) (FiniteAdeleRing (𝓞 D.host.E) D.host.E)) i j) Q := by
  intro D ι V e g hS Q hQ i j
  have hent : ∀ i j, ((finPt V g).1 : Matrix (Fin V.rank) (Fin V.rank) _) i j
      = finPart D (Formalism.L2.Theta.mt V g i j) := fun i j => rfl
  have h1 := congrArg (fun x => ι (finPart D x) Q) (hS i j)
  simp only [map_mul] at h1
  have hm : (ι (finPart D (e + cA D e)) * ι (finPart D ((Formalism.L2.Theta.mt V g - 1) i j))) Q
      = ι (finPart D (e + cA D e)) Q * ι (finPart D ((Formalism.L2.Theta.mt V g - 1) i j)) Q := rfl
  rw [hm, hQ, zero_mul] at h1
  have h2 : ι (finPart D (Formalism.L2.Theta.mt V g i j)) Q
      = ι (finPart D ((1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j)) Q := by
    have hs : (Formalism.L2.Theta.mt V g - 1) i j = Formalism.L2.Theta.mt V g i j - (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j := rfl
    rw [hs, map_sub, map_sub] at h1
    have hsub : (ι (finPart D (Formalism.L2.Theta.mt V g i j)) - ι (finPart D ((1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j))) Q
        = ι (finPart D (Formalism.L2.Theta.mt V g i j)) Q - ι (finPart D ((1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j)) Q := rfl
    rw [hsub] at h1
    exact (sub_eq_zero.mp h1.symm)
  show ι (((finPt V g).1 : Matrix (Fin V.rank) (Fin V.rank) _) i j) Q = _
  rw [hent, h2]
  by_cases hij : i = j
  · subst hij; simp [Matrix.one_apply_eq]
  · simp [Matrix.one_apply_ne hij]
