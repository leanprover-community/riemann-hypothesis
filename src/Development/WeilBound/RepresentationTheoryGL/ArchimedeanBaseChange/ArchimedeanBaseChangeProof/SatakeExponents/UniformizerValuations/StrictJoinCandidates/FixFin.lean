module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.StrictJoinCandidates.FrameExOf
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdmissibleOfFiniteLengthSubquotientsStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteLengthOfProductsStatement
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.BernsteinZelevinskyGL.TopAdm
import GroundTheory.LocalFields.PadicLogSeries
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

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BCT
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.FX

open PositivityTheory.Rg.BcB.F

theorem fixFin : FixFin := by
  intro E _ _ _ n D w K hKo hKc
  have hs : IsSmooth (Tail.prodAt D w) := GlobalTheory.SmGL.isSmooth_parInd _ _
  have hfl : HasFiniteLength (Tail.prodAt D w) :=
    GlobalTheory.T.finite_length_of_products (w.adicCompletion E) (Fin n) (Fin D.c) (fun i => Fin (D.N i)) (GlobalTheory.SmGL.stdBlocks D.N D.h)
      (fun i => (D.σ i w).V) (fun i => (D.σ i w).ρ) (fun i => (D.σ i w).smooth) (fun i => (D.σ i w).irred)
  have hadm : IsAdmissible (Tail.prodAt D w) :=
    GlobalTheory.T.admissible_of_finite_length_subquotients (Tail.prodAt D w) hs hfl fun W _ _ σ hsub hirr =>
      PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top (w.adicCompletion E) n W σ (hsub.isSmooth hs) hirr
  exact hadm.2 K hKo hKc

end PositivityTheory.Rg.BcB.F.FX

end
