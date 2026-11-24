module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.HeckeCl
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PBcSplits
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PIsoPts
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PPtsOfSplits
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PSplitsBasic
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PSplitsPts
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.IsAdmissibleIntegralBasisChangeOne

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV UpperTheory.Gal.G3

private theorem bcSplits : BcSplits :=
  pBcSplits (pSplitsBasic (pSplitsPts pIsoPts) pPtsOfSplits)

theorem UpperTheory.Gal.crystallineComparison.Br.trBc :
    UpperTheory.Gal.crystallineComparison.Br.TrBc := by
  intro B B' R _ T g Z Y p q s _ _ hs tr htr W r c hc J _ σ hσ hsp x
  exact htr _ (pullback.snd r g) (UpperTheory.Gal.G3.bcMap g c hc) (bcMap_snd g c hc) J
    (fun j ↦ UpperTheory.Gal.G3.bcMap g (σ j) ((hσ j).trans rfl)) (fun j ↦ bcMap_snd g (σ j) _)
    ((bcSplits g p q r s hs c hc J σ hσ).2.2 hsp) x
