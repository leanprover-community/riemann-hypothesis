module

public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.NilToPhiAlt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PDvdOfNil
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PNilRho
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PNilWeil
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PPhiKNil
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PWdModel
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

@[expose] public section

theorem UpperTheory.Ru.crystallineComparison.nilToPhi :
    UpperTheory.Ru.crystallineComparison.NilToPhi := by
  intro l _ P AI hT ι E Ω _ _ _ _ _ A w h O _ _ _ Bw hj a r LL r' hm hcr Q hN s u hu hQ
  refine ⟨(GlobalTheory.Pst.IsModel.isCrysAt_iff P hm).2 hcr, ?_⟩
  exact UpperTheory.Gal.crystallineComparison.phiKNil_of UpperTheory.Gal.crystallineComparison.dvdOfNil_of UpperTheory.Gal.crystallineComparison.nilWeil_of
    UpperTheory.Gal.crystallineComparison.nilRho_of UpperTheory.Gal.crystallineComparison.wdModel_of l P AI hT ι E Ω A w h O Bw hj a r LL r' hm hcr
    Q hN s u hu hQ
