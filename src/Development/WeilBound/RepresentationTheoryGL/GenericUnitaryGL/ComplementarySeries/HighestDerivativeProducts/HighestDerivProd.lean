module

public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.LeibnizOrd
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeibnizOrderOfExactSequencesStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PhiGpCommutationHoldsStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PhiPgCommutationHolds
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PhiPgRankZeroHoldsStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PsiGpCommutationHoldsStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResidueSequenceHoldsStatement
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.HighestDerivativeProducts.IsSmoothCharDpowM
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

@[expose] public section

namespace GlobalTheory.RgGu.Leib.Hand

theorem leibnizOrd (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    LeibnizOrd k :=
  GlobalTheory.T.leibniz_order_of_exact_sequences k (GlobalTheory.T.residue_sequence_holds k) (GlobalTheory.T.psi_gp_commutation_holds k) (GlobalTheory.T.phi_gp_commutation_holds k) (GlobalTheory.CompanionTheory.BZPsiPG.Hand.psiPG k) (GlobalTheory.CompanionTheory.BZPhiPG.phiPG k)
    (GlobalTheory.T.phi_pg_rank_zero_holds k)

end GlobalTheory.RgGu.Leib.Hand
