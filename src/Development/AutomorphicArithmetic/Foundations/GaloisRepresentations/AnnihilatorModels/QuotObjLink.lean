module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.CongKSOf
public import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ExistsHeckeCorrespondenceOnIntegralShimuraModel
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ExistsPIsogenyKernelEqSubgroupScheme
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.IdealSplitHolds
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MEsNorm
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.OrdGen
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

namespace UpperTheory.Gal.crystallineComparison.Mod

theorem esGen_link : EsGen := UpperTheory.Cb.exists_heckeCorrespondence_on_integral_shimuraModel
theorem esNorm_link : EsNorm := esNorm_of esGen_link
theorem ordGen_link : OrdGen := UpperTheory.Gal.Ord.ordGen
theorem quotObj_link : QuotObj := UpperTheory.Cb.exists_pIsogeny_kernel_eq_subgroupScheme
theorem congKS_link : CongKS := congKS_holds esNorm_link esGen_link ordGen_link quotObj_link

end UpperTheory.Gal.crystallineComparison.Mod
