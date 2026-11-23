module

public import Development.EtaleCohomology.KummerTheory.InjSlice
public import Development.EtaleCohomology.KummerTheory.EtaleNormalizedFreeChainsDifferentialOneZeroEqZe
public import Development.EtaleCohomology.KummerTheory.PrimIsPrimitiveRoot
public import Development.EtaleCohomology.KummerTheory.PrimTorsPf
public import Development.EtaleCohomology.KummerTheory.ResNegZero
public import Development.EtaleCohomology.KummerTheory.ShSectPf
public import Development.EtaleCohomology.KummerTheory.StalkPf
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
public import Development.EtaleCohomology.KummerTheory.EtaleKummerDegreeZeroCohomologyOfTwistSectionCla
public import Development.EtaleCohomology.KummerTheory.SecSHPf

@[expose] public section

theorem LateralTheory.Fix.Stalk.intersectionNumber_baseChange : LateralTheory.KummerTheory.Stalk := by
  have hT : LateralTheory.KummerTheory.TwSec :=
    LateralTheory.KummerTheory.TwSec_of LateralTheory.KummerTheory.PrimTors_of
      (LateralTheory.KummerTheory.SecSH_of LateralTheory.KummerTheory.ShSectPf.ShSect_of)
  exact LateralTheory.KummerTheory.Stalk_of
    (LateralTheory.KummerTheory.etale_kummer_degree_zero_cohomology_of_twist_section_class_and_root_ex hT (LateralTheory.KummerTheory.Cls0_of hT)
      (LateralTheory.KummerTheory.OneEx_of hT LateralTheory.KummerTheory.TwRes0_of LateralTheory.KummerTheory.Sec0Ex_of))
