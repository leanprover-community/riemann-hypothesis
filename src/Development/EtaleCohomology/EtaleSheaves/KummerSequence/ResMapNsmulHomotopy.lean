module

public import Development.EtaleCohomology.EtaleSheaves.KummerSequence.KummerH0Surjection
public import Development.EtaleCohomology.EtaleSheaves.KummerSequence.LeafKumMuPf
public import Development.EtaleCohomology.EtaleSheaves.KummerSequence.GmSepPf
public import Development.EtaleCohomology.EtaleSheaves.KummerSequence.LeafKumMuInjPfGlue
public import Development.EtaleCohomology.EtaleSheaves.KummerSequence.LeafKumMuMapPf
public import Development.EtaleCohomology.EtaleSheaves.KummerSequence.LeafKumMuSurjPowPf
public import Development.EtaleCohomology.EtaleSheaves.KummerSequence.LeafKumMuSurjPrimPf
public import Development.EtaleCohomology.EtaleSheaves.KummerSequence.LeafUnitRootPf
public import Development.EtaleCohomology.EtaleSheaves.KummerSequence.TwLocGenPf
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
public import Development.EtaleCohomology.EtaleSheaves.KummerSequence.LeafKumMuSurjPf
public import Development.EtaleCohomology.EtaleSheaves.KummerSequence.LeafKumSecSurjPf

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex CochainComplex.HomComplex

namespace LateralTheory.E.H2CurveOrder

open LateralTheory.E.E4 LeafKumSeqPf KummerH0Surjection

theorem muUnits : LeafKumMuPf.LeafKumMuUnits := by
  have hI := LeafKumMuInjPfGlue.LeafKumMuInj_of TwLocGenPf.TwLocGen_of GmSepPf.GmSep_of
  exact LeafKumMuUnitsPf.LeafKumMuUnits_of LeafKumMuMapPf.LeafKumMuMap_of hI
    (LeafKumMuSurjPf.etale_mu_twist_sections_surj_of_prim_root_pow_inj LeafKumMuSurjPrimPf.LeafKumMuSurjPrim_of
      LeafKumMuSurjPowPf.LeafKumMuSurjPow_of hI)

theorem kumSecSurj : LeafKumSecSurj := LeafKumSecSurjPf.LeafKumSecSurj_of LeafUnitRootPf.LeafUnitRoot_of

end LateralTheory.E.H2CurveOrder

end
