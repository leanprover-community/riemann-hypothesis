module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ExistsPrimitiveRootPow
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GeneratorCountTuples.LemmaK
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Counts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.LayerLe
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CMFieldExponentialBounds.AdmissibleOfPageN
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.CountIV
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.CountVs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.FinalLe
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.PointArith
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.SumOut
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.ThmHV
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

@[expose] public section

open Formalism.GaloisCohomology UpperTheory.Top

namespace UpperTheory.V.HV

theorem pointHV_of_counts (hP : GlobalTheory.Published.PoitouTateDuality) (hF : LocalFinitenessK) (hT : LocalTateDualityK) {CK : ℝ}
    (hK : LemmaK CK) (h1 : CountI) (h2 : CountII) (h3 : CountIII) (h5 : CountV) (hZ : CountZ) : PointHV :=
  point (sumIn h2 h5 (countVs hP hF hT CK hK) countIV) (sumOut h1 hZ h2 h3)

theorem thmHV_of_counts (hP : GlobalTheory.Published.PoitouTateDuality) (hF : LocalFinitenessK) (hT : LocalTateDualityK) {CK : ℝ}
    (hK : LemmaK CK) (h1 : CountI) (h2 : CountII) (h3 : CountIII) (h5 : CountV) (hZ : CountZ) (K : BConst) {Ct : ℝ}
    (hC : 0 < Ct) : ThmHV K Ct :=
  thmHV (pointHV_of_counts hP hF hT hK h1 h2 h3 h5 hZ) K Ct hC

theorem jointWin_of_counts (hP : GlobalTheory.Published.PoitouTateDuality) (hF : LocalFinitenessK) (hT : LocalTateDualityK) {CK : ℝ}
    (hK : LemmaK CK) {K : BConst} (hB : ThmBab K 401) (h1 : CountI) (h2 : CountII) (h3 : CountIII) (h5 : CountV)
    (hZ : CountZ) : JointWin 401 :=
  jointWin_of (by norm_num) hB (thmHV_of_counts hP hF hT hK h1 h2 h3 h5 hZ K (by norm_num))

theorem vwin_of_counts (hP : GlobalTheory.Published.PoitouTateDuality) (hF : LocalFinitenessK) (hT : LocalTateDualityK) {CK : ℝ}
    (hK : LemmaK CK) {K : BConst} (hB : ThmBab K 401) (hc : ThmBcFree) (h1 : CountI) (h2 : CountII) (h3 : CountIII)
    (h5 : CountV) (hZ : CountZ) : VWin :=
  vwin_of_joint (jointWin_of_counts hP hF hT hK hB h1 h2 h3 h5 hZ) ((thmBc_iff (by norm_num)).2 hc)

end UpperTheory.V.HV
