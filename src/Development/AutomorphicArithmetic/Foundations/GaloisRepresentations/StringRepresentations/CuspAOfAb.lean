module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.StringRepresentations.WeightsConj
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.StringRepresentations.AdmissibleTemperedUnramified
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RankOneUnitary
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Formalism.MainNotions.N
open GlobalTheory GlobalTheory.WeilDeligne UpperTheory.Lit.Car

namespace UpperTheory.GalN

theorem Aw.dim {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w} {x y : WD h} (k : Aw x y) :
    x.lpDim = y.lpDim := by rw [← WD.charPol_natDegree x 1, k.pol, WD.charPol_natDegree]

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N}

theorem relA_of_ab (T : GlobalTheory.RowTie.WDTie N A) {w : PlE H} {x y : A.LP w} (h : Ab (T.e w x) (T.e w y)) : RelA N A x y := by
  refine ⟨by rw [← T.dim, ← T.dim, h.dim], by rw [T.mono0, T.mono0]; exact h.mono, fun hy σ hσ => ?_⟩
  rw [T.inePol _ _ σ hσ, T.inePol _ _ σ hσ]
  rw [WD.inePol_of_mem_Ine _ hσ, WD.inePol_of_mem_Ine _ hσ]
  refine h.ine ((T.mono0 _ _).1 hy.1) (fun g hg => ?_) _ (deg_ineIncl _)
  have e := hy.2 g hg
  rw [T.inePol _ _ _ (comm_le_ine w hg), WD.inePol_of_mem _ g.2, ← T.dim] at e
  exact e

theorem cuspA_of_ab (T : GlobalTheory.RowTie.WDTie N A) {w : PlE H} {x y : A.LP w} (h1 : A.lpDim y ≠ 1)
    (h : Ab (T.e w x) (T.e w y)) : CuspA N A x y := ⟨relA_of_ab T h, fun e => absurd e h1⟩

end UpperTheory.GalN
