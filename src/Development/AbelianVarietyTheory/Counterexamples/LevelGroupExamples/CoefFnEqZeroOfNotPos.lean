module

public import Formalism.LocalToGlobal.ProjectiveLattices.TieUpA
public import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.NotJInjRdOfConst
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.SiegelSpaceAlgebraHolds
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.CountableOfIsAddFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.MaxCuspKilledCoefficientEqZero
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.MaximalCuspKernels.MaxCuspsSt

@[expose] public section

noncomputable section

namespace GlobalTheory.ReadingTieCheck

open NumberField ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj.FJ Formalism.L2.Pj.QAt MeasureTheory GlobalTheory.TorusFourier GlobalTheory.MaxCuspKilled

section Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r ρ : ℕ}

end Free

section Record

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections

variable {D : D7} {T : Top D} (h : LawsP T) (j : ℕ)

theorem reading_mem_SS (u : WeightFamilies.Wt D j) (F : (recB h.toLawsCore).Cusp j u) (k : (T.U j T.σ₀).Comp) :
    rdR h j F k ∈ ((T.U j T.σ₀).X k).SS (laU (T.U j T.σ₀) (wtA u) u.n k) :=
  readings_holomorphic_cuspForms siegelSpaceAlgebra_holds T.good_σ₀ (wtA u) u.n ⟨F.1, cutR_le T.C j u F.2⟩ k

theorem tieRead_iff : TieReadSt h j ↔ ∀ u : WeightFamilies.Wt D j, JInjRd T j (wtA u) u.n :=
  ⟨fun H => H.2, fun H => ⟨reading_mem_SS h j, H⟩⟩

theorem tieRead_holds (hj : InR D j) : TieReadSt h j :=
  (tieRead_iff h j).2 fun u =>
    GlobalTheory.ReadingIndependence.jInjRd_of_laws T h.toLawsCore.toLawsM hj (wtA u) u.n

end Record

end GlobalTheory.ReadingTieCheck
