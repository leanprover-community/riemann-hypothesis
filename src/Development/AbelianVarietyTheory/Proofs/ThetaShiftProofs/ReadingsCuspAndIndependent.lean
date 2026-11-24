module

public import Formalism.LocalToGlobal.ProjectiveLattices.TieUpA
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CuspFormFrameReadingsLinearIndependent
public import Formalism.LocalToGlobal.ProjectiveLattices.RosatiLatticeNorms.LinkFD
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
import Mathlib.Tactic.NormNum.Prime
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.SiegelSpaceAlgebraHolds
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ModelsAt
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Generic
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.FinitePlaceArcs.BeSumStatement

@[expose] public section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.Pj.QAt Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions GlobalTheory.ArcCM GlobalTheory.Shares

namespace GlobalTheory.ArcRead




theorem readings_cusp_and_independent :
    ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ), InR D j → TieReadSt h j := by
  intro D T h j hj
  refine ⟨fun u F k => ?_, fun u => GlobalTheory.Dict.readings_independent D T h.toLawsM j hj _ _⟩
  have hFC : F.1 ∈ T.C j u := cutR_le T.C j u F.2
  have hhol : rdU (T.U j T.σ₀) F.1 ∈ holSub (T.U j T.σ₀).X (laU (T.U j T.σ₀) (wtA u) u.n) :=
    ((mem_cusp _ _ _ _ _ F.1).1 hFC).2 T.σ₀ T.good_σ₀
  exact Formalism.L2.Pj.abelian₂.holSub_SS siegelSpaceAlgebra_holds (T.U j T.σ₀).X (laU (T.U j T.σ₀) (wtA u) u.n) hhol k

end GlobalTheory.ArcRead
