module

public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.IntUnit
public import Formalism.LocalToGlobal.ProjectiveLattices.FullXi
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.NormComparisonConstants
public import Development.AbelianVarietyTheory.Definitions.Jets.EmbShortThLeThetaPlain
public import Formalism.LocalToGlobal.ProjectiveLattices.FullExists
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsFullDataExtension
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsShortSeriesTwistCharOfTwistingIdeleCharStatement
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
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.GrowthConstantBoundGcR

@[expose] public section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.RunJoin GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 GlobalTheory.CompRat GlobalTheory.Member
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinalJoin2.FullExt

theorem exists_full_of_xiRec : ∀ (D : D7) (J : CoreJ D) (T : Top D), LawsJ J → LawsP T → T.toCore = J.toCore → T.Q.Canon → ∀ p : ℕ, FieldOK0 D p → ∀ (P : HeightOneSpectrum (𝓞 D.host.K)), ((p : ℕ) : 𝓞 D.host.K) ∈ P.asIdeal → ∀ de, XiRec D p de → ∃ (dd : ∀ j n, DeltaDat (T.Q.Xo j) T.Q.c n) (TF : Full D), LawsFull TF ∧ TF.toTop = { T with dδ := dd } ∧ TF.J = J ∧ XiTilde TF.xi de ∧ TF.half₂ = (P.asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E))) ∧ ∀ j, InR D j → GlobalTheory.FormTies.OneCover TF.toTop j ∧ ∀ n, (TF.dδ j n).pd = p := by
  intro D J T hJ hT hc hcan p hp P hP de hde
  obtain ⟨xi, hxi, ht⟩ := GlobalTheory.T.exists_shortSeriesTwistChar_of_twistingIdeleChar D p de hp.own hde
  obtain ⟨dd, TF, h1, h2, h3, h4, h5⟩ :=
    GlobalTheory.FinalJoin2.FullExt.exists_full_of_xiOK_noVol D J T hJ hT hc hcan p hp P hP xi hxi
  exact ⟨dd, TF, h1, h2, h3, h4 ▸ ht, h5⟩

end GlobalTheory.FinalJoin2.FullExt
