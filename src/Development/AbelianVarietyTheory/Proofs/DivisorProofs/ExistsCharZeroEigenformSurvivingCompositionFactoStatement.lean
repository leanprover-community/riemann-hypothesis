module

public import Development.AbelianVarietyTheory.Definitions.Divisors.LiftFrameEmbeddingBase
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCharZeroEigenformSurvivingCompositionFacto
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

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization

theorem _root_.GlobalTheory.T.exists_charZero_eigenform_surviving_compositionFactor : ∀ (l : ℕ) [Fact l.Prime] (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (F : Frame l ι N) (lam : ι → ℕ → ℕ) (mu : ι → ℕ → ℕ) (jK : F.K →* alg F.O N lam) (ϖ : F.O), F.Ok → F.IsJ lam jK → Irreducible ϖ → ∀ (Gm : Type) [AddCommGroup Gm] [Module F.O Gm] [Module (alg F.O N lam) Gm] [IsScalarTower F.O (alg F.O N lam) Gm] [Module F.T (Forms F.O (A := alg F.O N lam) F.Γ jK Gm)], F.IsHecke lam jK Gm → Embeds F.O N lam mu ϖ Gm → ∀ (m : Ideal F.T) [m.IsMaximal], ¬ Subsingleton (LocalizedModule m.primeCompl (Forms F.O (A := alg F.O N lam) F.Γ jK Gm)) → ∃ θ, F.IsEig mu θ ∧ F.Over θ m := by
  first | exact @GlobalTheory.ExpFrame.Eigenform.eigenform_of_surviving | exact GlobalTheory.ExpFrame.Eigenform.eigenform_of_surviving | (intros; apply GlobalTheory.ExpFrame.Eigenform.eigenform_of_surviving <;> assumption)
