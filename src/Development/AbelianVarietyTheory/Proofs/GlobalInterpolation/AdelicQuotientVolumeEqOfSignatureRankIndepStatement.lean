module

public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AdelicQuotientVolumeEqOfSignatureRankIndep
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.GlobalTheoryTheory.GenusMassVolumes
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.adelicQuotientVolume_eq_of_signature_rank_indep : (∀ D : D7, VolTie D → ∀ (W W₀ : HSpace D.host.E) (P Q P₀ Q₀ : ℕ), W.SigOK → W₀.SigOK → (∀ τ, W.sig τ = (P, Q)) → (∀ τ, W₀.sig τ = (P₀, Q₀)) → W.rank = W₀.rank → D.vol W = D.vol W₀) → ∀ D : D7, ∀ (W W₀ : HSpace D.host.E) (P Q P₀ Q₀ : ℕ), W.SigOK → W₀.SigOK → (∀ τ, W.sig τ = (P, Q)) → (∀ τ, W₀.sig τ = (P₀, Q₀)) → W.rank = W₀.rank → ∀ (μ : Measure (HA (AF D.host.F) D.sp.cm.sig W.gram)) (𝓕 : Set (HA (AF D.host.F) D.sp.cm.sig W.gram)) (μ₀ : Measure (HA (AF D.host.F) D.sp.cm.sig W₀.gram)) (𝓕₀ : Set (HA (AF D.host.F) D.sp.cm.sig W₀.gram)), IsVolMeas D W P Q μ → IsFundamentalDomain (HFinIn (AF D.host.F) D.sp.cm.sig W.gram) 𝓕 μ → IsVolMeas D W₀ P₀ Q₀ μ₀ → IsFundamentalDomain (HFinIn (AF D.host.F) D.sp.cm.sig W₀.gram) 𝓕₀ μ₀ → μ 𝓕 = μ₀ 𝓕₀ := by
  first | exact @GlobalTheory.Glob.volMeas_fundDomain_eq_of_tiedIndep | exact GlobalTheory.Glob.volMeas_fundDomain_eq_of_tiedIndep | (intros; apply GlobalTheory.Glob.volMeas_fundDomain_eq_of_tiedIndep <;> assumption)
