module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitInclMemExtSubIff
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemIsotropicFlagUnipotentIffSplitChainTrivial
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.AdelicU GlobalTheory.Cusp
open scoped Matrix TensorProduct

theorem _root_.GlobalTheory.T.mem_isotropic_flag_unipotent_iff_split_chain_trivial : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    {V : Formalism.BasicNotions.HSpace E} {v : HeightOneSpectrum (𝓞 F)} (hc : Formalism.BasicNotions.CMData F E), IsCMExt F E hc.sig →
    IsHermND hc.sig V.gram → ∀ (τ : E →ₐ[F] Fv F v) (𝔉 : GlobalTheory.Cusp.IsoFlag V) (g : GlobalTheory.AdelicU.GLoc hc.sig V.gram v),
    g ∈ 𝔉.unip hc (Fv F v) ↔ ∀ j : Fin (2 * 𝔉.k + 1), ∀ u ∈ GlobalTheory.SplitFlag.flagChain 𝔉 τ j.succ,
      ((GlobalTheory.AdelicU.splitHom hc.sig V.gram τ g : GL (Fin V.rank) (Fv F v)) : Matrix (Fin V.rank) (Fin V.rank) (Fv F v)) *ᵥ u - u ∈
        GlobalTheory.SplitFlag.flagChain 𝔉 τ j.castSucc := by
  first | exact @GlobalTheory.SplitFlag.mem_unip_iff_flagChain | exact GlobalTheory.SplitFlag.mem_unip_iff_flagChain | (intros; apply GlobalTheory.SplitFlag.mem_unip_iff_flagChain <;> assumption)
