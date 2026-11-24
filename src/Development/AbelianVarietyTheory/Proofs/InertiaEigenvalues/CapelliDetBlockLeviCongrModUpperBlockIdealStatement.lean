module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Formalism.RealPlaceAnalysis.StatementE
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CapelliDetBlockLeviCongrModUpperBlockIdeal
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf

@[expose] public section

open NumberField IsDedekindDomain Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec

theorem _root_.GlobalTheory.T.capelliDet_block_levi_congr_mod_upperBlockIdeal : ∀ (A : Type) [Ring A] [Algebra ℂ A] {c N : ℕ} (n : Fin c → ℕ) (h : ∑ i, n i = N) (X : Fin N → Fin N → A), Formalism.REAL.GlRel X → ∀ u : ℂ, Formalism.REAL.qdet X (u + ((N : ℂ) - 1) / 2) - (List.ofFn fun i : Fin c => Formalism.REAL.qdet (fun p q : Fin (n i) => X (stdBlocks n h ⟨i, p⟩) (stdBlocks n h ⟨i, q⟩)) (u + ((n i : ℂ) - 1) / 2 - (modExp (fun i => Fin (n i)) i : ℂ) / 2)).prod ∈ Submodule.span ℂ {y : A | ∃ (p q : Fin N) (w : A), blk (stdBlocks n h) p < blk (stdBlocks n h) q ∧ y = X p q * w} := by
  first | exact @GlobalTheory.CapHC.qdet_blocks_congr | exact GlobalTheory.CapHC.qdet_blocks_congr | (intros; apply GlobalTheory.CapHC.qdet_blocks_congr <;> assumption)
