module

public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaLatticePointMemThetaLatticeOfAdelic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators Pointwise

theorem _root_.GlobalTheory.T.cmThetaLatticePoint_mem_thetaLattice_of_adelic : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), cc ≠ ⊥ → ∀ (N N' : ℕ) (g : GA D N) (g' : GA D N') (L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L₁' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), Moves D (g : GL (Fin N) (AE D)) L₁ → Moves D (g' : GL (Fin N') (AE D)) L₁' → ∀ z : Matrix (Fin N') (Fin N) D.host.E, (∀ i j, ((((g' : GL (Fin N') (AE D))⁻¹ : GL (Fin N') (AE D)) : Matrix (Fin N') (Fin N') (AE D)) * z.map (inc D) * ((g : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D))) i j ∈ IhE D cc) → pt D (tor0 D cc δ) δ z ∈ La D (tor0 D cc δ) L₁ L₁' := by
  first | exact @GlobalTheory.NormSum.pt_mem_La_of_adelic | exact GlobalTheory.NormSum.pt_mem_La_of_adelic | (intros; apply GlobalTheory.NormSum.pt_mem_La_of_adelic <;> assumption)
