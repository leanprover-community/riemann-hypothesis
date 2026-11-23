module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalCharacterIntegrals.ShellP
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.TracePairSums.ShellConj
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

noncomputable section

namespace PositivityTheory.SiegelWeilFormula.SwLocFin

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory GlobalTheory.Cont PositivityTheory.PfSWUS.Loc Filter Topology
open scoped TensorProduct Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem jtR_conj_inv (v : HeightOneSpectrum (𝓞 F)) (σ : E →ₐ[F] E) (hcm : IsCMExt F E σ) {M n : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (ψR : Fv F v → ℂ) (μv : Measure (Fin n → Fin M → Fv F v ⊗[F] E))
    [μv.IsAddHaarMeasure] (Φv : (Fin n → Fin M → Fv F v ⊗[F] E) → ℂ) (hΦ : IsSB Φv) :
    ∃ r > 0, ∀ x : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E), nM v x ≤ r → ∀ b b' : HermR (Fv F v) σ n,
      (b' : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) = ((1 + x).map (sigR (Fv F v) σ))ᵀ * b * (1 + x) →
      jtR (Fv F v) σ J ψR μv Φv b' = jtR (Fv F v) σ J ψR μv Φv b :=
  SwSplit.jtR_conj_inv' v σ hcm J ψR μv Φv hΦ

end PositivityTheory.SiegelWeilFormula.SwLocFin
