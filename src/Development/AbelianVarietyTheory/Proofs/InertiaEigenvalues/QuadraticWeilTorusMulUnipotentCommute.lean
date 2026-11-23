module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsStableGauss
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TensorProduct.IsBaseChangeFree
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

open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.WeilQuad

theorem NL_smul {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [hU : Unram F E] (A : Et F E) (s : A.K) (y : A.L) :
    A.NL (s • y) = s ^ 2 * A.NL y := by
  have hfin : Module.Finite F E := Module.finite_of_finrank_eq_succ hU.finrank_eq
  let b : Module.Basis (Fin 2) F E := Module.finBasisOfFinrankEq F E hU.finrank_eq
  have hp := ((Algebra.IsPushout.comm F E A.K A.L).1 A.push).out
  let c := hp.basis b
  unfold Et.NL
  rw [Algebra.smul_def, map_mul, Algebra.norm_algebraMap_of_basis c, Fintype.card_fin]

theorem mOp_nOp : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.Kˣ) (μ : Measure A.L) (ω : A.K → ℂ),
    Hyp A ψ x μ ω → ∀ (s : A.Kˣ) (z : A.K) (φ : A.L → ℂ),
      mOp A ω s (nOp A ψ x z φ) = nOp A ψ x ((s : A.K) ^ 2 * z) (mOp A ω s φ) := by
  intro F E _ _ _ _ _ A ψ x μ ω _ s z φ
  funext y
  simp only [mOp, nOp, NL_smul]
  rw [show (z * (x : A.K) * ((s : A.K) ^ 2 * A.NL y)) = (s : A.K) ^ 2 * z * x * A.NL y by ring]
  ring

end GlobalTheory.JR.WeilQuad
