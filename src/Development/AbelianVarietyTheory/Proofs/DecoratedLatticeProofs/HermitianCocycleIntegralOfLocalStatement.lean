module

public import Formalism.LocalToGlobal.KernelLattices.XiIndCClass
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HermitianCocycleIntegralOfLocal
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

@[expose] public section

open NumberField IsDedekindDomain Formalism.L2.Ker

theorem _root_.GlobalTheory.T.hermitian_cocycle_integral_of_local : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (ι : Type) [Fintype ι] [Nonempty ι] (a b : ℕ) (emb : ι → E →+* ℂ) (δ : ℂ) (d : ℕ) (sc : ℝ) (M : Submodule (𝓞 E) (Formalism.L2.Col.HomE E a b)), δ ≠ 0 → (∀ (τ : ι) (x : E), emb τ (star x) = starRingEnd ℂ (emb τ x)) → Formalism.L2.Th1.H.IsSelfDual (HV sc) (laV emb δ M) → Formalism.L2.Th1.H.IsSemiChar (HV sc) (laV emb δ M) (alV d sc) → ∀ x y : Formalism.L2.Col.HomE E a b, (∀ Q : HeightOneSpectrum (𝓞 E), ∃ k : E, k ≠ 0 ∧ k⁻¹ • x ∈ Formalism.HermitianLatticesTheory.localization₂ Q.asIdeal M ∧ star k • y ∈ Formalism.HermitianLatticesTheory.localization₂ (Formalism.L2.Col.conjPrime₂ Q).asIdeal M) → (∃ n : ℤ, Formalism.L2.Th1.H.altE (HV sc) (embH emb δ x) (embH emb δ y) = n) ∧ ∃ n : ℤ, (Real.sqrt d * (HV sc (embH emb δ x) (embH emb δ y)).re + Formalism.L2.Th1.H.altE (HV sc) (embH emb δ x) (embH emb δ y)) / 2 = n := by
  first | exact @GlobalTheory.CocIntLoc.integral_of_local | exact GlobalTheory.CocIntLoc.integral_of_local | (intros; apply GlobalTheory.CocIntLoc.integral_of_local <;> assumption)
