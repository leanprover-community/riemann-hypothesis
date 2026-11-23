module

public import Formalism.LocalToGlobal.Columns.RecLevelLocT
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryLastRowDivisibleStabilizesLattices
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

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.DIV Matrix
open scoped TensorProduct

theorem _root_.GlobalTheory.T.unitary_lastRowDivisible_stabilizes_lattices : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] {ST : Finset (Pl E)} {π : 𝓞 E}, BasePi ST π → ∀ (v : HeightOneSpectrum (𝓞 F)) (g : GL (Fin n) (E ⊗[F] v.adicCompletion F)), g ∈ UPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (v.adicCompletion F) → ((∀ i j, (g : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) i j ∈ intV E v) ∧ ∀ j, j ≠ lastIdx n → ∃ s ∈ intV E v, (g : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) (lastIdx n) j = inclE (F := F) (v.adicCompletion F) (algebraMap (𝓞 E) E π) * s) → ((∀ i j, ((g⁻¹ : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) i j ∈ intV E v) ∧ ∀ j, j ≠ lastIdx n → ∃ s ∈ intV E v, ((g⁻¹ : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) (lastIdx n) j = inclE (F := F) (v.adicCompletion F) (algebraMap (𝓞 E) E π) * s) → g ∈ stabGL (Formalism.L2.Herm.locL v (baseLb E n ST)) ∧ g ∈ stabGL (baseDualV hc n ST v) ∧ g ∈ stabGL (latS (F := F) (v.adicCompletion F) (intV E v) (baseKer E n ST)) := by
  first | exact @GlobalTheory.unitary_offRow_stab_three | exact GlobalTheory.unitary_offRow_stab_three | (intros; apply GlobalTheory.unitary_offRow_stab_three <;> assumption)
