module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
public import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLemmas.HermitianLocalGlobalExistence
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CTUnitsLeft

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
theorem _root_.GlobalTheory.T.hermitian_local_global_existence : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (γ₀ : GL (Fin n) E), γ₀.val.charpoly ∈ Ell E n → ∀ H₀ : Matrix (Fin n) (Fin n) E, IsHerm (IsCMField.complexConj E).toRingEquiv.toRingHom H₀ → H₀.det ≠ 0 → cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ₀.val * H₀ * γ₀.val = H₀ → ∀ H : ∀ w : Pl E, Matrix (Fin n) (Fin n) (w.adicCompletion E), (∀ w, ¬ IsSplitAt w → IsHerm (cj w) (H w) ∧ (H w).det ≠ 0 ∧ cT (cj w) (γ₀.val.map (algebraMap E (w.adicCompletion E))) * H w * γ₀.val.map (algebraMap E (w.adicCompletion E)) = H w) → (∀ᶠ w in cofinite, ¬ IsSplitAt w → ∃ k m : GL (Fin n) (w.adicCompletion E), k⁻¹ * GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) γ₀ * k ∈ GlobalTheory.LFun.KGL w (n := n) ∧ m ∈ GlobalTheory.LFun.KGL w (n := n) ∧ m.val = cT (cj w) k.val * H w * k.val) → (∀ᶠ w in cofinite, ¬ IsSplitAt w → ∃ c : GL (Fin n) (w.adicCompletion E), c.val * γ₀.val.map (algebraMap E (w.adicCompletion E)) = γ₀.val.map (algebraMap E (w.adicCompletion E)) * c.val ∧ H w = cT (cj w) c.val * H₀.map (algebraMap E (w.adicCompletion E)) * c.val) := by first | exact @GlobalTheory.UsideLeaf.hermitian_local_global_existence.main | exact GlobalTheory.UsideLeaf.hermitian_local_global_existence.main
